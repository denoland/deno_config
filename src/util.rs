// Copyright 2018-2024 the Deno authors. MIT license.

use std::path::Component;
use std::path::Path;
use std::path::PathBuf;
use thiserror::Error;
use url::Url;

pub fn is_skippable_io_error(e: &std::io::Error) -> bool {
  use std::io::ErrorKind::*;

  // skip over invalid filenames on windows
  const ERROR_INVALID_NAME: i32 = 123;
  if cfg!(windows) && e.raw_os_error() == Some(ERROR_INVALID_NAME) {
    return true;
  }

  match e.kind() {
    InvalidInput | PermissionDenied | NotFound => {
      // ok keep going
      true
    }
    _ => {
      const NOT_A_DIRECTORY: i32 = 20;
      cfg!(unix) && e.raw_os_error() == Some(NOT_A_DIRECTORY)
    }
  }
}

/// Gets the parent of this module specifier.
pub fn specifier_parent(specifier: &Url) -> Url {
  let mut specifier = specifier.clone();
  // don't use specifier.segments() because it will strip the leading slash
  let mut segments = specifier.path().split('/').collect::<Vec<_>>();
  if segments.iter().all(|s| s.is_empty()) {
    return specifier;
  }
  if let Some(last) = segments.last() {
    if last.is_empty() {
      segments.pop();
    }
    segments.pop();
    let new_path = format!("{}/", segments.join("/"));
    specifier.set_path(&new_path);
  }
  specifier
}

#[derive(Debug, Error)]
#[error("Could not convert specifier to file path.\n  Specifier: {0}")]
pub struct SpecifierToFilePathError(pub Url);

/// Attempts to convert a url to a file path. By default, uses the Url
/// crate's `to_file_path()` method, but falls back to try and resolve unix-style
/// paths on Windows.
pub fn url_to_file_path(
  specifier: &Url,
) -> Result<PathBuf, SpecifierToFilePathError> {
  let result = if specifier.scheme() != "file" {
    Err(())
  } else {
    url_to_file_path_inner(specifier)
  };
  match result {
    Ok(path) => Ok(path),
    Err(()) => Err(SpecifierToFilePathError(specifier.clone())),
  }
}

fn url_to_file_path_inner(url: &Url) -> Result<PathBuf, ()> {
  #[cfg(any(unix, windows, target_os = "redox", target_os = "wasi"))]
  return url_to_file_path_real(url);
  #[cfg(not(any(unix, windows, target_os = "redox", target_os = "wasi")))]
  url_to_file_path_wasm(url)
}

#[cfg(any(unix, windows, target_os = "redox", target_os = "wasi"))]
fn url_to_file_path_real(url: &Url) -> Result<PathBuf, ()> {
  if cfg!(windows) {
    match url.to_file_path() {
      Ok(path) => Ok(path),
      Err(()) => {
        // This might be a unix-style path which is used in the tests even on Windows.
        // Attempt to see if we can convert it to a `PathBuf`. This code should be removed
        // once/if https://github.com/servo/rust-url/issues/730 is implemented.
        if url.scheme() == "file"
          && url.host().is_none()
          && url.port().is_none()
          && url.path_segments().is_some()
        {
          let path_str = url.path();
          match String::from_utf8(
            percent_encoding::percent_decode(path_str.as_bytes()).collect(),
          ) {
            Ok(path_str) => Ok(PathBuf::from(path_str)),
            Err(_) => Err(()),
          }
        } else {
          Err(())
        }
      }
    }
  } else {
    url.to_file_path()
  }
}

#[cfg(any(
  test,
  not(any(unix, windows, target_os = "redox", target_os = "wasi"))
))]
fn url_to_file_path_wasm(url: &Url) -> Result<PathBuf, ()> {
  fn is_windows_path_segment(specifier: &str) -> bool {
    let mut chars = specifier.chars();

    let first_char = chars.next();
    if first_char.is_none() || !first_char.unwrap().is_ascii_alphabetic() {
      return false;
    }

    if chars.next() != Some(':') {
      return false;
    }

    chars.next().is_none()
  }

  let path_segments = url.path_segments().unwrap().collect::<Vec<_>>();
  let mut final_text = String::new();
  let mut is_windows_share = false;
  if let Some(host) = url.host_str() {
    final_text.push_str("\\\\");
    final_text.push_str(host);
    is_windows_share = true;
  }
  for segment in path_segments.iter() {
    if is_windows_share {
      final_text.push('\\');
    } else if !final_text.is_empty() {
      final_text.push('/');
    }
    final_text.push_str(
      &percent_encoding::percent_decode_str(segment).decode_utf8_lossy(),
    );
  }
  if !is_windows_share && !is_windows_path_segment(path_segments[0]) {
    final_text = format!("/{}", final_text);
  }
  Ok(PathBuf::from(final_text))
}

/// Normalize all intermediate components of the path (ie. remove "./" and "../" components).
/// Similar to `fs::canonicalize()` but doesn't resolve symlinks.
///
/// Taken from Cargo
/// <https://github.com/rust-lang/cargo/blob/af307a38c20a753ec60f0ad18be5abed3db3c9ac/src/cargo/util/paths.rs#L60-L85>
#[inline]
pub fn normalize_path<P: AsRef<Path>>(path: P) -> PathBuf {
  fn inner(path: &Path) -> PathBuf {
    let mut components = path.components().peekable();
    let mut ret =
      if let Some(c @ Component::Prefix(..)) = components.peek().cloned() {
        components.next();
        PathBuf::from(c.as_os_str())
      } else {
        PathBuf::new()
      };

    for component in components {
      match component {
        Component::Prefix(..) => unreachable!(),
        Component::RootDir => {
          ret.push(component.as_os_str());
        }
        Component::CurDir => {}
        Component::ParentDir => {
          ret.pop();
        }
        Component::Normal(c) => {
          ret.push(c);
        }
      }
    }
    ret
  }

  inner(path.as_ref())
}

pub fn url_from_file_path(path: &Path) -> Result<Url, ()> {
  #[cfg(any(unix, windows, target_os = "redox", target_os = "wasi"))]
  return Url::from_file_path(path);
  #[cfg(not(any(unix, windows, target_os = "redox", target_os = "wasi")))]
  url_from_file_path_wasm(path)
}

pub fn url_from_directory_path(path: &Path) -> Result<Url, ()> {
  #[cfg(any(unix, windows, target_os = "redox", target_os = "wasi"))]
  return Url::from_directory_path(path);
  #[cfg(not(any(unix, windows, target_os = "redox", target_os = "wasi")))]
  url_from_directory_path_wasm(path)
}

#[cfg(any(
  test,
  not(any(unix, windows, target_os = "redox", target_os = "wasi"))
))]
fn url_from_directory_path_wasm(path: &Path) -> Result<Url, ()> {
  let mut url = url_from_file_path_wasm(path)?;
  url.path_segments_mut().unwrap().push("");
  Ok(url)
}

#[cfg(any(
  test,
  not(any(unix, windows, target_os = "redox", target_os = "wasi"))
))]
fn url_from_file_path_wasm(path: &Path) -> Result<Url, ()> {
  use std::path::Component;

  let original_path = path.to_string_lossy();
  let mut path_str = original_path;
  // assume paths containing backslashes are windows paths
  if path_str.contains('\\') {
    let mut url = Url::parse("file://").unwrap();
    if let Some(next) = path_str.strip_prefix(r#"\\?\UNC\"#) {
      if let Some((host, rest)) = next.split_once('\\') {
        if url.set_host(Some(host)).is_ok() {
          path_str = rest.to_string().into();
        }
      }
    } else if let Some(next) = path_str.strip_prefix(r#"\\?\"#) {
      path_str = next.to_string().into();
    } else if let Some(next) = path_str.strip_prefix(r#"\\"#) {
      if let Some((host, rest)) = next.split_once('\\') {
        if url.set_host(Some(host)).is_ok() {
          path_str = rest.to_string().into();
        }
      }
    }

    for component in path_str.split('\\') {
      url.path_segments_mut().unwrap().push(component);
    }

    Ok(url)
  } else {
    let mut url = Url::parse("file://").unwrap();
    for component in path.components() {
      match component {
        Component::RootDir => {
          url.path_segments_mut().unwrap().push("");
        }
        Component::Normal(segment) => {
          url
            .path_segments_mut()
            .unwrap()
            .push(&segment.to_string_lossy());
        }
        Component::Prefix(_) | Component::CurDir | Component::ParentDir => {
          return Err(());
        }
      }
    }

    Ok(url)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_specifier_parent() {
    run_test("file:///", "file:///");
    run_test("file:///test", "file:///");
    run_test("file:///test/", "file:///");
    run_test("file:///test/other", "file:///test/");
    run_test("file:///test/other.txt", "file:///test/");
    run_test("file:///test/other/", "file:///test/");

    fn run_test(specifier: &str, expected: &str) {
      let result = specifier_parent(&Url::parse(specifier).unwrap());
      assert_eq!(result.to_string(), expected);
    }
  }

  #[test]
  fn test_specifier_to_file_path() {
    run_success_test("file:///", "/");
    run_success_test("file:///test", "/test");
    run_success_test("file:///dir/test/test.txt", "/dir/test/test.txt");
    run_success_test(
      "file:///dir/test%20test/test.txt",
      "/dir/test test/test.txt",
    );

    fn run_success_test(specifier: &str, expected_path: &str) {
      let result = url_to_file_path(&Url::parse(specifier).unwrap()).unwrap();
      assert_eq!(result, PathBuf::from(expected_path));
    }
  }

  #[cfg(windows)]
  #[test]
  fn is_skippable_io_error_win_invalid_filename() {
    let error = std::io::Error::from_raw_os_error(123);
    assert!(is_skippable_io_error(&error));
  }

  #[test]
  fn test_url_to_file_path_wasm() {
    #[track_caller]
    fn convert(path: &str) -> String {
      url_to_file_path_wasm(&Url::parse(path).unwrap())
        .unwrap()
        .to_string_lossy()
        .into_owned()
    }

    assert_eq!(convert("file:///a/b/c.json"), "/a/b/c.json");
    assert_eq!(convert("file:///D:/test/other.json"), "D:/test/other.json");
    assert_eq!(
      convert("file:///path%20with%20spaces/and%23special%25chars!.json"),
      "/path with spaces/and#special%chars!.json",
    );
    assert_eq!(
      convert("file:///C:/My%20Documents/file.txt"),
      "C:/My Documents/file.txt"
    );
    assert_eq!(
      convert("file:///a/b/%D0%BF%D1%80%D0%B8%D0%BC%D0%B5%D1%80.txt"),
      "/a/b/пример.txt"
    );
    assert_eq!(
      convert("file://server/share/folder/file.txt"),
      "\\\\server\\share\\folder\\file.txt"
    );
  }

  #[test]
  fn test_url_from_file_path_wasm() {
    #[track_caller]
    fn convert(path: &str) -> String {
      url_from_file_path_wasm(Path::new(path))
        .unwrap()
        .to_string()
    }

    assert_eq!(convert("/a/b/c.json"), "file:///a/b/c.json");
    assert_eq!(
      convert("D:\\test\\other.json"),
      "file:///D:/test/other.json"
    );
    assert_eq!(
      convert("/path with spaces/and#special%chars!.json"),
      "file:///path%20with%20spaces/and%23special%25chars!.json"
    );
    assert_eq!(
      convert("C:\\My Documents\\file.txt"),
      "file:///C:/My%20Documents/file.txt"
    );
    assert_eq!(
      convert("/a/b/пример.txt"),
      "file:///a/b/%D0%BF%D1%80%D0%B8%D0%BC%D0%B5%D1%80.txt"
    );
    assert_eq!(
      convert("\\\\server\\share\\folder\\file.txt"),
      "file://server/share/folder/file.txt"
    );
    assert_eq!(convert(r#"\\?\UNC\server\share"#), "file://server/share");
    assert_eq!(
      convert(r"\\?\cat_pics\subfolder\file.jpg"),
      "file:///cat_pics/subfolder/file.jpg"
    );
    assert_eq!(convert(r"\\?\cat_pics"), "file:///cat_pics");
  }

  #[test]
  fn test_url_from_directory_path_wasm() {
    #[track_caller]
    fn convert(path: &str) -> String {
      url_from_directory_path_wasm(Path::new(path))
        .unwrap()
        .to_string()
    }

    assert_eq!(convert("/a/b/c"), "file:///a/b/c/");
    assert_eq!(convert("D:\\test\\other"), "file:///D:/test/other/");
  }
}
