// Copyright 2018-2023 the Deno authors. All rights reserved. MIT license.

use anyhow::bail;
use anyhow::Error as AnyError;
use serde_json::Value;
use std::path::Component;
use std::path::Path;
use std::path::PathBuf;
use url::Url;

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

/// Attempts to convert a specifier to a file path. By default, uses the Url
/// crate's `to_file_path()` method, but falls back to try and resolve unix-style
/// paths on Windows.
pub fn specifier_to_file_path(specifier: &Url) -> Result<PathBuf, AnyError> {
  let result = if specifier.scheme() != "file" {
    Err(())
  } else if cfg!(windows) {
    match specifier.to_file_path() {
      Ok(path) => Ok(path),
      Err(()) => {
        // This might be a unix-style path which is used in the tests even on Windows.
        // Attempt to see if we can convert it to a `PathBuf`. This code should be removed
        // once/if https://github.com/servo/rust-url/issues/730 is implemented.
        if specifier.scheme() == "file"
          && specifier.host().is_none()
          && specifier.port().is_none()
          && specifier.path_segments().is_some()
        {
          let path_str = specifier.path();
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
    specifier.to_file_path()
  };
  match result {
    Ok(path) => Ok(path),
    Err(()) => bail!("Invalid file path.\n  Specifier: {specifier}"),
  }
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

/// A function that works like JavaScript's `Object.assign()`.
pub fn json_merge(a: &mut Value, b: &Value) {
  match (a, b) {
    (&mut Value::Object(ref mut a), Value::Object(b)) => {
      for (k, v) in b {
        json_merge(a.entry(k.clone()).or_insert(Value::Null), v);
      }
    }
    (a, b) => {
      *a = b.clone();
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use serde_json::json;

  #[test]
  fn test_json_merge() {
    let mut value_a = json!({
      "a": true,
      "b": "c"
    });
    let value_b = json!({
      "b": "d",
      "e": false,
    });
    json_merge(&mut value_a, &value_b);
    assert_eq!(
      value_a,
      json!({
        "a": true,
        "b": "d",
        "e": false,
      })
    );
  }

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
      let result =
        specifier_to_file_path(&Url::parse(specifier).unwrap()).unwrap();
      assert_eq!(result, PathBuf::from(expected_path));
    }
  }
}
