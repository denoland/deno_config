// Copyright 2018-2024 the Deno authors. MIT license.

use std::borrow::Cow;
use std::path::Path;
use std::path::PathBuf;

#[derive(Debug, Default, Clone)]
pub struct FsMetadata {
  pub is_file: bool,
  pub is_directory: bool,
  pub is_symlink: bool,
}

#[derive(Debug, Clone)]
pub struct FsDirEntry {
  pub path: PathBuf,
  pub metadata: FsMetadata,
}

pub trait DenoConfigFs {
  fn stat_sync(&self, path: &Path) -> Result<FsMetadata, std::io::Error>;
  fn read_to_string_lossy(&self, path: &Path)
    -> Result<String, std::io::Error>;
  fn read_dir(&self, path: &Path) -> Result<Vec<FsDirEntry>, std::io::Error>;

  fn exists(&self, path: &Path) -> bool {
    self.stat_sync(path).is_ok()
  }
}

#[derive(Debug, Clone, Copy)]
pub struct RealDenoConfigFs;

impl DenoConfigFs for RealDenoConfigFs {
  fn stat_sync(&self, path: &Path) -> Result<FsMetadata, std::io::Error> {
    // allowed here for the real fs
    #[allow(clippy::disallowed_methods)]
    std::fs::metadata(path).map(|metadata| FsMetadata {
      is_file: metadata.is_file(),
      is_directory: metadata.is_dir(),
      is_symlink: metadata.file_type().is_symlink(),
    })
  }

  fn read_to_string_lossy(
    &self,
    path: &Path,
  ) -> Result<String, std::io::Error> {
    // allowed here for the real fs
    #[allow(clippy::disallowed_methods)]
    let bytes = std::fs::read(path)?;
    Ok(string_from_utf8_lossy(bytes))
  }

  fn read_dir(&self, path: &Path) -> Result<Vec<FsDirEntry>, std::io::Error> {
    // allowed here for the real fs
    #[allow(clippy::disallowed_methods)]
    let entries = std::fs::read_dir(path)?;
    let mut result = Vec::new();
    for entry in entries {
      let Ok(entry) = entry else {
        continue;
      };
      let path = entry.path();
      let Ok(metadata) = entry.metadata() else {
        continue;
      };
      let stat = FsMetadata {
        is_file: metadata.is_file(),
        is_directory: metadata.is_dir(),
        is_symlink: metadata.file_type().is_symlink(),
      };
      result.push(FsDirEntry {
        path,
        metadata: stat,
      });
    }
    Ok(result)
  }
}

impl<'a> Default for &'a dyn DenoConfigFs {
  fn default() -> Self {
    &RealDenoConfigFs
  }
}

#[cfg(feature = "package_json")]
pub struct DenoConfigPkgJsonAdapterFs<'a>(pub &'a dyn DenoConfigFs);

#[cfg(feature = "package_json")]
impl<'a> deno_package_json::fs::DenoPkgJsonFs
  for DenoConfigPkgJsonAdapterFs<'a>
{
  fn read_to_string_lossy(
    &self,
    path: &Path,
  ) -> Result<String, std::io::Error> {
    self.0.read_to_string_lossy(path)
  }
}

// Like String::from_utf8_lossy but operates on owned values
#[inline(always)]
fn string_from_utf8_lossy(buf: Vec<u8>) -> String {
  match String::from_utf8_lossy(&buf) {
    // buf contained non-utf8 chars than have been patched
    Cow::Owned(s) => s,
    // SAFETY: if Borrowed then the buf only contains utf8 chars,
    // we do this instead of .into_owned() to avoid copying the input buf
    Cow::Borrowed(_) => unsafe { String::from_utf8_unchecked(buf) },
  }
}

#[cfg(test)]
#[derive(Debug)]
enum DirEntry {
  // todo(dsherret): add symlink here in the future
  Directory,
  File(String),
}

#[cfg(test)]
impl DirEntry {
  pub fn as_metadata(&self) -> FsMetadata {
    match self {
      DirEntry::Directory => FsMetadata {
        is_file: false,
        is_directory: true,
        is_symlink: false,
      },
      DirEntry::File(_) => FsMetadata {
        is_file: true,
        is_directory: false,
        is_symlink: false,
      },
    }
  }
}

#[cfg(test)]
#[derive(Debug, Default)]
struct Dir {
  pub entries: std::collections::BTreeMap<String, DirEntry>,
}

#[cfg(test)]
#[derive(Debug, Default)]
pub(crate) struct TestFileSystem {
  directories: std::collections::BTreeMap<std::path::PathBuf, Dir>,
}

#[cfg(test)]
impl TestFileSystem {
  pub fn insert_json(
    &mut self,
    path: impl AsRef<Path>,
    contents: serde_json::Value,
  ) {
    self.insert(path, contents.to_string())
  }

  pub fn insert(&mut self, path: impl AsRef<Path>, contents: impl AsRef<str>) {
    let path = path.as_ref();
    self.get_dir_mut(path.parent().unwrap()).entries.insert(
      path.file_name().unwrap().to_string_lossy().to_string(),
      DirEntry::File(contents.as_ref().to_string()),
    );
  }

  fn get_dir_mut(&mut self, path: &Path) -> &mut Dir {
    let path = crate::util::normalize_path(path);
    if !self.directories.contains_key(&path) {
      if let Some(parent) = path.parent() {
        let parent_dir = self.get_dir_mut(parent);
        let file_name = path.file_name().unwrap().to_string_lossy().to_string();
        parent_dir.entries.insert(file_name, DirEntry::Directory);
      }
      self.directories.insert(
        path.clone(),
        Dir {
          entries: Default::default(),
        },
      );
    }
    self.directories.get_mut(&path).unwrap()
  }
}

#[cfg(test)]
impl DenoConfigFs for TestFileSystem {
  fn read_to_string_lossy(
    &self,
    path: &Path,
  ) -> Result<String, std::io::Error> {
    let path = crate::util::normalize_path(path);
    path
      .parent()
      .and_then(|parent| {
        self
          .directories
          .get(parent)
          .and_then(|d| d.entries.get(path.file_name()?.to_str()?))
          .and_then(|e| match e {
            DirEntry::Directory => None,
            DirEntry::File(text) => Some(text.clone()),
          })
      })
      .ok_or_else(|| {
        std::io::Error::new(std::io::ErrorKind::NotFound, "file not found")
      })
  }

  fn stat_sync(&self, path: &Path) -> Result<FsMetadata, std::io::Error> {
    path
      .parent()
      .and_then(|parent| {
        self
          .directories
          .get(parent)
          .and_then(|d| d.entries.get(path.file_name()?.to_str()?))
          .map(|e| e.as_metadata())
      })
      .ok_or_else(|| {
        std::io::Error::new(std::io::ErrorKind::NotFound, "not found")
      })
  }

  fn read_dir(&self, path: &Path) -> Result<Vec<FsDirEntry>, std::io::Error> {
    self
      .directories
      .get(path)
      .map(|dir| {
        dir
          .entries
          .iter()
          .map(|(name, entry)| FsDirEntry {
            path: path.join(name),
            metadata: entry.as_metadata(),
          })
          .collect::<Vec<_>>()
      })
      .ok_or_else(|| {
        std::io::Error::new(std::io::ErrorKind::NotFound, "not found")
      })
  }
}
