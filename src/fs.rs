// Copyright 2018-2024 the Deno authors. MIT license.

use std::path::Path;

pub trait DenoConfigFs {
  fn read_to_string(&self, path: &Path) -> Result<String, std::io::Error>;
}

#[derive(Debug, Clone, Copy)]
pub struct RealDenoConfigFs;

impl DenoConfigFs for RealDenoConfigFs {
  fn read_to_string(&self, path: &Path) -> Result<String, std::io::Error> {
    // allowed here for the real fs
    #[allow(clippy::disallowed_methods)]
    std::fs::read_to_string(path)
  }
}

impl<'a> Default for &'a dyn DenoConfigFs {
  fn default() -> Self {
    &RealDenoConfigFs
  }
}

#[cfg(test)]
#[derive(Debug, Default)]
pub(crate) struct TestFileSystem(
  pub std::collections::HashMap<std::path::PathBuf, String>,
);

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
    self
      .0
      .insert(path.as_ref().to_path_buf(), contents.as_ref().to_string());
  }
}

#[cfg(test)]
impl DenoConfigFs for TestFileSystem {
  fn read_to_string(&self, path: &Path) -> Result<String, std::io::Error> {
    self.0.get(path).cloned().ok_or_else(|| {
      std::io::Error::new(std::io::ErrorKind::NotFound, "file not found")
    })
  }
}
