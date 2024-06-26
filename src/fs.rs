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
