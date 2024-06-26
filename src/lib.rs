// Copyright 2018-2024 the Deno authors. MIT license.

#![deny(clippy::print_stderr)]
#![deny(clippy::print_stdout)]
#![deny(clippy::unused_async)]

#[cfg(feature = "deno_json")]
mod deno_json;
pub mod fs;
#[cfg(feature = "deno_json")]
pub mod glob;
#[cfg(feature = "package_json")]
pub mod package_json;
#[cfg(any(feature = "deno_json", feature = "package_json"))]
mod util;

pub use deno_json::*;
pub use util::SpecifierToFilePathError;
