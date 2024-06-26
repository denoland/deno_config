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
#[cfg(feature = "package_json")]
mod sync;
#[cfg(feature = "deno_json")]
mod util;
#[cfg(feature = "workspace")]
pub mod workspace;

#[cfg(feature = "deno_json")]
pub use deno_json::*;
#[cfg(feature = "deno_json")]
pub use util::SpecifierToFilePathError;
