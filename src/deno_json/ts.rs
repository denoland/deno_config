// Copyright 2018-2024 the Deno authors. MIT license.

use anyhow::Error as AnyError;
use serde::Deserialize;
use serde::Serialize;
use serde::Serializer;
use serde_json::json;
use serde_json::Value;
use std::collections::BTreeMap;
use std::fmt;
use url::Url;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct JsxImportSourceConfig {
  pub default_specifier: Option<String>,
  pub default_types_specifier: Option<String>,
  pub module: String,
  pub base_url: Url,
}

impl JsxImportSourceConfig {
  pub fn maybe_specifier_text(&self) -> Option<String> {
    self
      .default_specifier
      .as_ref()
      .map(|default_specifier| format!("{}/{}", default_specifier, self.module))
  }

  pub fn maybe_types_specifier_text(&self) -> Option<String> {
    self
      .default_types_specifier
      .as_ref()
      .map(|default_types_specifier| {
        format!("{}/{}", default_types_specifier, self.module)
      })
  }
}

/// The transpile options that are significant out of a user provided tsconfig
/// file, that we want to deserialize out of the final config for a transpile.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EmitConfigOptions {
  pub check_js: bool,
  pub experimental_decorators: bool,
  pub emit_decorator_metadata: bool,
  pub imports_not_used_as_values: String,
  pub inline_source_map: bool,
  pub inline_sources: bool,
  pub source_map: bool,
  pub jsx: String,
  pub jsx_factory: String,
  pub jsx_fragment_factory: String,
  pub jsx_import_source: Option<String>,
  pub jsx_precompile_skip_elements: Option<Vec<String>>,
}

/// There are certain compiler options that can impact what modules are part of
/// a module graph, which need to be deserialized into a structure for analysis.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CompilerOptions {
  pub jsx: Option<String>,
  pub jsx_import_source: Option<String>,
  pub jsx_import_source_types: Option<String>,
  pub types: Option<Vec<String>>,
}

/// A structure that represents a set of options that were ignored and the
/// path those options came from.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct IgnoredCompilerOptions {
  pub items: Vec<String>,
  pub maybe_specifier: Option<Url>,
}

impl fmt::Display for IgnoredCompilerOptions {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let mut codes = self.items.clone();
    codes.sort_unstable();
    if let Some(specifier) = &self.maybe_specifier {
      write!(f, "Unsupported compiler options in \"{}\".\n  The following options were ignored:\n    {}", specifier, codes.join(", "))
    } else {
      write!(f, "Unsupported compiler options provided.\n  The following options were ignored:\n    {}", codes.join(", "))
    }
  }
}

impl Serialize for IgnoredCompilerOptions {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    Serialize::serialize(&self.items, serializer)
  }
}

/// A set of all the compiler options that should be allowed;
static ALLOWED_COMPILER_OPTIONS: phf::Set<&'static str> = phf::phf_set! {
  "allowUnreachableCode",
  "allowUnusedLabels",
  "checkJs",
  "emitDecoratorMetadata",
  "exactOptionalPropertyTypes",
  "experimentalDecorators",
  "isolatedDeclarations",
  "jsx",
  "jsxFactory",
  "jsxFragmentFactory",
  "jsxImportSource",
  "jsxPrecompileSkipElements",
  "lib",
  "noErrorTruncation",
  "noFallthroughCasesInSwitch",
  "noImplicitAny",
  "noImplicitOverride",
  "noImplicitReturns",
  "noImplicitThis",
  "noPropertyAccessFromIndexSignature",
  "noUncheckedIndexedAccess",
  "noUnusedLocals",
  "noUnusedParameters",
  "strict",
  "strictBindCallApply",
  "strictBuiltinIteratorReturn",
  "strictFunctionTypes",
  "strictNullChecks",
  "strictPropertyInitialization",
  "types",
  "useUnknownInCatchVariables",
  "verbatimModuleSyntax",
};

#[derive(Debug, Default, Clone)]
pub struct ParsedTsConfigOptions {
  pub options: serde_json::Map<String, serde_json::Value>,
  pub maybe_ignored: Option<IgnoredCompilerOptions>,
}

pub fn parse_compiler_options(
  compiler_options: serde_json::Map<String, Value>,
  maybe_specifier: Option<&Url>,
) -> Result<ParsedTsConfigOptions, AnyError> {
  let mut allowed: serde_json::Map<String, Value> =
    serde_json::Map::with_capacity(compiler_options.len());
  let mut ignored: Vec<String> = Vec::with_capacity(compiler_options.len());

  for (key, value) in compiler_options {
    // We don't pass "types" entries to typescript via the compiler
    // options and instead provide those to tsc as "roots". This is
    // because our "types" behavior is at odds with how TypeScript's
    // "types" works.
    // We also don't pass "jsxImportSourceTypes" to TypeScript as it doesn't
    // know about this option. It will still take this option into account
    // because the graph resolves the JSX import source to the types for TSC.
    if key != "types" && key != "jsxImportSourceTypes" {
      if ALLOWED_COMPILER_OPTIONS.contains(key.as_str()) {
        allowed.insert(key, value.to_owned());
      } else {
        ignored.push(key);
      }
    }
  }
  let maybe_ignored = if !ignored.is_empty() {
    Some(IgnoredCompilerOptions {
      items: ignored,
      maybe_specifier: maybe_specifier.cloned(),
    })
  } else {
    None
  };

  Ok(ParsedTsConfigOptions {
    options: allowed,
    maybe_ignored,
  })
}

/// A structure for managing the configuration of TypeScript
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TsConfig(pub Value);

impl TsConfig {
  /// Create a new `TsConfig` with the base being the `value` supplied.
  pub fn new(value: Value) -> Self {
    TsConfig(value)
  }

  pub fn as_bytes(&self) -> Vec<u8> {
    let map = self.0.as_object().expect("invalid tsconfig");
    let ordered: BTreeMap<_, _> = map.iter().collect();
    let value = json!(ordered);
    value.to_string().as_bytes().to_owned()
  }

  /// Return the value of the `checkJs` compiler option, defaulting to `false`
  /// if not present.
  pub fn get_check_js(&self) -> bool {
    if let Some(check_js) = self.0.get("checkJs") {
      check_js.as_bool().unwrap_or(false)
    } else {
      false
    }
  }

  pub fn get_declaration(&self) -> bool {
    if let Some(declaration) = self.0.get("declaration") {
      declaration.as_bool().unwrap_or(false)
    } else {
      false
    }
  }

  /// Merge a serde_json value into the configuration.
  pub fn merge(&mut self, value: serde_json::Value) {
    json_merge(&mut self.0, value);
  }

  /// Take an optional user provided config file
  /// which was passed in via the `--config` flag and merge `compilerOptions` with
  /// the configuration.  Returning the result which optionally contains any
  /// compiler options that were ignored.
  pub fn merge_tsconfig_from_config_file(
    &mut self,
    maybe_config_file: Option<&super::ConfigFile>,
  ) -> Result<Option<IgnoredCompilerOptions>, AnyError> {
    if let Some(config_file) = maybe_config_file {
      let ParsedTsConfigOptions {
        options,
        maybe_ignored,
      } = config_file.to_compiler_options()?;
      self.merge(serde_json::Value::Object(options));
      Ok(maybe_ignored)
    } else {
      Ok(None)
    }
  }
}

impl Serialize for TsConfig {
  /// Serializes inner hash map which is ordered by the key
  fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    Serialize::serialize(&self.0, serializer)
  }
}

/// A function that works like JavaScript's `Object.assign()`.
fn json_merge(a: &mut Value, b: Value) {
  match (a, b) {
    (&mut Value::Object(ref mut a), Value::Object(b)) => {
      for (k, v) in b {
        json_merge(a.entry(k).or_insert(Value::Null), v);
      }
    }
    (a, b) => {
      *a = b;
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_tsconfig_as_bytes() {
    let mut tsconfig1 = TsConfig::new(json!({
      "strict": true,
      "target": "esnext",
    }));
    tsconfig1.merge(json!({
      "target": "es5",
      "module": "amd",
    }));
    let mut tsconfig2 = TsConfig::new(json!({
      "target": "esnext",
      "strict": true,
    }));
    tsconfig2.merge(json!({
      "module": "amd",
      "target": "es5",
    }));
    assert_eq!(tsconfig1.as_bytes(), tsconfig2.as_bytes());
  }

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
    json_merge(&mut value_a, value_b);
    assert_eq!(
      value_a,
      json!({
        "a": true,
        "b": "d",
        "e": false,
      })
    );
  }
}
