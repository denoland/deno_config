// Copyright 2018-2024 the Deno authors. MIT license.

use std::path::PathBuf;

use indexmap::IndexMap;
use serde::Serialize;
use serde_json::Map;
use serde_json::Value;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum PackageJsonReadError {
  #[error("Failed reading '{}'.", .path.display())]
  Io {
    path: PathBuf,
    #[source]
    source: std::io::Error,
  },
  #[error("Malformed package.json '{}'.", .path.display())]
  Deserialize {
    path: PathBuf,
    #[source]
    source: serde_json::Error,
  },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NodeModuleKind {
  Esm,
  Cjs,
}

#[derive(Clone, Debug, Serialize)]
pub struct PackageJson {
  pub exports: Option<Map<String, Value>>,
  pub imports: Option<Map<String, Value>>,
  pub bin: Option<Value>,
  main: Option<String>,   // use .main(...)
  module: Option<String>, // use .main(...)
  pub name: Option<String>,
  pub version: Option<String>,
  pub path: PathBuf,
  pub typ: String,
  pub types: Option<String>,
  pub dependencies: Option<IndexMap<String, String>>,
  pub dev_dependencies: Option<IndexMap<String, String>>,
  pub scripts: Option<IndexMap<String, String>>,
  pub workspaces: Option<Vec<String>>,
}

impl PackageJson {
  pub fn load_from_string(
    path: PathBuf,
    source: String,
  ) -> Result<PackageJson, PackageJsonReadError> {
    if source.trim().is_empty() {
      return Ok(PackageJson {
        path,
        main: None,
        name: None,
        version: None,
        module: None,
        typ: "none".to_string(),
        types: None,
        exports: None,
        imports: None,
        bin: None,
        dependencies: None,
        dev_dependencies: None,
        scripts: None,
        workspaces: None,
      });
    }

    let package_json: Value = serde_json::from_str(&source).map_err(|err| {
      PackageJsonReadError::Deserialize {
        path: path.clone(),
        source: err,
      }
    })?;
    Ok(Self::load_from_value(path, package_json))
  }

  pub fn load_from_value(
    path: PathBuf,
    package_json: serde_json::Value,
  ) -> PackageJson {
    // todo(dsherret): avoid all the clones here
    let imports_val = package_json.get("imports");
    let main_val = package_json.get("main");
    let module_val = package_json.get("module");
    let name_val = package_json.get("name");
    let version_val = package_json.get("version");
    let type_val = package_json.get("type");
    let bin = package_json.get("bin").map(ToOwned::to_owned);
    let exports = package_json.get("exports").and_then(|exports| {
      Some(if is_conditional_exports_main_sugar(exports) {
        let mut map = Map::new();
        map.insert(".".to_string(), exports.to_owned());
        map
      } else {
        exports.as_object()?.to_owned()
      })
    });

    let imports = imports_val
      .and_then(|imp| imp.as_object())
      .map(|imp| imp.to_owned());
    let main = main_val.and_then(|s| s.as_str()).map(|s| s.to_string());
    let name = name_val.and_then(|s| s.as_str()).map(|s| s.to_string());
    let version = version_val.and_then(|s| s.as_str()).map(|s| s.to_string());
    let module = module_val.and_then(|s| s.as_str()).map(|s| s.to_string());

    let dependencies = package_json.get("dependencies").and_then(|d| {
      if d.is_object() {
        let deps: IndexMap<String, String> =
          serde_json::from_value(d.to_owned()).unwrap();
        Some(deps)
      } else {
        None
      }
    });
    let dev_dependencies = package_json.get("devDependencies").and_then(|d| {
      if d.is_object() {
        let deps: IndexMap<String, String> =
          serde_json::from_value(d.to_owned()).unwrap();
        Some(deps)
      } else {
        None
      }
    });

    let scripts: Option<IndexMap<String, String>> = package_json
      .get("scripts")
      .and_then(|d| serde_json::from_value(d.to_owned()).ok());

    // Ignore unknown types for forwards compatibility
    let typ = if let Some(t) = type_val {
      if let Some(t) = t.as_str() {
        if t != "module" && t != "commonjs" {
          "none".to_string()
        } else {
          t.to_string()
        }
      } else {
        "none".to_string()
      }
    } else {
      "none".to_string()
    };

    // for typescript, it looks for "typings" first, then "types"
    let types = package_json
      .get("typings")
      .or_else(|| package_json.get("types"))
      .and_then(|t| t.as_str().map(|s| s.to_string()));
    let workspaces = package_json
      .get("workspaces")
      .and_then(|w| w.as_array())
      .map(|w| {
        w.iter()
          .filter_map(|v| v.as_str().map(|s| s.to_string()))
          .collect()
      });

    PackageJson {
      path,
      main,
      name,
      version,
      module,
      typ,
      types,
      exports,
      imports,
      bin,
      dependencies,
      dev_dependencies,
      scripts,
      workspaces,
    }
  }

  pub fn main(&self, referrer_kind: NodeModuleKind) -> Option<&str> {
    let main = if referrer_kind == NodeModuleKind::Esm && self.typ == "module" {
      self.module.as_ref().or(self.main.as_ref())
    } else {
      self.main.as_ref()
    };
    main.map(|m| m.trim()).filter(|m| !m.is_empty())
  }
}

fn is_conditional_exports_main_sugar(exports: &Value) -> bool {
  if exports.is_string() || exports.is_array() {
    return true;
  }

  if exports.is_null() || !exports.is_object() {
    return false;
  }

  let exports_obj = exports.as_object().unwrap();
  let mut is_conditional_sugar = false;
  let mut i = 0;
  for key in exports_obj.keys() {
    let cur_is_conditional_sugar = key.is_empty() || !key.starts_with('.');
    if i == 0 {
      is_conditional_sugar = cur_is_conditional_sugar;
      i += 1;
    } else if is_conditional_sugar != cur_is_conditional_sugar {
      panic!("\"exports\" cannot contains some keys starting with \'.\' and some not.
        The exports object must either be an object of package subpath keys
        or an object of main entry condition name keys only.")
    }
  }

  is_conditional_sugar
}
