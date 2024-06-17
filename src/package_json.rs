// Copyright 2018-2024 the Deno authors. MIT license.

use std::path::PathBuf;

use deno_semver::npm::NpmVersionReqParseError;
use deno_semver::package::PackageReq;
use deno_semver::VersionReq;
use indexmap::IndexMap;
use serde::Serialize;
use serde_json::Map;
use serde_json::Value;
use thiserror::Error;

#[derive(Debug, Error, Clone)]
pub enum PackageJsonDepValueParseError {
  #[error(transparent)]
  VersionReq(#[from] NpmVersionReqParseError),
  #[error("Not implemented scheme '{scheme}'")]
  Unsupported { scheme: String },
}

pub type PackageJsonDeps =
  IndexMap<String, Result<PackageReq, PackageJsonDepValueParseError>>;

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

  /// Gets an application level package.json's npm package requirements.
  pub fn resolve_local_package_json_version_reqs(&self) -> PackageJsonDeps {
    /// Gets the name and raw version constraint for a registry info or
    /// package.json dependency entry taking into account npm package aliases.
    fn parse_dep_entry_name_and_raw_version<'a>(
      key: &'a str,
      value: &'a str,
    ) -> (&'a str, &'a str) {
      if let Some(package_and_version) = value.strip_prefix("npm:") {
        if let Some((name, version)) = package_and_version.rsplit_once('@') {
          // if empty, then the name was scoped and there's no version
          if name.is_empty() {
            (package_and_version, "*")
          } else {
            (name, version)
          }
        } else {
          (package_and_version, "*")
        }
      } else {
        (key, value)
      }
    }

    fn parse_entry(
      key: &str,
      value: &str,
    ) -> Result<PackageReq, PackageJsonDepValueParseError> {
      if value.starts_with("workspace:")
        || value.starts_with("file:")
        || value.starts_with("git:")
        || value.starts_with("http:")
        || value.starts_with("https:")
      {
        return Err(PackageJsonDepValueParseError::Unsupported {
          scheme: value.split(':').next().unwrap().to_string(),
        });
      }
      let (name, version_req) =
        parse_dep_entry_name_and_raw_version(key, value);
      let result = VersionReq::parse_from_npm(version_req);
      match result {
        Ok(version_req) => Ok(PackageReq {
          name: name.to_string(),
          version_req,
        }),
        Err(err) => Err(PackageJsonDepValueParseError::VersionReq(err)),
      }
    }

    fn insert_deps(
      deps: Option<&IndexMap<String, String>>,
      result: &mut PackageJsonDeps,
    ) {
      if let Some(deps) = deps {
        for (key, value) in deps {
          result
            .entry(key.to_string())
            .or_insert_with(|| parse_entry(key, value));
        }
      }
    }

    let deps = self.dependencies.as_ref();
    let dev_deps = self.dev_dependencies.as_ref();
    let mut result = IndexMap::new();

    // favors the deps over dev_deps
    insert_deps(deps, &mut result);
    insert_deps(dev_deps, &mut result);

    result
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
