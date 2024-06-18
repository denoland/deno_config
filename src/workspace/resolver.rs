// Copyright 2018-2024 the Deno authors. MIT license.

use std::collections::BTreeMap;
use std::future::Future;
use std::sync::Arc;

use anyhow::Error as AnyError;
use deno_semver::npm::NpmPackageReqReference;
use deno_semver::package::PackageReqReference;
use import_map::ImportMap;
use import_map::ImportMapDiagnostic;
use import_map::ImportMapError;
use import_map::ImportMapWithDiagnostics;
use indexmap::IndexMap;
use thiserror::Error;
use url::Url;

use crate::package_json::PackageJson;
use crate::package_json::PackageJsonDepValueParseError;
use crate::package_json::PackageJsonDeps;
use crate::ConfigFile;

use super::Workspace;

struct DenoJsonResolverFolderConfig {
  import_map: Option<Arc<ImportMap>>,
  config: Arc<ConfigFile>,
}

#[derive(Debug)]
struct PkgJsonResolverFolderConfig {
  deps: PackageJsonDeps,
  pkg_json: Arc<PackageJson>,
}

struct ResolverFolderConfigs {
  deno_json: Option<DenoJsonResolverFolderConfig>,
  pkg_json: Option<PkgJsonResolverFolderConfig>,
}

#[derive(Debug, Error)]
pub enum WorkspaceResolverCreateError {
  #[error("Failed loading import map specified in '{referrer}'")]
  ImportMapFetch {
    referrer: Url,
    #[source]
    source: AnyError,
  },
  #[error(transparent)]
  ImportMap(#[from] import_map::ImportMapError),
}

pub struct SpecifiedImportMap {
  pub base_url: Url,
  pub value: serde_json::Value,
}

pub enum MappedResolution<'a> {
  PackageJson {
    pkg_json: &'a Arc<PackageJson>,
    alias: &'a str,
    req_ref: NpmPackageReqReference,
  },
  ImportMap(Url),
}

impl<'a> MappedResolution<'a> {
  pub fn into_url(self) -> Result<Url, url::ParseError> {
    match self {
      Self::PackageJson { req_ref, .. } => Url::parse(&req_ref.to_string()),
      Self::ImportMap(url) => Ok(url),
    }
  }
}

#[derive(Debug, Error)]
pub enum MappedResolutionError {
  #[error(transparent)]
  ImportMap(#[from] ImportMapError),
  #[error(transparent)]
  PkgJsonDep(#[from] PackageJsonDepValueParseError),
}

#[derive(Debug)]
pub struct WorkspaceResolver {
  import_map: ImportMapWithDiagnostics,
  pkg_jsons: BTreeMap<Url, PkgJsonResolverFolderConfig>,
}

impl WorkspaceResolver {
  pub(crate) async fn from_workspace<
    TReturn: Future<Output = Result<String, AnyError>>,
  >(
    workspace: &Workspace,
    specified_import_map: Option<SpecifiedImportMap>,
    fetch_text: impl Fn(&Url) -> TReturn,
  ) -> Result<Self, WorkspaceResolverCreateError> {
    let (root_dir, root_folder) = workspace.root_folder();
    let deno_jsons = workspace
      .config_folders()
      .iter()
      .filter_map(|(_, f)| f.deno_json.as_ref())
      .collect::<Vec<_>>();
    let base_url = root_folder
      .deno_json
      .as_ref()
      .map(|c| c.specifier.clone())
      .unwrap_or_else(|| root_dir.join("deno.json").unwrap());

    let (import_map_url, import_map) = match specified_import_map {
      // todo(THIS PR): is it ok that if someone does --import-map= that it just
      // overwrites the entire workspace import map?
      Some(SpecifiedImportMap {
        base_url,
        value: import_map,
      }) => (base_url, import_map),
      None => {
        let config_specified_import_map = match root_folder.deno_json.as_ref() {
          Some(config) => config
            .to_import_map_value(fetch_text)
            .await
            .map_err(|source| WorkspaceResolverCreateError::ImportMapFetch {
              referrer: config.specifier.clone(),
              source,
            })?,
          None => None,
        };
        let base_import_map_config = match config_specified_import_map {
          Some((base_url, import_map_value)) => {
            import_map::ext::ImportMapConfig {
              base_url: base_url.into_owned(),
              import_map_value: import_map::ext::expand_import_map_value(
                import_map_value,
              ),
            }
          }
          None => import_map::ext::ImportMapConfig {
            base_url,
            import_map_value: serde_json::Value::Object(Default::default()),
          },
        };
        let child_import_map_configs = deno_jsons
          .iter()
          .filter(|f| {
            Some(&f.specifier)
              != root_folder.deno_json.as_ref().map(|c| &c.specifier)
          })
          .map(|config| import_map::ext::ImportMapConfig {
            base_url: config.specifier.clone(),
            import_map_value: import_map::ext::expand_import_map_value(
              config.to_import_map_value_from_imports(),
            ),
          })
          .collect::<Vec<_>>();
        let (import_map_url, import_map) =
          ::import_map::ext::create_synthetic_import_map(
            base_import_map_config,
            child_import_map_configs,
          );
        let import_map = enhance_import_map_value_with_workspace_members(
          import_map,
          deno_jsons.iter().map(|c| c.as_ref()),
        );
        (import_map_url, import_map)
      }
    };
    let import_map = import_map::parse_from_value(import_map_url, import_map)?;
    let pkg_jsons = workspace
      .config_folders()
      .iter()
      .filter_map(|(dir_url, f)| {
        let pkg_json = f.pkg_json.clone()?;
        let deps = pkg_json.resolve_local_package_json_version_reqs();
        Some((
          dir_url.clone(),
          PkgJsonResolverFolderConfig { deps, pkg_json },
        ))
      })
      .collect::<BTreeMap<_, _>>();
    Ok(Self {
      import_map,
      pkg_jsons,
    })
  }

  /// Creates a new WorkspaceResolver specifically for deno compile.
  pub fn new_for_deno_compile(
    import_map: ImportMap,
    pkg_jsons: Vec<Arc<PackageJson>>,
  ) -> Self {
    let import_map = ImportMapWithDiagnostics {
      import_map,
      diagnostics: Default::default(),
    };
    let pkg_jsons = pkg_jsons
      .into_iter()
      .map(|pkg_json| {
        let deps = pkg_json.resolve_local_package_json_version_reqs();
        (
          Url::from_directory_path(pkg_json.path.parent().unwrap()).unwrap(),
          PkgJsonResolverFolderConfig { deps, pkg_json },
        )
      })
      .collect::<BTreeMap<_, _>>();
    Self {
      import_map,
      pkg_jsons,
    }
  }

  pub fn import_map(&self) -> &ImportMap {
    &self.import_map.import_map
  }

  pub fn package_jsons(&self) -> impl Iterator<Item = &Arc<PackageJson>> {
    self.pkg_jsons.values().map(|c| &c.pkg_json)
  }

  pub fn diagnostics(&self) -> &[ImportMapDiagnostic] {
    &self.import_map.diagnostics
  }

  pub fn resolve<'a>(
    &'a self,
    specifier: &str,
    referrer: &Url,
  ) -> Result<MappedResolution<'a>, MappedResolutionError> {
    // attempt to resolve with the import map first
    let import_map_err =
      match self.import_map.import_map.resolve(specifier, referrer) {
        Ok(value) => return Ok(MappedResolution::ImportMap(value)),
        Err(err) => err,
      };

    // then using the package.json
    let mut previously_found_dir = false;
    for (dir_url, pkg_json_folder) in self.pkg_jsons.iter().rev() {
      if !referrer.as_str().starts_with(dir_url.as_str()) {
        if previously_found_dir {
          break;
        } else {
          continue;
        }
      }
      previously_found_dir = true;

      for (bare_specifier, req_result) in &pkg_json_folder.deps {
        if let Some(path) = specifier.strip_prefix(bare_specifier) {
          if path.is_empty() || path.starts_with('/') {
            let sub_path = path.strip_prefix('/').unwrap_or(path);
            let req = req_result.as_ref().map_err(|e| e.clone())?;
            return Ok(MappedResolution::PackageJson {
              pkg_json: &pkg_json_folder.pkg_json,
              alias: &bare_specifier,
              req_ref: NpmPackageReqReference::new(PackageReqReference {
                req: req.clone(),
                sub_path: if sub_path.is_empty() {
                  None
                } else {
                  Some(sub_path.to_string())
                },
              }),
            });
          }
        }
      }
    }

    // wasn't found, so maybe surface the import map error
    Err(import_map_err.into())
  }
}

fn enhance_import_map_value_with_workspace_members<'a>(
  mut import_map_value: serde_json::Value,
  deno_jsons: impl Iterator<Item = &'a ConfigFile>,
) -> serde_json::Value {
  let mut imports = if let Some(serde_json::Value::Object(imports)) =
    import_map_value.get("imports").as_ref()
  {
    imports.clone() // todo(dsherret): do not clone here
  } else {
    serde_json::Map::new()
  };

  for deno_json in deno_jsons {
    let Some(name) = &deno_json.json.name else {
      continue;
    };
    let Some(version) = &deno_json.json.version else {
      continue;
    };
    // Don't override existings, explicit imports
    if imports.contains_key(name) {
      continue;
    }

    imports.insert(
      name.to_string(),
      serde_json::Value::String(format!("jsr:{}@^{}", name, version)),
    );
  }

  import_map_value["imports"] = serde_json::Value::Object(imports);
  import_map_value
}
