// Copyright 2018-2024 the Deno authors. MIT license.

use std::collections::BTreeMap;
use std::future::Future;
use std::sync::Arc;

use anyhow::Error as AnyError;
use deno_semver::npm::NpmPackageReqReference;
use deno_semver::package::PackageReqReference;
use import_map::specifier::SpecifierError;
use import_map::ImportMap;
use import_map::ImportMapDiagnostic;
use import_map::ImportMapError;
use import_map::ImportMapWithDiagnostics;
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

#[derive(Debug, Default, Clone)]
pub struct CreateResolverOptions {
  /// Whether to resolve dependencies by reading the dependencies list
  /// from a package.json
  ///
  /// This should only be set when a node_modules folder doesn't exist
  /// as node resolution should be used otherwise.
  pub pkg_json_dep_resolution: bool,
  pub specified_import_map: Option<SpecifiedImportMap>,
}

#[derive(Debug, Clone)]
pub struct SpecifiedImportMap {
  pub base_url: Url,
  pub value: serde_json::Value,
}

#[derive(Debug, Clone)]
pub enum MappedResolution<'a> {
  Normal(Url),
  ImportMap(Url),
  PackageJson {
    pkg_json: &'a Arc<PackageJson>,
    alias: &'a str,
    req_ref: NpmPackageReqReference,
  },
}

impl<'a> MappedResolution<'a> {
  pub fn into_url(self) -> Result<Url, url::ParseError> {
    match self {
      Self::Normal(url) | Self::ImportMap(url) => Ok(url),
      Self::PackageJson { req_ref, .. } => Url::parse(&req_ref.to_string()),
    }
  }
}

#[derive(Debug, Error)]
pub enum MappedResolutionError {
  #[error(transparent)]
  Specifier(#[from] SpecifierError),
  #[error(transparent)]
  ImportMap(#[from] ImportMapError),
  #[error(transparent)]
  PkgJsonDep(#[from] PackageJsonDepValueParseError),
}

impl MappedResolutionError {
  pub fn is_unmapped_bare_specifier(&self) -> bool {
    match self {
        MappedResolutionError::Specifier(err) => match err {
            SpecifierError::InvalidUrl(_) => false,
            SpecifierError::ImportPrefixMissing { .. } => {
              true
            },
        },
        MappedResolutionError::ImportMap(err) => match err {
            ImportMapError::UnmappedBareSpecifier(_, _) => true,
            ImportMapError::Other(_) => false,
        },
        MappedResolutionError::PkgJsonDep(_) => false,
    }
  }
}

#[derive(Debug)]
pub struct WorkspaceResolver {
  maybe_import_map: Option<ImportMapWithDiagnostics>,
  pkg_jsons: BTreeMap<Arc<Url>, PkgJsonResolverFolderConfig>,
}

impl WorkspaceResolver {
  pub(crate) async fn from_workspace<
    TReturn: Future<Output = Result<String, AnyError>>,
  >(
    workspace: &Workspace,
    options: CreateResolverOptions,
    fetch_text: impl Fn(&Url) -> TReturn,
  ) -> Result<Self, WorkspaceResolverCreateError> {
    async fn resolve_import_map<
      TReturn: Future<Output = Result<String, AnyError>>,
    >(
      workspace: &Workspace,
      specified_import_map: Option<SpecifiedImportMap>,
      fetch_text: impl Fn(&Url) -> TReturn,
    ) -> Result<Option<ImportMapWithDiagnostics>, WorkspaceResolverCreateError>
    {
      let root_folder = workspace.root_folder().1;
      let deno_jsons = workspace
        .config_folders()
        .iter()
        .filter_map(|(_, f)| f.deno_json.as_ref())
        .collect::<Vec<_>>();

      let (import_map_url, import_map) = match specified_import_map {
        // todo(THIS PR): is it ok that if someone does --import-map= that it just
        // overwrites the entire workspace import map?
        Some(SpecifiedImportMap {
          base_url,
          value: import_map,
        }) => (base_url, import_map),
        None => {
          let Some(config) = root_folder.deno_json.as_ref() else {
            return Ok(None);
          };
          let config_specified_import_map = config
            .to_import_map_value(fetch_text)
            .await
            .map_err(|source| WorkspaceResolverCreateError::ImportMapFetch {
              referrer: config.specifier.clone(),
              source,
            })?;
          let base_import_map_config = match config_specified_import_map {
            Some((base_url, import_map_value)) => {
              import_map::ext::ImportMapConfig {
                base_url: base_url.into_owned(),
                import_map_value: import_map::ext::expand_import_map_value(
                  import_map_value,
                ),
              }
            }
            None => {
              if !deno_jsons.iter().any(|c| {
                c.json.import_map.is_some()
                  || c.json.scopes.is_some()
                  || c.json.imports.is_some()
              }) {
                // no configs have an import map, so exit
                return Ok(None);
              }

              import_map::ext::ImportMapConfig {
                base_url: config.specifier.clone(),
                import_map_value: serde_json::Value::Object(Default::default()),
              }
            }
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
      Ok(Some(import_map::parse_from_value(
        import_map_url,
        import_map,
      )?))
    }

    let maybe_import_map =
      resolve_import_map(workspace, options.specified_import_map, fetch_text)
        .await?;
    let pkg_jsons = if options.pkg_json_dep_resolution {
      workspace
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
        .collect::<BTreeMap<_, _>>()
    } else {
      BTreeMap::default()
    };
    Ok(Self {
      maybe_import_map,
      pkg_jsons,
    })
  }

  /// Creates a new WorkspaceResolver from the specified import map and package.jsons.
  ///
  /// Generally, create this from a Workspace instead.
  pub fn new_raw(
    maybe_import_map: Option<ImportMap>,
    pkg_jsons: Vec<Arc<PackageJson>>,
  ) -> Self {
    let maybe_import_map =
      maybe_import_map.map(|import_map| ImportMapWithDiagnostics {
        import_map,
        diagnostics: Default::default(),
      });
    let pkg_jsons = pkg_jsons
      .into_iter()
      .map(|pkg_json| {
        let deps = pkg_json.resolve_local_package_json_version_reqs();
        (
          Arc::new(
            Url::from_directory_path(pkg_json.path.parent().unwrap()).unwrap(),
          ),
          PkgJsonResolverFolderConfig { deps, pkg_json },
        )
      })
      .collect::<BTreeMap<_, _>>();
    Self {
      maybe_import_map,
      pkg_jsons,
    }
  }

  pub fn maybe_import_map(&self) -> Option<&ImportMap> {
    self.maybe_import_map.as_ref().map(|c| &c.import_map)
  }

  pub fn package_jsons(&self) -> impl Iterator<Item = &Arc<PackageJson>> {
    self.pkg_jsons.values().map(|c| &c.pkg_json)
  }

  pub fn diagnostics(&self) -> &[ImportMapDiagnostic] {
    self
      .maybe_import_map
      .as_ref()
      .map(|c| &c.diagnostics as &[ImportMapDiagnostic])
      .unwrap_or(&[])
  }

  pub fn resolve<'a>(
    &'a self,
    specifier: &str,
    referrer: &Url,
  ) -> Result<MappedResolution<'a>, MappedResolutionError> {
    // attempt to resolve with the import map and normally first
    let resolve_error = match &self.maybe_import_map {
      Some(import_map) => {
        match import_map.import_map.resolve(specifier, referrer) {
          Ok(value) => return Ok(MappedResolution::ImportMap(value)),
          Err(err) => MappedResolutionError::ImportMap(err),
        }
      }
      None => {
        match import_map::specifier::resolve_import(specifier, referrer) {
          Ok(value) => return Ok(MappedResolution::Normal(value)),
          Err(err) => MappedResolutionError::Specifier(err),
        }
      }
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

    // wasn't found, so surface the initial resolve error
    Err(resolve_error)
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
