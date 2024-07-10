// Copyright 2018-2024 the Deno authors. MIT license.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::future::Future;
use std::path::Path;

use anyhow::Error as AnyError;
use deno_semver::package::PackageReq;
use deno_semver::RangeSetOrTag;
use deno_semver::Version;
use deno_semver::VersionReq;
use import_map::specifier::SpecifierError;
use import_map::ImportMap;
use import_map::ImportMapDiagnostic;
use import_map::ImportMapError;
use import_map::ImportMapWithDiagnostics;
use serde::Deserialize;
use serde::Serialize;
use thiserror::Error;
use url::Url;

use crate::package_json::PackageJsonDepValue;
use crate::package_json::PackageJsonDepValueParseError;
use crate::package_json::PackageJsonDeps;
use crate::package_json::PackageJsonRc;
use crate::sync::new_rc;
use crate::ConfigFile;

use super::UrlRc;
use super::Workspace;

#[derive(Debug)]
struct PkgJsonResolverFolderConfig {
  deps: PackageJsonDeps,
  pkg_json: PackageJsonRc,
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
  #[error(
    "Specifying an import map in a workspace via CLI flags is not implemented."
  )]
  WorkspaceSpecifiedImportMapNotImplemented,
}

/// Whether to resolve dependencies by reading the dependencies list
/// from a package.json
#[derive(
  Debug, Default, Serialize, Deserialize, Copy, Clone, PartialEq, Eq,
)]
pub enum PackageJsonDepResolution {
  /// Resolves based on the dep entries in the package.json.
  #[default]
  Enabled,
  /// Doesn't use the package.json to resolve dependencies. Let's the caller
  /// resolve based on the file system.
  Disabled,
}

#[derive(Debug, Default, Clone)]
pub struct CreateResolverOptions {
  pub pkg_json_dep_resolution: PackageJsonDepResolution,
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
    pkg_json: &'a PackageJsonRc,
    alias: &'a str,
    sub_path: Option<String>,
    dep_result: &'a Result<PackageJsonDepValue, PackageJsonDepValueParseError>,
  },
}

#[derive(Debug, Error)]
pub enum MappedResolutionError {
  #[error(transparent)]
  Specifier(#[from] SpecifierError),
  #[error(transparent)]
  ImportMap(#[from] ImportMapError),
}

impl MappedResolutionError {
  pub fn is_unmapped_bare_specifier(&self) -> bool {
    match self {
      MappedResolutionError::Specifier(err) => match err {
        SpecifierError::InvalidUrl(_) => false,
        SpecifierError::ImportPrefixMissing { .. } => true,
      },
      MappedResolutionError::ImportMap(err) => match err {
        ImportMapError::UnmappedBareSpecifier(_, _) => true,
        ImportMapError::Other(_) => false,
      },
    }
  }
}

#[derive(Error, Debug)]
#[error(transparent)]
pub struct WorkspaceResolvePkgJsonFolderError(
  Box<WorkspaceResolvePkgJsonFolderErrorKind>,
);

impl WorkspaceResolvePkgJsonFolderError {
  pub fn as_kind(&self) -> &WorkspaceResolvePkgJsonFolderErrorKind {
    &self.0
  }

  pub fn into_kind(self) -> WorkspaceResolvePkgJsonFolderErrorKind {
    *self.0
  }
}

impl<E> From<E> for WorkspaceResolvePkgJsonFolderError
where
  WorkspaceResolvePkgJsonFolderErrorKind: From<E>,
{
  fn from(err: E) -> Self {
    WorkspaceResolvePkgJsonFolderError(Box::new(
      WorkspaceResolvePkgJsonFolderErrorKind::from(err),
    ))
  }
}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum WorkspaceResolvePkgJsonFolderErrorKind {
  #[error("Could not find package.json with name '{0}' in workspace.")]
  NotFound(String),
  #[error("Found package.json in workspace, but version '{1}' didn't satisy constraint '{0}'.")]
  VersionNotSatisfied(VersionReq, Version),
}

#[derive(Debug)]
pub struct WorkspaceResolver {
  maybe_import_map: Option<ImportMapWithDiagnostics>,
  pkg_jsons: BTreeMap<UrlRc, PkgJsonResolverFolderConfig>,
  pkg_json_dep_resolution: PackageJsonDepResolution,
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
        Some(SpecifiedImportMap {
          base_url,
          value: import_map,
        }) => {
          if workspace.config_folders.len() > 1 {
            // We're not entirely sure how this should work, so for now we're just surfacing an error.
            // Most likely it should just overwrite the import map.
            return Err(WorkspaceResolverCreateError::WorkspaceSpecifiedImportMapNotImplemented);
          }
          (base_url, import_map)
        }
        None => {
          if !deno_jsons.iter().any(|p| p.is_package())
            && !deno_jsons.iter().any(|c| {
              c.json.import_map.is_some()
                || c.json.scopes.is_some()
                || c.json.imports.is_some()
            })
          {
            // no configs have an import map and none are a package, so exit
            return Ok(None);
          }

          let config_specified_import_map = match root_folder.deno_json.as_ref()
          {
            Some(deno_json) => deno_json
              .to_import_map_value(fetch_text)
              .await
              .map_err(|source| WorkspaceResolverCreateError::ImportMapFetch {
                referrer: deno_json.specifier.clone(),
                source,
              })?
              .unwrap_or_else(|| {
                (
                  Cow::Borrowed(&deno_json.specifier),
                  serde_json::Value::Object(Default::default()),
                )
              }),
            None => (
              Cow::Owned(workspace.root_dir.join("deno.json").unwrap()),
              serde_json::Value::Object(Default::default()),
            ),
          };
          let base_import_map_config = import_map::ext::ImportMapConfig {
            base_url: config_specified_import_map.0.into_owned(),
            import_map_value: config_specified_import_map.1,
          };
          let child_import_map_configs = deno_jsons
            .iter()
            .filter(|f| {
              Some(&f.specifier)
                != root_folder.deno_json.as_ref().map(|c| &c.specifier)
            })
            .map(|config| import_map::ext::ImportMapConfig {
              base_url: config.specifier.clone(),
              import_map_value: {
                // don't include scopes here
                let mut value = serde_json::Map::with_capacity(1);
                if let Some(imports) = &config.json.imports {
                  value.insert("imports".to_string(), imports.clone());
                }
                value.into()
              },
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
          let import_map = import_map::ext::expand_import_map_value(import_map);
          log::debug!(
            "Workspace config generated this import map {}",
            serde_json::to_string_pretty(&import_map).unwrap()
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
    let pkg_jsons = workspace
      .config_folders()
      .iter()
      .filter_map(|(dir_url, f)| {
        let pkg_json = f.pkg_json.clone()?;
        let deps = pkg_json.resolve_local_package_json_deps();
        Some((
          dir_url.clone(),
          PkgJsonResolverFolderConfig { deps, pkg_json },
        ))
      })
      .collect::<BTreeMap<_, _>>();
    Ok(Self {
      pkg_json_dep_resolution: options.pkg_json_dep_resolution,
      maybe_import_map,
      pkg_jsons,
    })
  }

  /// Creates a new WorkspaceResolver from the specified import map and package.jsons.
  ///
  /// Generally, create this from a Workspace instead.
  pub fn new_raw(
    maybe_import_map: Option<ImportMap>,
    pkg_jsons: Vec<PackageJsonRc>,
    pkg_json_dep_resolution: PackageJsonDepResolution,
  ) -> Self {
    let maybe_import_map =
      maybe_import_map.map(|import_map| ImportMapWithDiagnostics {
        import_map,
        diagnostics: Default::default(),
      });
    let pkg_jsons = pkg_jsons
      .into_iter()
      .map(|pkg_json| {
        let deps = pkg_json.resolve_local_package_json_deps();
        (
          new_rc(
            Url::from_directory_path(pkg_json.path.parent().unwrap()).unwrap(),
          ),
          PkgJsonResolverFolderConfig { deps, pkg_json },
        )
      })
      .collect::<BTreeMap<_, _>>();
    Self {
      maybe_import_map,
      pkg_jsons,
      pkg_json_dep_resolution,
    }
  }

  pub fn maybe_import_map(&self) -> Option<&ImportMap> {
    self.maybe_import_map.as_ref().map(|c| &c.import_map)
  }

  pub fn package_jsons(&self) -> impl Iterator<Item = &PackageJsonRc> {
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
    if self.pkg_json_dep_resolution == PackageJsonDepResolution::Enabled {
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

        for (bare_specifier, dep_result) in &pkg_json_folder.deps {
          if let Some(path) = specifier.strip_prefix(bare_specifier) {
            if path.is_empty() || path.starts_with('/') {
              let sub_path = path.strip_prefix('/').unwrap_or(path);
              return Ok(MappedResolution::PackageJson {
                pkg_json: &pkg_json_folder.pkg_json,
                alias: bare_specifier,
                sub_path: if sub_path.is_empty() {
                  None
                } else {
                  Some(sub_path.to_string())
                },
                dep_result,
              });
            }
          }
        }
      }
    }

    // wasn't found, so surface the initial resolve error
    Err(resolve_error)
  }

  pub fn resolve_workspace_pkg_json_folder_for_npm_specifier(
    &self,
    pkg_req: &PackageReq,
  ) -> Option<&Path> {
    let result = self
      .resolve_workspace_pkg_json_folder_for_pkg_json_dep(
        &pkg_req.name,
        &pkg_req.version_req,
      )
      .ok()?;

    if let Some(tag) = pkg_req.version_req.tag() {
      if tag != "workspace" {
        return None;
      }
    }

    Some(result)
  }

  pub fn resolve_workspace_pkg_json_folder_for_pkg_json_dep(
    &self,
    name: &str,
    version_req: &VersionReq,
  ) -> Result<&Path, WorkspaceResolvePkgJsonFolderError> {
    // this is not conditional on pkg_json_dep_resolution because we want
    // to be able to do this resolution to figure out mapping an npm specifier
    // to a workspace folder when using BYONM
    let pkg_json = self
      .package_jsons()
      .find(|p| p.name.as_deref() == Some(name));
    let Some(pkg_json) = pkg_json else {
      return Err(
        WorkspaceResolvePkgJsonFolderErrorKind::NotFound(name.to_string())
          .into(),
      );
    };
    match version_req.inner() {
      RangeSetOrTag::RangeSet(set) => {
        if let Some(version) = pkg_json
          .version
          .as_ref()
          .and_then(|v| Version::parse_from_npm(v).ok())
        {
          if set.satisfies(&version) {
            Ok(pkg_json.dir_path())
          } else {
            Err(
              WorkspaceResolvePkgJsonFolderErrorKind::VersionNotSatisfied(
                version_req.clone(),
                version,
              )
              .into(),
            )
          }
        } else {
          // just match it
          Ok(pkg_json.dir_path())
        }
      }
      RangeSetOrTag::Tag(_) => {
        // always match tags
        Ok(pkg_json.dir_path())
      }
    }
  }

  pub fn pkg_json_dep_resolution(&self) -> PackageJsonDepResolution {
    self.pkg_json_dep_resolution
  }
}

fn enhance_import_map_value_with_workspace_members<'a>(
  mut import_map_value: serde_json::Value,
  deno_jsons: impl Iterator<Item = &'a ConfigFile>,
) -> serde_json::Value {
  let maybe_imports = import_map_value
    .as_object_mut()
    .and_then(|o| o.remove("imports"));
  let mut imports =
    if let Some(serde_json::Value::Object(imports)) = maybe_imports {
      imports
    } else {
      serde_json::Map::new()
    };

  for deno_json in deno_jsons {
    let Some(name) = &deno_json.json.name else {
      continue;
    };
    // todo(dsherret): support and use `@workspace` here instead
    // so it works even when no version is specified
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

#[cfg(test)]
mod test {
  use std::path::Path;
  use std::path::PathBuf;

  use deno_semver::VersionReq;
  use serde_json::json;
  use url::Url;

  use super::*;
  use crate::fs::TestFileSystem;
  use crate::sync::new_rc;
  use crate::workspace::WorkspaceDiscoverOptions;
  use crate::workspace::WorkspaceDiscoverStart;
  use crate::workspace::WorkspaceRc;

  fn root_dir() -> PathBuf {
    if cfg!(windows) {
      PathBuf::from("C:\\Users\\user")
    } else {
      PathBuf::from("/home/user")
    }
  }

  #[tokio::test]
  async fn pkg_json_resolution() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": [
          "a",
          "b",
        ]
      }),
    );
    fs.insert_json(
      root_dir().join("a/deno.json"),
      json!({
        "imports": {
          "b": "./index.js",
        },
      }),
    );
    fs.insert_json(
      root_dir().join("b/package.json"),
      json!({
        "dependencies": {
          "pkg": "npm:pkg@^1.0.0",
        },
      }),
    );
    let workspace = workspace_at_start_dir(&fs, &root_dir());
    let resolver = create_resolver(&workspace).await;
    assert!(resolver.diagnostics().is_empty());
    let resolve = |name: &str, referrer: &str| {
      resolver.resolve(
        name,
        &Url::from_file_path(root_dir().join(referrer)).unwrap(),
      )
    };
    match resolve("pkg", "b/index.js").unwrap() {
      MappedResolution::PackageJson {
        alias,
        sub_path,
        dep_result,
        ..
      } => {
        assert_eq!(alias, "pkg");
        assert_eq!(sub_path, None);
        dep_result.as_ref().unwrap();
      }
      _ => unreachable!(),
    }
  }

  #[tokio::test]
  async fn single_pkg_no_import_map() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "name": "@scope/pkg",
        "version": "1.0.0",
        "exports": "./mod.ts"
      }),
    );
    let workspace = workspace_at_start_dir(&fs, &root_dir());
    let resolver = create_resolver(&workspace).await;
    assert!(resolver.diagnostics().is_empty());
    let result = resolver
      .resolve(
        "@scope/pkg",
        &Url::from_file_path(root_dir().join("file.ts")).unwrap(),
      )
      .unwrap();
    match result {
      MappedResolution::ImportMap(url) => {
        assert_eq!(url, Url::parse("jsr:@scope/pkg@^1.0.0").unwrap());
      }
      _ => unreachable!(),
    }
  }

  #[tokio::test]
  async fn resolve_workspace_pkg_json_folder() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": [
          "a",
          "b",
          "no-version"
        ]
      }),
    );
    fs.insert_json(
      root_dir().join("a/package.json"),
      json!({
        "name": "@scope/a",
        "version": "1.0.0",
      }),
    );
    fs.insert_json(
      root_dir().join("b/package.json"),
      json!({
        "name": "@scope/b",
        "version": "2.0.0",
      }),
    );
    fs.insert_json(
      root_dir().join("no-version/package.json"),
      json!({
        "name": "@scope/no-version",
      }),
    );
    let workspace = workspace_at_start_dir(&fs, &root_dir());
    let resolver = create_resolver(&workspace).await;
    // resolve for pkg json dep
    {
      let resolve = |name: &str, req: &str| {
        resolver.resolve_workspace_pkg_json_folder_for_pkg_json_dep(
          name,
          &VersionReq::parse_from_npm(req).unwrap(),
        )
      };
      assert_eq!(
        resolve("non-existent", "*").map_err(|e| e.into_kind()),
        Err(WorkspaceResolvePkgJsonFolderErrorKind::NotFound(
          "non-existent".to_string()
        ))
      );
      assert_eq!(
        resolve("@scope/a", "6").map_err(|e| e.into_kind()),
        Err(WorkspaceResolvePkgJsonFolderErrorKind::VersionNotSatisfied(
          VersionReq::parse_from_npm("6").unwrap(),
          Version::parse_from_npm("1.0.0").unwrap(),
        ))
      );
      assert_eq!(resolve("@scope/a", "1").unwrap(), root_dir().join("a"));
      assert_eq!(resolve("@scope/a", "*").unwrap(), root_dir().join("a"));
      assert_eq!(
        resolve("@scope/a", "workspace").unwrap(),
        root_dir().join("a")
      );
      assert_eq!(resolve("@scope/b", "2").unwrap(), root_dir().join("b"));
      // just match any tags with the workspace
      assert_eq!(resolve("@scope/a", "latest").unwrap(), root_dir().join("a"));

      // match any version for a pkg with no version
      assert_eq!(
        resolve("@scope/no-version", "1").unwrap(),
        root_dir().join("no-version")
      );
      assert_eq!(
        resolve("@scope/no-version", "20").unwrap(),
        root_dir().join("no-version")
      );
    }
    // resolve for specifier
    {
      let resolve = |pkg_req: &str| {
        resolver.resolve_workspace_pkg_json_folder_for_npm_specifier(
          &PackageReq::from_str(pkg_req).unwrap(),
        )
      };
      assert_eq!(resolve("non-existent@*"), None);
      assert_eq!(
        resolve("@scope/no-version@1").unwrap(),
        root_dir().join("no-version")
      );

      assert_eq!(resolve("@scope/a@workspace").unwrap(), root_dir().join("a"));
      // difference is here, it won't match for a non-workspace tag for an npm specifier
      assert_eq!(resolve("@scope/a@latest"), None);
    }
  }

  #[tokio::test]
  async fn resolve_workspace_pkg_json_workspace_deno_json_import_map() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["*"]
      }),
    );
    fs.insert_json(
      root_dir().join("a/package.json"),
      json!({
        "name": "@scope/a",
        "version": "1.0.0",
      }),
    );
    fs.insert_json(
      root_dir().join("a/deno.json"),
      json!({
        "name": "@scope/jsr-pkg",
        "version": "1.0.0",
        "exports": "./mod.ts"
      }),
    );

    let workspace = workspace_at_start_dir(&fs, &root_dir());
    let resolver = create_resolver(&workspace).await;
    let resolution = resolver
      .resolve(
        "@scope/jsr-pkg",
        &Url::from_file_path(root_dir().join("b.ts")).unwrap(),
      )
      .unwrap();
    match resolution {
      MappedResolution::ImportMap(specifier) => {
        assert_eq!(specifier, Url::parse("jsr:@scope/jsr-pkg@^1.0.0").unwrap());
      }
      _ => unreachable!(),
    }
  }

  #[tokio::test]
  async fn specified_import_map() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(root_dir().join("deno.json"), json!({}));
    let workspace = workspace_at_start_dir(&fs, &root_dir());
    let resolver = workspace
      .create_resolver(
        super::CreateResolverOptions {
          pkg_json_dep_resolution: PackageJsonDepResolution::Enabled,
          specified_import_map: Some(SpecifiedImportMap {
            base_url: Url::from_directory_path(root_dir()).unwrap(),
            value: json!({
              "imports": {
                "b": "./b/mod.ts",
              },
            }),
          }),
        },
        |_| async move { unreachable!() },
      )
      .await
      .unwrap();
    let root = Url::from_directory_path(root_dir()).unwrap();
    match resolver
      .resolve("b", &root.join("main.ts").unwrap())
      .unwrap()
    {
      MappedResolution::ImportMap(url) => {
        assert_eq!(url, root.join("b/mod.ts").unwrap());
      }
      _ => unreachable!(),
    }
  }

  #[tokio::test]
  async fn workspace_specified_import_map() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./a"]
      }),
    );
    fs.insert_json(root_dir().join("a").join("deno.json"), json!({}));
    let workspace = workspace_at_start_dir(&fs, &root_dir());
    let err = workspace
      .create_resolver(
        super::CreateResolverOptions {
          pkg_json_dep_resolution: PackageJsonDepResolution::Enabled,
          specified_import_map: Some(SpecifiedImportMap {
            base_url: Url::from_directory_path(root_dir()).unwrap(),
            value: json!({
              "imports": {
                "b": "./b/mod.ts",
              },
            }),
          }),
        },
        |_| async move { unreachable!() },
      )
      .await
      .unwrap_err();
    assert!(matches!(
      err,
      WorkspaceResolverCreateError::WorkspaceSpecifiedImportMapNotImplemented
    ));
  }

  async fn create_resolver(workspace: &WorkspaceRc) -> WorkspaceResolver {
    workspace
      .create_resolver(
        super::CreateResolverOptions {
          pkg_json_dep_resolution: PackageJsonDepResolution::Enabled,
          specified_import_map: None,
        },
        |_| async move { unreachable!() },
      )
      .await
      .unwrap()
  }

  fn workspace_at_start_dir(
    fs: &TestFileSystem,
    start_dir: &Path,
  ) -> WorkspaceRc {
    new_rc(
      Workspace::discover(
        WorkspaceDiscoverStart::Paths(&[start_dir.to_path_buf()]),
        &WorkspaceDiscoverOptions {
          fs,
          discover_pkg_json: true,
          ..Default::default()
        },
      )
      .unwrap(),
    )
  }
}
