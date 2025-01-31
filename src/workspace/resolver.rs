// Copyright 2018-2024 the Deno authors. MIT license.

use crate::deno_json::ConfigFile;
use crate::deno_json::ConfigFileError;
use crate::sync::new_rc;
use crate::workspace::Workspace;
use deno_error::JsError;
use deno_package_json::PackageJsonDepValue;
use deno_package_json::PackageJsonDepValueParseError;
use deno_package_json::PackageJsonDepWorkspaceReq;
use deno_package_json::PackageJsonDepsRc;
use deno_package_json::PackageJsonRc;
use deno_path_util::url_from_directory_path;
use deno_path_util::url_to_file_path;
use deno_semver::jsr::JsrPackageReqReference;
use deno_semver::package::PackageReq;
use deno_semver::RangeSetOrTag;
use deno_semver::Version;
use deno_semver::VersionReq;
use import_map::specifier::SpecifierError;
use import_map::ImportMap;
use import_map::ImportMapDiagnostic;
use import_map::ImportMapError;
use import_map::ImportMapErrorKind;
use import_map::ImportMapWithDiagnostics;
use indexmap::IndexMap;
use serde::Deserialize;
use serde::Serialize;
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::fmt;
use std::path::Path;
use sys_traits::FsMetadata;
use sys_traits::FsRead;
use thiserror::Error;
use url::Url;

use super::UrlRc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolverWorkspaceJsrPackage {
  pub base: Url,
  pub name: String,
  pub version: Option<Version>,
  pub exports: IndexMap<String, String>,
  pub is_patch: bool,
}

#[derive(Debug)]
struct PkgJsonResolverFolderConfig {
  deps: PackageJsonDepsRc,
  pkg_json: PackageJsonRc,
}

#[derive(Debug, Error, JsError)]
pub enum WorkspaceResolverCreateError {
  #[class(inherit)]
  #[error("Failed loading import map specified in '{referrer}'")]
  ImportMapFetch {
    referrer: Url,
    #[source]
    #[inherit]
    source: Box<ConfigFileError>,
  },
  #[class(inherit)]
  #[error(transparent)]
  ImportMap(
    #[from]
    #[inherit]
    ImportMapError,
  ),
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MappedResolutionDiagnostic {
  ConstraintNotMatchedLocalVersion {
    /// If it was for a patch (true) or workspace (false) member.
    is_patch: bool,
    reference: JsrPackageReqReference,
    local_version: Version,
  },
}

impl std::fmt::Display for MappedResolutionDiagnostic {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::ConstraintNotMatchedLocalVersion {
        is_patch,
        reference,
        local_version,
      } => {
        write!(
          f,
          "{0} '{1}@{2}' was not used because it did not match '{1}@{3}'",
          if *is_patch {
            "Patch"
          } else {
            "Workspace member"
          },
          reference.req().name,
          local_version,
          reference.req().version_req
        )
      }
    }
  }
}

#[derive(Debug, Clone)]
pub enum MappedResolution<'a> {
  Normal {
    specifier: Url,
    maybe_diagnostic: Option<Box<MappedResolutionDiagnostic>>,
  },
  ImportMap {
    specifier: Url,
    maybe_diagnostic: Option<Box<MappedResolutionDiagnostic>>,
  },
  WorkspaceJsrPackage {
    specifier: Url,
    pkg_req_ref: JsrPackageReqReference,
  },
  /// Resolved a bare specifier to a package.json that was a workspace member.
  WorkspaceNpmPackage {
    target_pkg_json: &'a PackageJsonRc,
    pkg_name: &'a str,
    sub_path: Option<String>,
  },
  PackageJson {
    pkg_json: &'a PackageJsonRc,
    alias: &'a str,
    sub_path: Option<String>,
    dep_result: &'a Result<PackageJsonDepValue, PackageJsonDepValueParseError>,
  },
}

#[derive(Debug, Clone, Error, JsError)]
#[class(type)]
pub enum WorkspaceResolveError {
  #[error("Failed joining '{}' to '{}'. {:#}", .sub_path, .base, .error)]
  InvalidExportPath {
    base: Url,
    sub_path: String,
    error: url::ParseError,
  },
  #[error("Unknown export '{}' for '{}'.\n  Package exports:\n{}", export_name, package_name, .exports.iter().map(|e| format!(" * {}", e)).collect::<Vec<_>>().join("\n"))]
  UnknownExport {
    package_name: String,
    export_name: String,
    exports: Vec<String>,
  },
}

#[derive(Debug, Error, JsError)]
pub enum MappedResolutionError {
  #[class(inherit)]
  #[error(transparent)]
  Specifier(#[from] SpecifierError),
  #[class(inherit)]
  #[error(transparent)]
  ImportMap(#[from] ImportMapError),
  #[class(inherit)]
  #[error(transparent)]
  Workspace(#[from] WorkspaceResolveError),
}

impl MappedResolutionError {
  pub fn is_unmapped_bare_specifier(&self) -> bool {
    match self {
      MappedResolutionError::Specifier(err) => match err {
        SpecifierError::InvalidUrl(_) => false,
        SpecifierError::ImportPrefixMissing { .. } => true,
      },
      MappedResolutionError::ImportMap(err) => {
        matches!(**err, ImportMapErrorKind::UnmappedBareSpecifier(_, _))
      }
      MappedResolutionError::Workspace(_) => false,
    }
  }
}

#[derive(Error, Debug, JsError)]
#[class(inherit)]
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

#[derive(Debug, Error, JsError, Clone, PartialEq, Eq)]
#[class(type)]
pub enum WorkspaceResolvePkgJsonFolderErrorKind {
  #[error("Could not find package.json with name '{0}' in workspace.")]
  NotFound(String),
  #[error("Found package.json in workspace, but version '{1}' didn't satisy constraint '{0}'.")]
  VersionNotSatisfied(VersionReq, Version),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompilerOptionsRootDirsDiagnostic {
  InvalidType(Url),
  InvalidEntryType(Url, usize),
  UnexpectedError(Url, String),
  UnexpectedEntryError(Url, usize, String),
}

impl fmt::Display for CompilerOptionsRootDirsDiagnostic {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::InvalidType(s) => write!(f, "Invalid value for \"compilerOptions.rootDirs\" (\"{s}\"). Expected a string."),
      Self::InvalidEntryType(s, i) => write!(f, "Invalid value for \"compilerOptions.rootDirs[{i}]\" (\"{s}\"). Expected a string."),
      Self::UnexpectedError(s, message) => write!(f, "Unexpected error while parsing \"compilerOptions.rootDirs\" (\"{s}\"): {message}"),
      Self::UnexpectedEntryError(s, i, message) => write!(f, "Unexpected error while parsing \"compilerOptions.rootDirs[{i}]\" (\"{s}\"): {message}"),
    }
  }
}

#[derive(Debug)]
struct CompilerOptionsRootDirsResolver<TSys: FsMetadata> {
  root_dirs_from_root: Vec<Url>,
  root_dirs_by_member: BTreeMap<Url, Option<Vec<Url>>>,
  diagnostics: Vec<CompilerOptionsRootDirsDiagnostic>,
  sys: TSys,
}

impl<TSys: FsMetadata> CompilerOptionsRootDirsResolver<TSys> {
  fn from_workspace(workspace: &Workspace, sys: TSys) -> Self {
    let mut diagnostics: Vec<CompilerOptionsRootDirsDiagnostic> = Vec::new();
    fn get_root_dirs(
      config_file: &ConfigFile,
      dir_url: &Url,
      diagnostics: &mut Vec<CompilerOptionsRootDirsDiagnostic>,
    ) -> Option<Vec<Url>> {
      let dir_path = url_to_file_path(dir_url)
        .inspect_err(|err| {
          diagnostics.push(CompilerOptionsRootDirsDiagnostic::UnexpectedError(
            config_file.specifier.clone(),
            err.to_string(),
          ));
        })
        .ok()?;
      let root_dirs = config_file
        .json
        .compiler_options
        .as_ref()?
        .as_object()?
        .get("rootDirs")?
        .as_array();
      if root_dirs.is_none() {
        diagnostics.push(CompilerOptionsRootDirsDiagnostic::InvalidType(
          config_file.specifier.clone(),
        ));
      }
      let root_dirs = root_dirs?
        .iter()
        .enumerate()
        .filter_map(|(i, s)| {
          let s = s.as_str();
          if s.is_none() {
            diagnostics.push(
              CompilerOptionsRootDirsDiagnostic::InvalidEntryType(
                config_file.specifier.clone(),
                i,
              ),
            );
          }
          url_from_directory_path(&dir_path.join(s?))
            .inspect_err(|err| {
              diagnostics.push(
                CompilerOptionsRootDirsDiagnostic::UnexpectedEntryError(
                  config_file.specifier.clone(),
                  i,
                  err.to_string(),
                ),
              );
            })
            .ok()
        })
        .collect();
      Some(root_dirs)
    }
    let root_deno_json = workspace.root_deno_json();
    let root_dirs_from_root = root_deno_json
      .and_then(|c| {
        let root_dir_url = c
          .specifier
          .join(".")
          .inspect_err(|err| {
            diagnostics.push(
              CompilerOptionsRootDirsDiagnostic::UnexpectedError(
                c.specifier.clone(),
                err.to_string(),
              ),
            );
          })
          .ok()?;
        get_root_dirs(c, &root_dir_url, &mut diagnostics)
      })
      .unwrap_or_default();
    let root_dirs_by_member = workspace
      .resolver_deno_jsons()
      .filter_map(|c| {
        if let Some(root_deno_json) = root_deno_json {
          if c.specifier == root_deno_json.specifier {
            return None;
          }
        }
        let dir_url = c
          .specifier
          .join(".")
          .inspect_err(|err| {
            diagnostics.push(
              CompilerOptionsRootDirsDiagnostic::UnexpectedError(
                c.specifier.clone(),
                err.to_string(),
              ),
            );
          })
          .ok()?;
        let root_dirs = get_root_dirs(c, &dir_url, &mut diagnostics);
        Some((dir_url, root_dirs))
      })
      .collect();
    Self {
      root_dirs_from_root,
      root_dirs_by_member,
      diagnostics,
      sys,
    }
  }

  fn new_raw(
    root_dirs_from_root: Vec<Url>,
    root_dirs_by_member: BTreeMap<Url, Option<Vec<Url>>>,
    sys: TSys,
  ) -> Self {
    Self {
      root_dirs_from_root,
      root_dirs_by_member,
      diagnostics: Default::default(),
      sys,
    }
  }

  fn resolve_types(&self, specifier: &Url, referrer: &Url) -> Option<Url> {
    if specifier.scheme() != "file" || referrer.scheme() != "file" {
      return None;
    }
    let root_dirs = self
      .root_dirs_by_member
      .iter()
      .rfind(|(s, _)| referrer.as_str().starts_with(s.as_str()))
      .and_then(|(_, r)| r.as_ref())
      .unwrap_or(&self.root_dirs_from_root);
    let (matched_root_dir, suffix) = root_dirs
      .iter()
      .filter_map(|r| {
        let suffix = specifier.as_str().strip_prefix(r.as_str())?;
        Some((r, suffix))
      })
      .max_by_key(|(r, _)| r.as_str().len())?;
    for root_dir in root_dirs {
      if root_dir == matched_root_dir {
        continue;
      }
      let Ok(candidate_specifier) = root_dir.join(suffix) else {
        continue;
      };
      let Ok(candidate_path) = url_to_file_path(&candidate_specifier) else {
        continue;
      };
      if self.sys.fs_is_file_no_err(&candidate_path) {
        return Some(candidate_specifier);
      }
    }
    None
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ResolutionKind {
  /// Resolving for code that will be executed.
  Execution,
  /// Resolving for code that will be used for type information.
  Types,
}

impl ResolutionKind {
  pub fn is_types(&self) -> bool {
    *self == ResolutionKind::Types
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WorkspaceResolverDiagnostic<'a> {
  ImportMap(&'a ImportMapDiagnostic),
  CompilerOptionsRootDirs(&'a CompilerOptionsRootDirsDiagnostic),
}

impl fmt::Display for WorkspaceResolverDiagnostic<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::ImportMap(d) => write!(f, "Import map: {d}"),
      Self::CompilerOptionsRootDirs(d) => d.fmt(f),
    }
  }
}

#[derive(Debug)]
pub struct WorkspaceResolver<TSys: FsMetadata + FsRead> {
  workspace_root: UrlRc,
  jsr_pkgs: Vec<ResolverWorkspaceJsrPackage>,
  maybe_import_map: Option<ImportMapWithDiagnostics>,
  pkg_jsons: BTreeMap<UrlRc, PkgJsonResolverFolderConfig>,
  pkg_json_dep_resolution: PackageJsonDepResolution,
  compiler_options_root_dirs_resolver: CompilerOptionsRootDirsResolver<TSys>,
}

impl<TSys: FsMetadata + FsRead> WorkspaceResolver<TSys> {
  pub(crate) fn from_workspace(
    workspace: &Workspace,
    sys: TSys,
    options: CreateResolverOptions,
  ) -> Result<Self, WorkspaceResolverCreateError> {
    fn resolve_import_map(
      sys: &impl FsRead,
      workspace: &Workspace,
      specified_import_map: Option<SpecifiedImportMap>,
    ) -> Result<Option<ImportMapWithDiagnostics>, WorkspaceResolverCreateError>
    {
      let root_deno_json = workspace.root_deno_json();
      let deno_jsons = workspace.resolver_deno_jsons().collect::<Vec<_>>();

      let (import_map_url, import_map) = match specified_import_map {
        Some(SpecifiedImportMap {
          base_url,
          value: import_map,
        }) => (base_url, import_map),
        None => {
          if !deno_jsons.iter().any(|p| p.is_package())
            && !deno_jsons.iter().any(|c| {
              c.json.import_map.is_some()
                || c.json.scopes.is_some()
                || c.json.imports.is_some()
                || c
                  .json
                  .compiler_options
                  .as_ref()
                  .and_then(|v| v.as_object()?.get("rootDirs")?.as_array())
                  .is_some_and(|a| a.len() > 1)
            })
          {
            // no configs have an import map and none are a package, so exit
            return Ok(None);
          }

          let config_specified_import_map = match root_deno_json.as_ref() {
            Some(deno_json) => deno_json
              .to_import_map_value(sys)
              .map_err(|source| WorkspaceResolverCreateError::ImportMapFetch {
                referrer: deno_json.specifier.clone(),
                source: Box::new(source),
              })?
              .unwrap_or_else(|| {
                (
                  Cow::Borrowed(&deno_json.specifier),
                  serde_json::Value::Object(Default::default()),
                )
              }),
            None => (
              Cow::Owned(workspace.root_dir().join("deno.json").unwrap()),
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
                != root_deno_json.as_ref().map(|c| &c.specifier)
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
      resolve_import_map(&sys, workspace, options.specified_import_map)?;
    let jsr_pkgs = workspace.resolver_jsr_pkgs().collect::<Vec<_>>();
    let pkg_jsons = workspace
      .resolver_pkg_jsons()
      .map(|(dir_url, pkg_json)| {
        let deps = pkg_json.resolve_local_package_json_deps();
        (
          dir_url.clone(),
          PkgJsonResolverFolderConfig {
            deps: deps.clone(),
            pkg_json: pkg_json.clone(),
          },
        )
      })
      .collect::<BTreeMap<_, _>>();

    let compiler_options_root_dirs_resolver =
      CompilerOptionsRootDirsResolver::from_workspace(workspace, sys);

    Ok(Self {
      workspace_root: workspace.root_dir().clone(),
      pkg_json_dep_resolution: options.pkg_json_dep_resolution,
      jsr_pkgs,
      maybe_import_map,
      pkg_jsons,
      compiler_options_root_dirs_resolver,
    })
  }

  /// Creates a new WorkspaceResolver from the specified import map and package.jsons.
  ///
  /// Generally, create this from a Workspace instead.
  #[allow(clippy::too_many_arguments)]
  pub fn new_raw(
    workspace_root: UrlRc,
    maybe_import_map: Option<ImportMap>,
    jsr_pkgs: Vec<ResolverWorkspaceJsrPackage>,
    pkg_jsons: Vec<PackageJsonRc>,
    pkg_json_dep_resolution: PackageJsonDepResolution,
    root_dirs_from_root: Vec<Url>,
    root_dirs_by_member: BTreeMap<Url, Option<Vec<Url>>>,
    sys: TSys,
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
            url_from_directory_path(pkg_json.path.parent().unwrap()).unwrap(),
          ),
          PkgJsonResolverFolderConfig {
            deps: deps.clone(),
            pkg_json,
          },
        )
      })
      .collect::<BTreeMap<_, _>>();
    let compiler_options_root_dirs_resolver =
      CompilerOptionsRootDirsResolver::new_raw(
        root_dirs_from_root,
        root_dirs_by_member,
        sys,
      );
    Self {
      workspace_root,
      jsr_pkgs,
      maybe_import_map,
      pkg_jsons,
      pkg_json_dep_resolution,
      compiler_options_root_dirs_resolver,
    }
  }

  /// Prepare the workspace resolver for serialization
  ///
  /// The most significant preparation involves converting
  /// absolute paths into relative (based on `root_dir_url`).
  /// It also takes care of pre-serializing non-serde internal data.
  pub fn to_serializable(
    &self,
    root_dir_url: &Url,
  ) -> SerializableWorkspaceResolver {
    let root_dir_url = BaseUrl(root_dir_url);
    SerializableWorkspaceResolver {
      import_map: self.maybe_import_map().map(|i| {
        SerializedWorkspaceResolverImportMap {
          specifier: root_dir_url.make_relative_if_descendant(i.base_url()),
          json: Cow::Owned(i.to_json()),
        }
      }),
      jsr_pkgs: self
        .jsr_packages()
        .map(|pkg| SerializedResolverWorkspaceJsrPackage {
          relative_base: root_dir_url.make_relative_if_descendant(&pkg.base),
          name: Cow::Borrowed(&pkg.name),
          version: Cow::Borrowed(&pkg.version),
          exports: Cow::Borrowed(&pkg.exports),
        })
        .collect(),
      package_jsons: self
        .package_jsons()
        .map(|pkg_json| {
          (
            root_dir_url
              .make_relative_if_descendant(&pkg_json.specifier())
              .into_owned(),
            serde_json::to_value(pkg_json).unwrap(),
          )
        })
        .collect(),
      pkg_json_resolution: self.pkg_json_dep_resolution(),
      root_dirs_from_root: self
        .compiler_options_root_dirs_resolver
        .root_dirs_from_root
        .iter()
        .map(|s| root_dir_url.make_relative_if_descendant(s))
        .collect(),
      root_dirs_by_member: self
        .compiler_options_root_dirs_resolver
        .root_dirs_by_member
        .iter()
        .map(|(s, r)| {
          (
            root_dir_url.make_relative_if_descendant(s),
            r.as_ref().map(|r| {
              r.iter()
                .map(|s| root_dir_url.make_relative_if_descendant(s))
                .collect()
            }),
          )
        })
        .collect(),
    }
  }

  /// Deserialize a `WorkspaceResolver`
  ///
  /// Deserialization of `WorkspaceResolver`s is made in two steps. First
  /// the serialized data must be deserialized in to `SerializableWorkspaceResolver`
  /// (usually with serde), and then this method converts it into a `WorkspaceResolver`.
  ///
  /// This second step involves mainly converting the relative paths within
  /// `SerializableWorkspaceResolver` into absolute paths using `root_dir_url`.
  pub fn try_from_serializable(
    root_dir_url: Url,
    serializable_workspace_resolver: SerializableWorkspaceResolver,
    sys: TSys,
  ) -> Result<Self, ImportMapError> {
    let import_map = match serializable_workspace_resolver.import_map {
      Some(import_map) => Some(
        import_map::parse_from_json_with_options(
          root_dir_url.join(&import_map.specifier).unwrap(),
          &import_map.json,
          import_map::ImportMapOptions {
            address_hook: None,
            expand_imports: true,
          },
        )?
        .import_map,
      ),
      None => None,
    };
    let pkg_jsons = serializable_workspace_resolver
      .package_jsons
      .into_iter()
      .map(|(relative_path, json)| {
        let path =
          url_to_file_path(&root_dir_url.join(&relative_path).unwrap())
            .unwrap();
        let pkg_json =
          deno_package_json::PackageJson::load_from_value(path, json);
        PackageJsonRc::new(pkg_json)
      })
      .collect();
    let jsr_packages = serializable_workspace_resolver
      .jsr_pkgs
      .into_iter()
      .map(|pkg| ResolverWorkspaceJsrPackage {
        is_patch: false, // only used for enhancing the diagnostics, which are discarded when serializing
        base: root_dir_url.join(&pkg.relative_base).unwrap(),
        name: pkg.name.into_owned(),
        version: pkg.version.into_owned(),
        exports: pkg.exports.into_owned(),
      })
      .collect();
    let root_dirs_from_root = serializable_workspace_resolver
      .root_dirs_from_root
      .iter()
      .map(|s| root_dir_url.join(s).unwrap())
      .collect();
    let root_dirs_by_member = serializable_workspace_resolver
      .root_dirs_by_member
      .iter()
      .map(|(s, r)| {
        (
          root_dir_url.join(s).unwrap(),
          r.as_ref()
            .map(|r| r.iter().map(|s| root_dir_url.join(s).unwrap()).collect()),
        )
      })
      .collect();
    Ok(Self::new_raw(
      UrlRc::new(root_dir_url),
      import_map,
      jsr_packages,
      pkg_jsons,
      serializable_workspace_resolver.pkg_json_resolution,
      root_dirs_from_root,
      root_dirs_by_member,
      sys,
    ))
  }

  pub fn maybe_import_map(&self) -> Option<&ImportMap> {
    self.maybe_import_map.as_ref().map(|c| &c.import_map)
  }

  pub fn package_jsons(&self) -> impl Iterator<Item = &PackageJsonRc> {
    self.pkg_jsons.values().map(|c| &c.pkg_json)
  }

  pub fn jsr_packages(
    &self,
  ) -> impl Iterator<Item = &ResolverWorkspaceJsrPackage> {
    self.jsr_pkgs.iter()
  }

  pub fn diagnostics(&self) -> Vec<WorkspaceResolverDiagnostic<'_>> {
    self
      .compiler_options_root_dirs_resolver
      .diagnostics
      .iter()
      .map(WorkspaceResolverDiagnostic::CompilerOptionsRootDirs)
      .chain(
        self
          .maybe_import_map
          .as_ref()
          .iter()
          .flat_map(|c| &c.diagnostics)
          .map(WorkspaceResolverDiagnostic::ImportMap),
      )
      .collect()
  }

  pub fn resolve<'a>(
    &'a self,
    specifier: &str,
    referrer: &Url,
    resolution_kind: ResolutionKind,
  ) -> Result<MappedResolution<'a>, MappedResolutionError> {
    // 1. Attempt to resolve with the import map and normally first
    let resolve_error = match &self.maybe_import_map {
      Some(import_map) => {
        match import_map.import_map.resolve(specifier, referrer) {
          Ok(mut value) => {
            if resolution_kind.is_types() {
              if let Some(specifier) = self
                .compiler_options_root_dirs_resolver
                .resolve_types(&value, referrer)
              {
                value = specifier
              }
            }
            return self.maybe_resolve_specifier_to_workspace_jsr_pkg(
              MappedResolution::ImportMap {
                specifier: value,
                maybe_diagnostic: None,
              },
            );
          }
          Err(err) => MappedResolutionError::ImportMap(err),
        }
      }
      None => {
        match import_map::specifier::resolve_import(specifier, referrer) {
          Ok(mut value) => {
            if resolution_kind.is_types() {
              if let Some(specifier) = self
                .compiler_options_root_dirs_resolver
                .resolve_types(&value, referrer)
              {
                value = specifier
              }
            }
            return self.maybe_resolve_specifier_to_workspace_jsr_pkg(
              MappedResolution::Normal {
                specifier: value,
                maybe_diagnostic: None,
              },
            );
          }
          Err(err) => MappedResolutionError::Specifier(err),
        }
      }
    };

    // 2. Try to resolve the bare specifier to a workspace member
    if resolve_error.is_unmapped_bare_specifier() {
      for member in &self.jsr_pkgs {
        if let Some(path) = specifier.strip_prefix(&member.name) {
          if path.is_empty() || path.starts_with('/') {
            let path = path.strip_prefix('/').unwrap_or(path);
            let pkg_req_ref = match JsrPackageReqReference::from_str(&format!(
              "jsr:{}{}/{}",
              member.name,
              member
                .version
                .as_ref()
                .map(|v| format!("@^{}", v))
                .unwrap_or_else(String::new),
              path
            )) {
              Ok(pkg_req_ref) => pkg_req_ref,
              Err(_) => {
                // Ignore the error as it will be surfaced as a diagnostic
                // in workspace.diagnostics() routine.
                continue;
              }
            };
            return self.resolve_workspace_jsr_pkg(member, pkg_req_ref);
          }
        }
      }
    }

    if self.pkg_json_dep_resolution == PackageJsonDepResolution::Enabled {
      // 2. Attempt to resolve from the package.json dependencies.
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

        for (bare_specifier, dep_result) in pkg_json_folder
          .deps
          .dependencies
          .iter()
          .chain(pkg_json_folder.deps.dev_dependencies.iter())
        {
          if let Some(path) = specifier.strip_prefix(bare_specifier.as_str()) {
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

      // 3. Finally try to resolve to a workspace npm package if inside the workspace.
      if referrer.as_str().starts_with(self.workspace_root.as_str()) {
        for pkg_json_folder in self.pkg_jsons.values() {
          let Some(name) = &pkg_json_folder.pkg_json.name else {
            continue;
          };
          let Some(path) = specifier.strip_prefix(name) else {
            continue;
          };
          if path.is_empty() || path.starts_with('/') {
            let sub_path = path.strip_prefix('/').unwrap_or(path);
            return Ok(MappedResolution::WorkspaceNpmPackage {
              target_pkg_json: &pkg_json_folder.pkg_json,
              pkg_name: name,
              sub_path: if sub_path.is_empty() {
                None
              } else {
                Some(sub_path.to_string())
              },
            });
          }
        }
      }
    }

    // wasn't found, so surface the initial resolve error
    Err(resolve_error)
  }

  fn maybe_resolve_specifier_to_workspace_jsr_pkg<'a>(
    &'a self,
    resolution: MappedResolution<'a>,
  ) -> Result<MappedResolution<'a>, MappedResolutionError> {
    let specifier = match resolution {
      MappedResolution::Normal { ref specifier, .. } => specifier,
      MappedResolution::ImportMap { ref specifier, .. } => specifier,
      _ => return Ok(resolution),
    };
    if specifier.scheme() != "jsr" {
      return Ok(resolution);
    }
    let mut maybe_diagnostic = None;
    if let Ok(package_req_ref) =
      JsrPackageReqReference::from_specifier(specifier)
    {
      for pkg in &self.jsr_pkgs {
        if pkg.name == package_req_ref.req().name {
          if let Some(version) = &pkg.version {
            if package_req_ref.req().version_req.matches(version) {
              return self.resolve_workspace_jsr_pkg(pkg, package_req_ref);
            } else {
              maybe_diagnostic = Some(Box::new(
                MappedResolutionDiagnostic::ConstraintNotMatchedLocalVersion {
                  is_patch: pkg.is_patch,
                  reference: package_req_ref.clone(),
                  local_version: version.clone(),
                },
              ));
            }
          } else {
            // always resolve to workspace packages with no version
            return self.resolve_workspace_jsr_pkg(pkg, package_req_ref);
          }
        }
      }
    }
    Ok(match resolution {
      MappedResolution::Normal { specifier, .. } => MappedResolution::Normal {
        specifier,
        maybe_diagnostic,
      },
      MappedResolution::ImportMap { specifier, .. } => {
        MappedResolution::ImportMap {
          specifier,
          maybe_diagnostic,
        }
      }
      _ => return Ok(resolution),
    })
  }

  fn resolve_workspace_jsr_pkg<'a>(
    &'a self,
    pkg: &'a ResolverWorkspaceJsrPackage,
    pkg_req_ref: JsrPackageReqReference,
  ) -> Result<MappedResolution<'a>, MappedResolutionError> {
    let export_name = pkg_req_ref.export_name();
    match pkg.exports.get(export_name.as_ref()) {
      Some(sub_path) => match pkg.base.join(sub_path) {
        Ok(specifier) => Ok(MappedResolution::WorkspaceJsrPackage {
          specifier,
          pkg_req_ref,
        }),
        Err(err) => Err(
          WorkspaceResolveError::InvalidExportPath {
            base: pkg.base.clone(),
            sub_path: sub_path.to_string(),
            error: err,
          }
          .into(),
        ),
      },
      None => Err(
        WorkspaceResolveError::UnknownExport {
          package_name: pkg.name.clone(),
          export_name: export_name.to_string(),
          exports: pkg.exports.keys().cloned().collect(),
        }
        .into(),
      ),
    }
  }

  pub fn resolve_workspace_pkg_json_folder_for_npm_specifier(
    &self,
    pkg_req: &PackageReq,
  ) -> Option<&Path> {
    if pkg_req.version_req.tag().is_some() {
      return None;
    }

    self
      .resolve_workspace_pkg_json_folder_for_pkg_json_dep(
        &pkg_req.name,
        &PackageJsonDepWorkspaceReq::VersionReq(pkg_req.version_req.clone()),
      )
      .ok()
  }

  pub fn resolve_workspace_pkg_json_folder_for_pkg_json_dep(
    &self,
    name: &str,
    workspace_version_req: &PackageJsonDepWorkspaceReq,
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
    match workspace_version_req {
      PackageJsonDepWorkspaceReq::VersionReq(version_req) => {
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
      PackageJsonDepWorkspaceReq::Tilde | PackageJsonDepWorkspaceReq::Caret => {
        // always match tilde and caret requirements
        Ok(pkg_json.dir_path())
      }
    }
  }

  pub fn pkg_json_dep_resolution(&self) -> PackageJsonDepResolution {
    self.pkg_json_dep_resolution
  }
}

#[derive(Deserialize, Serialize)]
pub struct SerializedWorkspaceResolverImportMap<'a> {
  #[serde(borrow)]
  pub specifier: Cow<'a, str>,
  #[serde(borrow)]
  pub json: Cow<'a, str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializedResolverWorkspaceJsrPackage<'a> {
  #[serde(borrow)]
  pub relative_base: Cow<'a, str>,
  #[serde(borrow)]
  pub name: Cow<'a, str>,
  pub version: Cow<'a, Option<Version>>,
  pub exports: Cow<'a, IndexMap<String, String>>,
}

#[derive(Deserialize, Serialize)]
pub struct SerializableWorkspaceResolver<'a> {
  #[serde(borrow)]
  pub import_map: Option<SerializedWorkspaceResolverImportMap<'a>>,
  #[serde(borrow)]
  pub jsr_pkgs: Vec<SerializedResolverWorkspaceJsrPackage<'a>>,
  pub package_jsons: Vec<(String, serde_json::Value)>,
  pub pkg_json_resolution: PackageJsonDepResolution,
  pub root_dirs_from_root: Vec<Cow<'a, str>>,
  pub root_dirs_by_member: BTreeMap<Cow<'a, str>, Option<Vec<Cow<'a, str>>>>,
}

#[derive(Debug, Clone, Copy)]
struct BaseUrl<'a>(&'a Url);

impl BaseUrl<'_> {
  fn make_relative_if_descendant<'a>(&self, target: &'a Url) -> Cow<'a, str> {
    if target.scheme() != "file" {
      return Cow::Borrowed(target.as_str());
    }

    match self.0.make_relative(target) {
      Some(relative) => {
        if relative.starts_with("../") {
          Cow::Borrowed(target.as_str())
        } else {
          Cow::Owned(relative)
        }
      }
      None => Cow::Borrowed(target.as_str()),
    }
  }
}

#[cfg(test)]
mod test {
  use std::path::Path;
  use std::path::PathBuf;

  use deno_path_util::url_from_directory_path;
  use deno_path_util::url_from_file_path;
  use deno_semver::VersionReq;
  use serde_json::json;
  use sys_traits::impls::InMemorySys;
  use url::Url;

  use super::*;
  use crate::workspace::test::UnreachableSys;
  use crate::workspace::WorkspaceDirectory;
  use crate::workspace::WorkspaceDiscoverOptions;
  use crate::workspace::WorkspaceDiscoverStart;

  fn root_dir() -> PathBuf {
    if cfg!(windows) {
      PathBuf::from("C:\\Users\\user")
    } else {
      PathBuf::from("/home/user")
    }
  }

  #[test]
  fn pkg_json_resolution() {
    let sys = InMemorySys::default();
    sys.fs_insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": [
          "a",
          "b",
          "c",
        ]
      }),
    );
    sys.fs_insert_json(
      root_dir().join("a/deno.json"),
      json!({
        "imports": {
          "b": "./index.js",
        },
      }),
    );
    sys.fs_insert_json(
      root_dir().join("b/package.json"),
      json!({
        "dependencies": {
          "pkg": "npm:pkg@^1.0.0",
        },
      }),
    );
    sys.fs_insert_json(
      root_dir().join("c/package.json"),
      json!({
        "name": "pkg",
        "version": "0.5.0"
      }),
    );
    let workspace = workspace_at_start_dir(&sys, &root_dir());
    let resolver = create_resolver(&workspace);
    assert_eq!(resolver.diagnostics(), Vec::new());
    let resolve = |name: &str, referrer: &str| {
      resolver.resolve(
        name,
        &url_from_file_path(&deno_path_util::normalize_path(
          root_dir().join(referrer),
        ))
        .unwrap(),
        ResolutionKind::Execution,
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
      value => unreachable!("{:?}", value),
    }
    match resolve("pkg/sub-path", "b/index.js").unwrap() {
      MappedResolution::PackageJson {
        alias,
        sub_path,
        dep_result,
        ..
      } => {
        assert_eq!(alias, "pkg");
        assert_eq!(sub_path.unwrap(), "sub-path");
        dep_result.as_ref().unwrap();
      }
      value => unreachable!("{:?}", value),
    }

    // pkg is not a dependency in this folder, so it should resolve
    // to the workspace member
    match resolve("pkg", "index.js").unwrap() {
      MappedResolution::WorkspaceNpmPackage {
        pkg_name,
        sub_path,
        target_pkg_json,
      } => {
        assert_eq!(pkg_name, "pkg");
        assert_eq!(sub_path, None);
        assert_eq!(target_pkg_json.dir_path(), root_dir().join("c"));
      }
      _ => unreachable!(),
    }
    match resolve("pkg/sub-path", "index.js").unwrap() {
      MappedResolution::WorkspaceNpmPackage {
        pkg_name,
        sub_path,
        target_pkg_json,
      } => {
        assert_eq!(pkg_name, "pkg");
        assert_eq!(sub_path.unwrap(), "sub-path");
        assert_eq!(target_pkg_json.dir_path(), root_dir().join("c"));
      }
      _ => unreachable!(),
    }

    // won't resolve the package outside the workspace
    assert!(resolve("pkg", "../outside-workspace.js").is_err());
  }

  #[test]
  fn single_pkg_no_import_map() {
    let sys = InMemorySys::default();
    sys.fs_insert_json(
      root_dir().join("deno.json"),
      json!({
        "name": "@scope/pkg",
        "version": "1.0.0",
        "exports": "./mod.ts"
      }),
    );
    let workspace = workspace_at_start_dir(&sys, &root_dir());
    let resolver = create_resolver(&workspace);
    assert_eq!(resolver.diagnostics(), Vec::new());
    let result = resolver
      .resolve(
        "@scope/pkg",
        &url_from_file_path(&root_dir().join("file.ts")).unwrap(),
        ResolutionKind::Execution,
      )
      .unwrap();
    match result {
      MappedResolution::WorkspaceJsrPackage { specifier, .. } => {
        assert_eq!(
          specifier,
          url_from_file_path(&root_dir().join("mod.ts")).unwrap()
        );
      }
      _ => unreachable!(),
    }
  }

  #[test]
  fn resolve_workspace_pkg_json_folder() {
    let sys = InMemorySys::default();
    sys.fs_insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": [
          "a",
          "b",
          "no-version"
        ]
      }),
    );
    sys.fs_insert_json(
      root_dir().join("a/package.json"),
      json!({
        "name": "@scope/a",
        "version": "1.0.0",
      }),
    );
    sys.fs_insert_json(
      root_dir().join("b/package.json"),
      json!({
        "name": "@scope/b",
        "version": "2.0.0",
      }),
    );
    sys.fs_insert_json(
      root_dir().join("no-version/package.json"),
      json!({
        "name": "@scope/no-version",
      }),
    );
    let workspace = workspace_at_start_dir(&sys, &root_dir());
    let resolver = create_resolver(&workspace);
    // resolve for pkg json dep
    {
      let resolve = |name: &str, req: &str| {
        resolver.resolve_workspace_pkg_json_folder_for_pkg_json_dep(
          name,
          &PackageJsonDepWorkspaceReq::VersionReq(
            VersionReq::parse_from_npm(req).unwrap(),
          ),
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

      // won't match for tags
      assert_eq!(resolve("@scope/a@workspace"), None);
      assert_eq!(resolve("@scope/a@latest"), None);
    }
  }

  #[test]
  fn resolve_workspace_pkg_json_workspace_deno_json_import_map() {
    let sys = InMemorySys::default();
    sys.fs_insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["*"]
      }),
    );
    sys.fs_insert_json(
      root_dir().join("a/package.json"),
      json!({
        "name": "@scope/a",
        "version": "1.0.0",
      }),
    );
    sys.fs_insert_json(
      root_dir().join("a/deno.json"),
      json!({
        "name": "@scope/jsr-pkg",
        "version": "1.0.0",
        "exports": "./mod.ts"
      }),
    );

    let workspace = workspace_at_start_dir(&sys, &root_dir());
    let resolver = create_resolver(&workspace);
    {
      let resolution = resolver
        .resolve(
          "@scope/jsr-pkg",
          &url_from_file_path(&root_dir().join("b.ts")).unwrap(),
          ResolutionKind::Execution,
        )
        .unwrap();
      match resolution {
        MappedResolution::WorkspaceJsrPackage { specifier, .. } => {
          assert_eq!(
            specifier,
            url_from_file_path(&root_dir().join("a/mod.ts")).unwrap()
          );
        }
        _ => unreachable!(),
      }
    }
    {
      let resolution_err = resolver
        .resolve(
          "@scope/jsr-pkg/not-found-export",
          &url_from_file_path(&root_dir().join("b.ts")).unwrap(),
          ResolutionKind::Execution,
        )
        .unwrap_err();
      match resolution_err {
        MappedResolutionError::Workspace(
          WorkspaceResolveError::UnknownExport {
            package_name,
            export_name,
            exports,
          },
        ) => {
          assert_eq!(package_name, "@scope/jsr-pkg");
          assert_eq!(export_name, "./not-found-export");
          assert_eq!(exports, vec!["."]);
        }
        _ => unreachable!(),
      }
    }
  }

  #[test]
  fn resolve_compiler_options_root_dirs() {
    let sys = InMemorySys::default();
    sys.fs_insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["member", "member2"],
        "compilerOptions": {
          "rootDirs": ["member", "member2", "member2_types"],
        },
      }),
    );
    // Overrides `rootDirs` from workspace root.
    sys.fs_insert_json(
      root_dir().join("member/deno.json"),
      json!({
        "compilerOptions": {
          "rootDirs": ["foo", "foo_types"],
        },
      }),
    );
    // Use `rootDirs` from workspace root.
    sys.fs_insert_json(root_dir().join("member2/deno.json"), json!({}));
    sys.fs_insert(root_dir().join("member/foo_types/import.ts"), "");
    sys.fs_insert(root_dir().join("member2_types/import.ts"), "");
    // This file should be ignored. It would be used if `member/deno.json` had
    // no `rootDirs`.
    sys.fs_insert(root_dir().join("member2_types/foo/import.ts"), "");

    let workspace_dir = workspace_at_start_dir(&sys, &root_dir());
    let resolver = workspace_dir
      .workspace
      .create_resolver(
        sys.clone(),
        super::CreateResolverOptions {
          pkg_json_dep_resolution: PackageJsonDepResolution::Enabled,
          specified_import_map: None,
        },
      )
      .unwrap();
    let root_dir_url = workspace_dir.workspace.root_dir();

    let referrer = root_dir_url.join("member/foo/mod.ts").unwrap();
    let resolution = resolver
      .resolve("./import.ts", &referrer, ResolutionKind::Types)
      .unwrap();
    let MappedResolution::ImportMap { specifier, .. } = &resolution else {
      unreachable!("{:#?}", &resolution);
    };
    assert_eq!(
      specifier.as_str(),
      root_dir_url
        .join("member/foo_types/import.ts")
        .unwrap()
        .as_str()
    );

    let referrer = root_dir_url.join("member2/mod.ts").unwrap();
    let resolution = resolver
      .resolve("./import.ts", &referrer, ResolutionKind::Types)
      .unwrap();
    let MappedResolution::ImportMap { specifier, .. } = &resolution else {
      unreachable!("{:#?}", &resolution);
    };
    assert_eq!(
      specifier.as_str(),
      root_dir_url
        .join("member2_types/import.ts")
        .unwrap()
        .as_str()
    );

    // Ignore rootDirs for `ResolutionKind::Execution`.
    let referrer = root_dir_url.join("member/foo/mod.ts").unwrap();
    let resolution = resolver
      .resolve("./import.ts", &referrer, ResolutionKind::Execution)
      .unwrap();
    let MappedResolution::ImportMap { specifier, .. } = &resolution else {
      unreachable!("{:#?}", &resolution);
    };
    assert_eq!(
      specifier.as_str(),
      root_dir_url.join("member/foo/import.ts").unwrap().as_str()
    );

    // Ignore rootDirs for `ResolutionKind::Execution`.
    let referrer = root_dir_url.join("member2/mod.ts").unwrap();
    let resolution = resolver
      .resolve("./import.ts", &referrer, ResolutionKind::Execution)
      .unwrap();
    let MappedResolution::ImportMap { specifier, .. } = &resolution else {
      unreachable!("{:#?}", &resolution);
    };
    assert_eq!(
      specifier.as_str(),
      root_dir_url.join("member2/import.ts").unwrap().as_str()
    );
  }

  #[test]
  fn specified_import_map() {
    let sys = InMemorySys::default();
    sys.fs_insert_json(root_dir().join("deno.json"), json!({}));
    let workspace_dir = workspace_at_start_dir(&sys, &root_dir());
    let resolver = workspace_dir
      .workspace
      .create_resolver(
        UnreachableSys,
        super::CreateResolverOptions {
          pkg_json_dep_resolution: PackageJsonDepResolution::Enabled,
          specified_import_map: Some(SpecifiedImportMap {
            base_url: url_from_directory_path(&root_dir()).unwrap(),
            value: json!({
              "imports": {
                "b": "./b/mod.ts",
              },
            }),
          }),
        },
      )
      .unwrap();
    let root = url_from_directory_path(&root_dir()).unwrap();
    match resolver
      .resolve(
        "b",
        &root.join("main.ts").unwrap(),
        ResolutionKind::Execution,
      )
      .unwrap()
    {
      MappedResolution::ImportMap { specifier, .. } => {
        assert_eq!(specifier, root.join("b/mod.ts").unwrap());
      }
      _ => unreachable!(),
    }
  }

  #[test]
  fn workspace_specified_import_map() {
    let sys = InMemorySys::default();
    sys.fs_insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./a"]
      }),
    );
    sys.fs_insert_json(root_dir().join("a").join("deno.json"), json!({}));
    let workspace_dir = workspace_at_start_dir(&sys, &root_dir());
    workspace_dir
      .workspace
      .create_resolver(
        UnreachableSys,
        super::CreateResolverOptions {
          pkg_json_dep_resolution: PackageJsonDepResolution::Enabled,
          specified_import_map: Some(SpecifiedImportMap {
            base_url: url_from_directory_path(&root_dir()).unwrap(),
            value: json!({
              "imports": {
                "b": "./b/mod.ts",
              },
            }),
          }),
        },
      )
      .unwrap();
  }

  #[test]
  fn resolves_patch_member_with_version() {
    let sys = InMemorySys::default();
    sys.fs_insert_json(
      root_dir().join("deno.json"),
      json!({
        "patch": ["../patch"]
      }),
    );
    sys.fs_insert_json(
      root_dir().join("../patch/deno.json"),
      json!({
        "name": "@scope/patch",
        "version": "1.0.0",
        "exports": "./mod.ts"
      }),
    );
    let workspace_dir = workspace_at_start_dir(&sys, &root_dir());
    let resolver = workspace_dir
      .workspace
      .create_resolver(
        UnreachableSys,
        super::CreateResolverOptions {
          pkg_json_dep_resolution: PackageJsonDepResolution::Enabled,
          specified_import_map: None,
        },
      )
      .unwrap();
    let root = url_from_directory_path(&root_dir()).unwrap();
    match resolver
      .resolve(
        "@scope/patch",
        &root.join("main.ts").unwrap(),
        ResolutionKind::Execution,
      )
      .unwrap()
    {
      MappedResolution::WorkspaceJsrPackage { specifier, .. } => {
        assert_eq!(specifier, root.join("../patch/mod.ts").unwrap());
      }
      _ => unreachable!(),
    }
    // matching version
    match resolver
      .resolve(
        "jsr:@scope/patch@1",
        &root.join("main.ts").unwrap(),
        ResolutionKind::Execution,
      )
      .unwrap()
    {
      MappedResolution::WorkspaceJsrPackage { specifier, .. } => {
        assert_eq!(specifier, root.join("../patch/mod.ts").unwrap());
      }
      _ => unreachable!(),
    }
    // not matching version
    match resolver
      .resolve(
        "jsr:@scope/patch@2",
        &root.join("main.ts").unwrap(),
        ResolutionKind::Execution,
      )
      .unwrap()
    {
      MappedResolution::ImportMap {
        specifier,
        maybe_diagnostic,
      } => {
        assert_eq!(specifier, Url::parse("jsr:@scope/patch@2").unwrap());
        assert_eq!(
          maybe_diagnostic,
          Some(Box::new(
            MappedResolutionDiagnostic::ConstraintNotMatchedLocalVersion {
              is_patch: true,
              reference: JsrPackageReqReference::from_str("jsr:@scope/patch@2")
                .unwrap(),
              local_version: Version::parse_from_npm("1.0.0").unwrap(),
            }
          ))
        );
      }
      _ => unreachable!(),
    }
  }

  #[test]
  fn resolves_patch_member_no_version() {
    let sys = InMemorySys::default();
    sys.fs_insert_json(
      root_dir().join("deno.json"),
      json!({
        "patch": ["../patch"]
      }),
    );
    sys.fs_insert_json(
      root_dir().join("../patch/deno.json"),
      json!({
        "name": "@scope/patch",
        "exports": "./mod.ts"
      }),
    );
    let workspace_dir = workspace_at_start_dir(&sys, &root_dir());
    let resolver = workspace_dir
      .workspace
      .create_resolver(
        UnreachableSys,
        super::CreateResolverOptions {
          pkg_json_dep_resolution: PackageJsonDepResolution::Enabled,
          specified_import_map: None,
        },
      )
      .unwrap();
    let root = url_from_directory_path(&root_dir()).unwrap();
    match resolver
      .resolve(
        "@scope/patch",
        &root.join("main.ts").unwrap(),
        ResolutionKind::Execution,
      )
      .unwrap()
    {
      MappedResolution::WorkspaceJsrPackage { specifier, .. } => {
        assert_eq!(specifier, root.join("../patch/mod.ts").unwrap());
      }
      _ => unreachable!(),
    }
    // always resolves, no matter what version
    match resolver
      .resolve(
        "jsr:@scope/patch@12",
        &root.join("main.ts").unwrap(),
        ResolutionKind::Execution,
      )
      .unwrap()
    {
      MappedResolution::WorkspaceJsrPackage { specifier, .. } => {
        assert_eq!(specifier, root.join("../patch/mod.ts").unwrap());
      }
      _ => unreachable!(),
    }
  }

  #[test]
  fn resolves_workspace_member() {
    let sys = InMemorySys::default();
    sys.fs_insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member"]
      }),
    );
    sys.fs_insert_json(
      root_dir().join("./member/deno.json"),
      json!({
        "name": "@scope/member",
        "version": "1.0.0",
        "exports": "./mod.ts"
      }),
    );
    let workspace_dir = workspace_at_start_dir(&sys, &root_dir());
    let resolver = workspace_dir
      .workspace
      .create_resolver(
        UnreachableSys,
        super::CreateResolverOptions {
          pkg_json_dep_resolution: PackageJsonDepResolution::Enabled,
          specified_import_map: None,
        },
      )
      .unwrap();
    let root = url_from_directory_path(&root_dir()).unwrap();
    match resolver
      .resolve(
        "@scope/member",
        &root.join("main.ts").unwrap(),
        ResolutionKind::Execution,
      )
      .unwrap()
    {
      MappedResolution::WorkspaceJsrPackage { specifier, .. } => {
        assert_eq!(specifier, root.join("./member/mod.ts").unwrap());
      }
      _ => unreachable!(),
    }
    // matching version
    match resolver
      .resolve(
        "jsr:@scope/member@1",
        &root.join("main.ts").unwrap(),
        ResolutionKind::Execution,
      )
      .unwrap()
    {
      MappedResolution::WorkspaceJsrPackage { specifier, .. } => {
        assert_eq!(specifier, root.join("./member/mod.ts").unwrap());
      }
      _ => unreachable!(),
    }
    // not matching version
    match resolver
      .resolve(
        "jsr:@scope/member@2",
        &root.join("main.ts").unwrap(),
        ResolutionKind::Execution,
      )
      .unwrap()
    {
      MappedResolution::ImportMap {
        specifier,
        maybe_diagnostic,
      } => {
        assert_eq!(specifier, Url::parse("jsr:@scope/member@2").unwrap());
        assert_eq!(
          maybe_diagnostic,
          Some(Box::new(
            MappedResolutionDiagnostic::ConstraintNotMatchedLocalVersion {
              is_patch: false,
              reference: JsrPackageReqReference::from_str(
                "jsr:@scope/member@2"
              )
              .unwrap(),
              local_version: Version::parse_from_npm("1.0.0").unwrap(),
            }
          ))
        );
      }
      _ => unreachable!(),
    }
  }

  #[test]
  fn resolves_patch_workspace() {
    let sys = InMemorySys::default();
    sys.fs_insert_json(
      root_dir().join("deno.json"),
      json!({
        "imports": {
          "@std/fs": "jsr:@std/fs@0.200.0"
        },
        "patch": ["../patch"]
      }),
    );
    sys.fs_insert_json(
      root_dir().join("../patch/deno.json"),
      json!({
        "workspace": ["./member"]
      }),
    );
    sys.fs_insert_json(
      root_dir().join("../patch/member/deno.json"),
      json!({
        "name": "@scope/patch",
        "version": "1.0.0",
        "exports": "./mod.ts",
        "imports": {
          "@std/fs": "jsr:@std/fs@1"
        }
      }),
    );
    let workspace_dir = workspace_at_start_dir(&sys, &root_dir());
    let resolver = workspace_dir
      .workspace
      .create_resolver(
        UnreachableSys,
        super::CreateResolverOptions {
          pkg_json_dep_resolution: PackageJsonDepResolution::Enabled,
          specified_import_map: None,
        },
      )
      .unwrap();
    let root = url_from_directory_path(&root_dir()).unwrap();
    match resolver
      .resolve(
        "jsr:@scope/patch@1",
        &root.join("main.ts").unwrap(),
        ResolutionKind::Execution,
      )
      .unwrap()
    {
      MappedResolution::WorkspaceJsrPackage { specifier, .. } => {
        assert_eq!(specifier, root.join("../patch/member/mod.ts").unwrap());
      }
      _ => unreachable!(),
    }
    // resolving @std/fs from root
    match resolver
      .resolve(
        "@std/fs",
        &root.join("main.ts").unwrap(),
        ResolutionKind::Execution,
      )
      .unwrap()
    {
      MappedResolution::ImportMap { specifier, .. } => {
        assert_eq!(specifier, Url::parse("jsr:@std/fs@0.200.0").unwrap());
      }
      _ => unreachable!(),
    }
    // resolving @std/fs in patched package
    match resolver
      .resolve(
        "@std/fs",
        &root.join("../patch/member/mod.ts").unwrap(),
        ResolutionKind::Execution,
      )
      .unwrap()
    {
      MappedResolution::ImportMap { specifier, .. } => {
        assert_eq!(specifier, Url::parse("jsr:@std/fs@1").unwrap());
      }
      _ => unreachable!(),
    }
  }

  #[test]
  fn invalid_package_name_with_slashes() {
    let sys = InMemorySys::default();
    sys.fs_insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./libs/math"]
      }),
    );
    sys.fs_insert_json(
      root_dir().join("libs/math/deno.json"),
      json!({
        "name": "@deno-test/libs/math", // Invalid package name containing slashes
        "version": "1.0.0",
        "exports": "./mod.ts"
      }),
    );
    let workspace = workspace_at_start_dir(&sys, &root_dir());
    let resolver = create_resolver(&workspace);
    let result = resolver.resolve(
      "@deno-test/libs/math",
      &url_from_file_path(&root_dir().join("main.ts")).unwrap(),
      ResolutionKind::Execution,
    );
    // Resolve shouldn't panic and tt should result in unmapped
    // bare specifier error as the package name is invalid.
    assert!(result.err().unwrap().is_unmapped_bare_specifier());

    let diagnostics = workspace.workspace.diagnostics();
    assert_eq!(diagnostics.len(), 1);
    assert!(diagnostics
      .first()
      .unwrap()
      .to_string()
      .starts_with(r#"Invalid workspace member name "@deno-test/libs/math"."#));
  }

  fn create_resolver(
    workspace_dir: &WorkspaceDirectory,
  ) -> WorkspaceResolver<UnreachableSys> {
    workspace_dir
      .workspace
      .create_resolver(
        UnreachableSys,
        super::CreateResolverOptions {
          pkg_json_dep_resolution: PackageJsonDepResolution::Enabled,
          specified_import_map: None,
        },
      )
      .unwrap()
  }

  fn workspace_at_start_dir(
    sys: &InMemorySys,
    start_dir: &Path,
  ) -> WorkspaceDirectory {
    WorkspaceDirectory::discover(
      sys,
      WorkspaceDiscoverStart::Paths(&[start_dir.to_path_buf()]),
      &WorkspaceDiscoverOptions {
        discover_pkg_json: true,
        ..Default::default()
      },
    )
    .unwrap()
  }
}
