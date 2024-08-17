// Copyright 2018-2024 the Deno authors. MIT license.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::future::Future;
use std::path::Path;
use std::path::PathBuf;

use anyhow::bail;
use anyhow::Context;
use anyhow::Error as AnyError;
use deno_package_json::PackageJson;
use deno_package_json::PackageJsonLoadError;
use deno_package_json::PackageJsonRc;
use deno_semver::package::PackageNv;
use deno_semver::package::PackageReq;
use deno_semver::RangeSetOrTag;
use deno_semver::Version;
use deno_semver::VersionReq;
use discovery::discover_workspace_config_files;
use discovery::ConfigFileDiscovery;
use discovery::ConfigFolder;
use discovery::DenoOrPkgJson;
use indexmap::IndexMap;
use thiserror::Error;
use url::Url;

use crate::deno_json::get_ts_config_for_emit;
use crate::deno_json::BenchConfig;
use crate::deno_json::ConfigFile;
use crate::deno_json::ConfigFileRc;
use crate::deno_json::ConfigFileReadError;
use crate::deno_json::ConfigParseOptions;
use crate::deno_json::FmtConfig;
use crate::deno_json::FmtOptionsConfig;
use crate::deno_json::IgnoredCompilerOptions;
use crate::deno_json::JsxImportSourceConfig;
use crate::deno_json::LintConfig;
use crate::deno_json::LintOptionsConfig;
use crate::deno_json::LintRulesConfig;
use crate::deno_json::PatchConfigParseError;
use crate::deno_json::PublishConfig;
use crate::deno_json::Task;
use crate::deno_json::TestConfig;
use crate::deno_json::TsConfigForEmit;
use crate::deno_json::TsConfigType;
use crate::deno_json::WorkspaceConfigParseError;
use crate::glob::FilePatterns;
use crate::glob::PathOrPattern;
use crate::glob::PathOrPatternParseError;
use crate::glob::PathOrPatternSet;
use crate::sync::new_rc;
use crate::SpecifierToFilePathError;

mod discovery;
mod resolver;

pub use resolver::CreateResolverOptions;
pub use resolver::MappedResolution;
pub use resolver::MappedResolutionDiagnostic;
pub use resolver::MappedResolutionError;
pub use resolver::PackageJsonDepResolution;
pub use resolver::ResolverWorkspaceJsrPackage;
pub use resolver::SpecifiedImportMap;
pub use resolver::WorkspaceResolvePkgJsonFolderError;
pub use resolver::WorkspaceResolvePkgJsonFolderErrorKind;
pub use resolver::WorkspaceResolver;
pub use resolver::WorkspaceResolverCreateError;

#[allow(clippy::disallowed_types)]
type UrlRc = crate::sync::MaybeArc<Url>;
#[allow(clippy::disallowed_types)]
type WorkspaceRc = crate::sync::MaybeArc<Workspace>;

#[derive(Debug, Clone)]
pub struct JsrPackageConfig {
  /// The package name.
  pub name: String,
  pub member_dir: WorkspaceDirectory,
  pub config_file: ConfigFileRc,
  pub license: Option<String>,
}

#[derive(Debug, Clone)]
pub struct NpmPackageConfig {
  pub nv: PackageNv,
  pub workspace_dir: WorkspaceDirectory,
  pub pkg_json: PackageJsonRc,
}

impl NpmPackageConfig {
  pub fn matches_req(&self, req: &PackageReq) -> bool {
    self.matches_name_and_version_req(&req.name, &req.version_req)
  }

  pub fn matches_name_and_version_req(
    &self,
    name: &str,
    version_req: &VersionReq,
  ) -> bool {
    if name != self.nv.name {
      return false;
    }
    match version_req.inner() {
      RangeSetOrTag::RangeSet(set) => set.satisfies(&self.nv.version),
      RangeSetOrTag::Tag(tag) => tag == "workspace",
    }
  }
}

#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct WorkspaceLintConfig {
  pub report: Option<String>,
}

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum WorkspaceDiagnosticKind {
  #[error(
    "\"{0}\" field can only be specified in the workspace root deno.json file."
  )]
  RootOnlyOption(&'static str),
  #[error("\"{0}\" field can only be specified in a workspace member deno.json file and not the workspace root file.")]
  MemberOnlyOption(&'static str),
  #[error("\"workspaces\" field was ignored. Use \"workspace\" instead.")]
  InvalidWorkspacesOption,
  #[error("\"exports\" field should be specified when specifying a \"name\".")]
  MissingExports,
  #[error("\"importMap\" field is ignored when \"imports\" or \"scopes\" are specified in the config file.")]
  ImportMapReferencingImportMap,
  /// npm dependencies can't be patched when using a node_modules directory
  /// at the moment because I can't think of a way to get it to work well
  /// due to node resolution. For example, resolving a package to a separate
  /// folder means that dependencies will resolve using the node_modules directory
  /// in that folder, which sounds very error prone because the node_modules
  /// might have duplicate copies of packages in the root node_modules directory.
  /// When using the global resolver it's somewhat fine though because all
  /// dependencies resolve to the same global cache directory and are thus deduplicated.
  #[error("Patching npm dependencies is not supported when using a node_modules directory (Use `--node-modules-dir=false`)")]
  NpmPatchIgnored,
}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[error("{}\n    at {}", .kind, .config_url)]
pub struct WorkspaceDiagnostic {
  pub kind: WorkspaceDiagnosticKind,
  pub config_url: Url,
}

#[derive(Debug, Error)]
pub enum ResolveWorkspacePatchError {
  #[error(transparent)]
  ConfigRead(#[from] ConfigReadError),
  #[error("Could not find patch member in '{}'.", .dir_url)]
  NotFound { dir_url: Url },
  #[error("Workspace member cannot be specified as a patch.")]
  WorkspaceMemberNotAllowed,
  #[error(transparent)]
  InvalidPatch(#[from] url::ParseError),
  #[error(transparent)]
  Workspace(Box<WorkspaceDiscoverError>),
}

#[derive(Debug, Error)]
pub enum ConfigReadError {
  #[error(transparent)]
  DenoJsonRead(#[from] ConfigFileReadError),
  #[error(transparent)]
  PackageJsonRead(#[from] PackageJsonLoadError),
}

#[derive(Debug, Error)]
pub enum ResolveWorkspaceMemberError {
  #[error(transparent)]
  ConfigRead(#[from] ConfigReadError),
  #[error("Could not find config file for workspace member in '{}'.", .dir_url)]
  NotFound { dir_url: Url },
  #[error("Could not find package.json for workspace member in '{}'.", .dir_url)]
  NotFoundPackageJson { dir_url: Url },
  #[error("Could not find config file for workspace member in '{}'. Ensure you specify the directory and not the configuration file in the workspace member.", .dir_url)]
  NotFoundMaybeSpecifiedFile { dir_url: Url },
  #[error("Workspace member must be nested in a directory under the workspace.\n  Member: {member_url}\n  Workspace: {workspace_url}")]
  NonDescendant { workspace_url: Url, member_url: Url },
  #[error("Cannot specify a workspace member twice ('{}').", .member)]
  Duplicate { member: String },
  #[error("The '{name}' package ('{deno_json_url}') cannot have the same name as the package at '{other_deno_json_url}'.")]
  DuplicatePackageName {
    name: String,
    deno_json_url: Url,
    other_deno_json_url: Url,
  },
  #[error("Remove the reference to the current config file (\"{}\") in \"workspaces\".", .member)]
  InvalidSelfReference { member: String },
  #[error("Invalid workspace member '{}' for config '{}'.", member, base)]
  InvalidMember {
    base: Url,
    member: String,
    #[source]
    source: url::ParseError,
  },
  #[error(
    "Failed converting npm workspace member '{}' to pattern for config '{}'.",
    member,
    base
  )]
  NpmMemberToPattern {
    base: Url,
    member: String,
    // this error has the text that failed
    #[source]
    source: PathOrPatternParseError,
  },
}

#[derive(Error, Debug)]
#[error(transparent)]
pub struct WorkspaceDiscoverError(Box<WorkspaceDiscoverErrorKind>);

impl WorkspaceDiscoverError {
  pub fn as_kind(&self) -> &WorkspaceDiscoverErrorKind {
    &self.0
  }

  pub fn into_kind(self) -> WorkspaceDiscoverErrorKind {
    *self.0
  }
}

impl<E> From<E> for WorkspaceDiscoverError
where
  WorkspaceDiscoverErrorKind: From<E>,
{
  fn from(err: E) -> Self {
    WorkspaceDiscoverError(Box::new(WorkspaceDiscoverErrorKind::from(err)))
  }
}

#[derive(Debug, Error)]
pub enum WorkspaceDiscoverErrorKind {
  #[error("Failed resolving start directory.")]
  FailedResolvingStartDirectory(#[source] anyhow::Error),
  #[error(transparent)]
  ConfigRead(#[from] ConfigReadError),
  #[error(transparent)]
  PackageJsonReadError(#[from] PackageJsonLoadError),
  #[error(transparent)]
  PatchConfigParseError(#[from] PatchConfigParseError),
  #[error(transparent)]
  WorkspaceConfigParse(#[from] WorkspaceConfigParseError),
  #[error(transparent)]
  ResolveMember(#[from] ResolveWorkspaceMemberError),
  #[error("Failed loading patch '{}' in config '{}'.", patch, base)]
  ResolvePatch {
    patch: String,
    base: Url,
    #[source]
    source: ResolveWorkspacePatchError,
  },
  #[error("Command resolved to multiple config files. Ensure all specified paths are within the same workspace.\n  First: {base_workspace_url}\n  Second: {other_workspace_url}")]
  MultipleWorkspaces {
    base_workspace_url: Url,
    other_workspace_url: Url,
  },
  #[error(transparent)]
  SpecifierToFilePath(#[from] SpecifierToFilePathError),
  #[error("Config file must be a member of the workspace.\n  Config: {config_url}\n  Workspace: {workspace_url}")]
  ConfigNotWorkspaceMember {
    workspace_url: UrlRc,
    config_url: Url,
  },
  #[error(
    "Failed collecting npm workspace members.\n  Config: {package_json_url}"
  )]
  FailedCollectingNpmMembers {
    package_json_url: Url,
    #[source]
    source: AnyError,
  },
}

#[derive(Debug, Clone, Copy)]
pub enum WorkspaceDiscoverStart<'a> {
  Paths(&'a [PathBuf]),
  ConfigFile(&'a Path),
}

#[derive(Debug, Clone, Copy)]
pub enum VendorEnablement<'a> {
  Disable,
  Enable {
    /// The cwd, which will be used when no configuration file is
    /// resolved in order to discover the vendor folder.
    cwd: &'a Path,
  },
}

pub trait WorkspaceCache {
  fn get(&self, dir_path: &Path) -> Option<WorkspaceRc>;
  fn set(&self, dir_path: PathBuf, workspace: WorkspaceRc);
}

#[derive(Default, Clone)]
pub struct WorkspaceDiscoverOptions<'a> {
  pub fs: &'a dyn crate::fs::DenoConfigFs,
  /// A cache for deno.json files. This is mostly only useful in the LSP where
  /// workspace discovery may occur multiple times.
  pub deno_json_cache: Option<&'a dyn crate::deno_json::DenoJsonCache>,
  pub pkg_json_cache: Option<&'a dyn deno_package_json::PackageJsonCache>,
  /// A cache for workspaces. This is mostly only useful in the LSP where
  /// workspace discovery may occur multiple times.
  pub workspace_cache: Option<&'a dyn WorkspaceCache>,
  pub config_parse_options: ConfigParseOptions,
  pub additional_config_file_names: &'a [&'a str],
  pub discover_pkg_json: bool,
  pub maybe_vendor_override: Option<VendorEnablement<'a>>,
  /// Whether a node_modules directory should be forced to be used.
  ///
  /// This is currently only used to inform whether "patch" functionality
  /// should support patching npm dependencies as only the global resolver
  /// is supported.
  pub node_modules_dir_flag: Option<bool>,
}

#[derive(Clone)]
pub struct WorkspaceDirectoryEmptyOptions<'a> {
  pub root_dir: UrlRc,
  pub use_vendor_dir: VendorEnablement<'a>,
}

/// Configuration files found in a specific folder.
#[derive(Debug, Default, Clone)]
pub struct FolderConfigs {
  pub deno_json: Option<ConfigFileRc>,
  pub pkg_json: Option<PackageJsonRc>,
}

impl FolderConfigs {
  fn from_config_folder(config_folder: ConfigFolder) -> Self {
    match config_folder {
      ConfigFolder::Single(deno_or_pkg_json) => match deno_or_pkg_json {
        DenoOrPkgJson::Deno(deno_json) => FolderConfigs {
          deno_json: Some(deno_json),
          pkg_json: None,
        },
        DenoOrPkgJson::PkgJson(pkg_json) => FolderConfigs {
          deno_json: None,
          pkg_json: Some(pkg_json),
        },
      },
      ConfigFolder::Both {
        deno_json,
        pkg_json,
      } => FolderConfigs {
        deno_json: Some(deno_json),
        pkg_json: Some(pkg_json),
      },
    }
  }
}

#[derive(Debug)]
pub struct Workspace {
  root_dir: UrlRc,
  config_folders: IndexMap<UrlRc, FolderConfigs>,
  patches: BTreeMap<UrlRc, FolderConfigs>,
  /// Whether npm patches were removed from the collection of patches.
  removed_npm_patches: bool,
  pub(crate) vendor_dir: Option<PathBuf>,
}

impl Workspace {
  pub(crate) fn new(
    root: ConfigFolder,
    members: BTreeMap<UrlRc, ConfigFolder>,
    patches: BTreeMap<UrlRc, ConfigFolder>,
    vendor_dir: Option<PathBuf>,
    node_modules_dir_flag: Option<bool>,
  ) -> Self {
    let root_dir = new_rc(root.folder_url());
    let mut config_folders = IndexMap::with_capacity(members.len() + 1);
    config_folders
      .insert(root_dir.clone(), FolderConfigs::from_config_folder(root));
    config_folders.extend(members.into_iter().map(
      |(folder_url, config_folder)| {
        (folder_url, FolderConfigs::from_config_folder(config_folder))
      },
    ));
    let mut workspace = Workspace {
      root_dir,
      config_folders,
      patches: patches
        .into_iter()
        .map(|(url, folder)| (url, FolderConfigs::from_config_folder(folder)))
        .collect(),
      removed_npm_patches: false,
      vendor_dir,
    };
    if workspace.patches.values().any(|f| f.pkg_json.is_some()) {
      let uses_node_modules_dir = node_modules_dir_flag
        .or_else(|| {
          workspace
            .root_deno_json()
            .and_then(|c| c.json.node_modules_dir)
        })
        .unwrap_or_else(|| {
          workspace.vendor_dir.is_some()
            || workspace.package_jsons().next().is_some()
        });
      if uses_node_modules_dir {
        workspace.patches.retain(|_, f| f.pkg_json.is_none());
        workspace.removed_npm_patches = true;
      }
    }
    workspace
  }

  pub fn root_dir(&self) -> &UrlRc {
    &self.root_dir
  }

  pub fn root_dir_path(&self) -> PathBuf {
    self.root_dir.to_file_path().unwrap()
  }

  pub fn root_folder_configs(&self) -> &FolderConfigs {
    self.config_folders.get(&self.root_dir).unwrap()
  }

  pub fn root_deno_json(&self) -> Option<&ConfigFileRc> {
    self.root_folder_configs().deno_json.as_ref()
  }

  pub fn root_pkg_json(&self) -> Option<&PackageJsonRc> {
    self.root_folder_configs().pkg_json.as_ref()
  }

  pub fn config_folders(&self) -> &IndexMap<UrlRc, FolderConfigs> {
    &self.config_folders
  }

  pub fn deno_jsons(&self) -> impl Iterator<Item = &ConfigFileRc> {
    self
      .config_folders
      .values()
      .filter_map(|f| f.deno_json.as_ref())
  }

  pub fn package_jsons(&self) -> impl Iterator<Item = &PackageJsonRc> {
    self
      .config_folders
      .values()
      .filter_map(|f| f.pkg_json.as_ref())
  }

  pub fn jsr_packages<'a>(
    self: &'a WorkspaceRc,
  ) -> impl Iterator<Item = JsrPackageConfig> + 'a {
    self.deno_jsons().filter_map(|c| {
      if !c.is_package() {
        return None;
      }
      Some(JsrPackageConfig {
        member_dir: self.resolve_member_dir(&c.specifier),
        name: c.json.name.clone()?,
        config_file: c.clone(),
        license: c.to_license(),
      })
    })
  }

  pub fn npm_packages(self: &WorkspaceRc) -> Vec<NpmPackageConfig> {
    self
      .package_jsons()
      .filter_map(|c| self.package_json_to_npm_package_config(c))
      .collect()
  }

  fn package_json_to_npm_package_config(
    self: &WorkspaceRc,
    pkg_json: &PackageJsonRc,
  ) -> Option<NpmPackageConfig> {
    Some(NpmPackageConfig {
      workspace_dir: self.resolve_member_dir(&pkg_json.specifier()),
      nv: PackageNv {
        name: pkg_json.name.clone()?,
        version: {
          let version = pkg_json.version.as_ref()?;
          deno_semver::Version::parse_from_npm(version).ok()?
        },
      },
      pkg_json: pkg_json.clone(),
    })
  }

  pub fn patch_folders(&self) -> impl Iterator<Item = &FolderConfigs> {
    self.patches.values()
  }

  pub fn patch_deno_jsons(&self) -> impl Iterator<Item = &ConfigFileRc> {
    self.patches.values().filter_map(|f| f.deno_json.as_ref())
  }

  pub fn patch_npm_packages(self: &WorkspaceRc) -> Vec<NpmPackageConfig> {
    self
      .patch_pkg_jsons()
      .filter_map(|c| self.package_json_to_npm_package_config(c))
      .collect()
  }

  pub fn patch_pkg_jsons(&self) -> impl Iterator<Item = &PackageJsonRc> {
    self.patches.values().filter_map(|f| f.pkg_json.as_ref())
  }

  pub fn resolver_deno_jsons(&self) -> impl Iterator<Item = &ConfigFileRc> {
    self
      .deno_jsons()
      .chain(self.patches.values().filter_map(|f| f.deno_json.as_ref()))
  }

  pub fn resolver_pkg_jsons(
    &self,
  ) -> impl Iterator<Item = (&UrlRc, &PackageJsonRc)> {
    self
      .config_folders
      .iter()
      .filter_map(|(k, v)| Some((k, v.pkg_json.as_ref()?)))
      .chain(
        self
          .patches
          .iter()
          .filter_map(|(k, v)| Some((k, v.pkg_json.as_ref()?))),
      )
  }

  pub fn resolver_jsr_pkgs(
    &self,
  ) -> impl Iterator<Item = ResolverWorkspaceJsrPackage> + '_ {
    self
      .config_folders
      .iter()
      .filter_map(|(dir_url, f)| Some((dir_url, f.deno_json.as_ref()?, false)))
      .chain(self.patches.iter().filter_map(|(dir_url, f)| {
        Some((dir_url, f.deno_json.as_ref()?, true))
      }))
      .filter_map(|(dir_url, config_file, is_patch)| {
        let name = config_file.json.name.as_ref()?;
        let version = config_file
          .json
          .version
          .as_ref()
          .and_then(|v| Version::parse_standard(v).ok());
        let exports_config = config_file.to_exports_config().ok()?;
        Some(ResolverWorkspaceJsrPackage {
          is_patch,
          base: dir_url.as_ref().clone(),
          name: name.to_string(),
          version,
          exports: exports_config.into_map(),
        })
      })
  }

  pub async fn create_resolver<
    TReturn: Future<Output = Result<String, AnyError>>,
  >(
    &self,
    options: CreateResolverOptions,
    fetch_text: impl FnOnce(&Url) -> TReturn,
  ) -> Result<WorkspaceResolver, WorkspaceResolverCreateError> {
    WorkspaceResolver::from_workspace(self, options, fetch_text).await
  }

  /// Resolves a workspace directory, which can be used for deriving
  /// configuration specific to a member.
  pub fn resolve_member_dir(
    self: &WorkspaceRc,
    specifier: &Url,
  ) -> WorkspaceDirectory {
    WorkspaceDirectory::new(specifier, self.clone())
  }

  pub fn resolve_deno_json(
    &self,
    specifier: &Url,
  ) -> Option<(&UrlRc, &ConfigFileRc)> {
    self.resolve_deno_json_from_str(specifier.as_str())
  }

  fn resolve_deno_json_from_str(
    &self,
    specifier: &str,
  ) -> Option<(&UrlRc, &ConfigFileRc)> {
    let mut specifier = specifier;
    if !specifier.ends_with('/') {
      specifier = parent_specifier_str(specifier)?;
    }
    loop {
      let (folder_url, folder) = self.resolve_folder_str(specifier)?;
      if let Some(config) = folder.deno_json.as_ref() {
        return Some((folder_url, config));
      }
      specifier = parent_specifier_str(folder_url.as_str())?;
    }
  }

  fn resolve_pkg_json_from_str(
    &self,
    specifier: &str,
  ) -> Option<(&UrlRc, &PackageJsonRc)> {
    let mut specifier = specifier;
    if !specifier.ends_with('/') {
      specifier = parent_specifier_str(specifier)?;
    }
    loop {
      let (folder_url, folder) = self.resolve_folder_str(specifier)?;
      if let Some(pkg_json) = folder.pkg_json.as_ref() {
        return Some((folder_url, pkg_json));
      }
      specifier = parent_specifier_str(folder_url.as_str())?;
    }
  }

  pub fn resolve_folder(
    &self,
    specifier: &Url,
  ) -> Option<(&UrlRc, &FolderConfigs)> {
    self.resolve_folder_str(specifier.as_str())
  }

  fn resolve_folder_str(
    &self,
    specifier: &str,
  ) -> Option<(&UrlRc, &FolderConfigs)> {
    let mut best_match: Option<(&UrlRc, &FolderConfigs)> = None;
    for (dir_url, config) in &self.config_folders {
      if specifier.starts_with(dir_url.as_str())
        && (best_match.is_none()
          || dir_url.as_str().len() > best_match.unwrap().0.as_str().len())
      {
        best_match = Some((dir_url, config));
      }
    }
    best_match
  }

  pub fn diagnostics(&self) -> Vec<WorkspaceDiagnostic> {
    fn check_member_diagnostics(
      member_config: &ConfigFile,
      diagnostics: &mut Vec<WorkspaceDiagnostic>,
    ) {
      if member_config.json.compiler_options.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("compilerOptions"),
        });
      }
      if member_config.json.import_map.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("importMap"),
        });
      }
      if member_config.json.lock.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("lock"),
        });
      }
      if member_config.json.node_modules_dir.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("nodeModulesDir"),
        });
      }
      if member_config.json.patch.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("patch"),
        });
      }
      if member_config.json.scopes.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("scopes"),
        });
      }
      if !member_config.json.unstable.is_empty() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("unstable"),
        });
      }
      if member_config.json.vendor.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("vendor"),
        });
      }
      if member_config.json.workspace.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("workspace"),
        });
      }
      if let Some(value) = &member_config.json.lint {
        if value.get("report").is_some() {
          diagnostics.push(WorkspaceDiagnostic {
            config_url: member_config.specifier.clone(),
            kind: WorkspaceDiagnosticKind::RootOnlyOption("lint.report"),
          });
        }
      }
    }

    fn check_all_configs(
      config: &ConfigFile,
      diagnostics: &mut Vec<WorkspaceDiagnostic>,
    ) {
      if config.json.deprecated_workspaces.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::InvalidWorkspacesOption,
        });
      }
      if config.json.name.is_some() && config.json.exports.is_none() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::MissingExports,
        });
      }
      if config.is_an_import_map() && config.json.import_map.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::ImportMapReferencingImportMap,
        });
      }
    }

    let mut diagnostics = Vec::new();
    for (url, folder) in &self.config_folders {
      if let Some(config) = &folder.deno_json {
        let is_root = url == &self.root_dir;
        if !is_root {
          check_member_diagnostics(config, &mut diagnostics);
        }

        check_all_configs(config, &mut diagnostics);
      }
    }

    if self.removed_npm_patches {
      diagnostics.push(WorkspaceDiagnostic {
        config_url: self
          .root_deno_json()
          .map(|c| c.specifier.clone())
          .unwrap_or_else(|| (*self.root_dir).clone()),
        kind: WorkspaceDiagnosticKind::NpmPatchIgnored,
      });
    }

    for folder in self.patches.values() {
      if let Some(config) = &folder.deno_json {
        if config.json.patch.is_some() {
          // supporting patching in patches is too complicated
          diagnostics.push(WorkspaceDiagnostic {
            config_url: config.specifier.clone(),
            kind: WorkspaceDiagnosticKind::RootOnlyOption("patch"),
          });
        }
      }
    }

    diagnostics
  }

  pub fn check_js(&self) -> bool {
    self
      .with_root_config_only(|root_config| root_config.get_check_js())
      .unwrap_or(false)
  }

  pub fn node_modules_dir(&self) -> Option<bool> {
    self
      .with_root_config_only(|root_config| root_config.json.node_modules_dir)
      .unwrap_or(None)
  }

  pub fn vendor_dir_path(&self) -> Option<&PathBuf> {
    self.vendor_dir.as_ref()
  }

  pub fn to_compiler_options(
    &self,
  ) -> Result<
    Option<(serde_json::Value, Option<IgnoredCompilerOptions>)>,
    AnyError,
  > {
    self
      .with_root_config_only(|root_config| root_config.to_compiler_options())
      .map(|o| o.map(Some))
      .unwrap_or(Ok(None))
  }

  pub fn to_lint_config(&self) -> Result<WorkspaceLintConfig, AnyError> {
    self
      .with_root_config_only(|root_config| {
        Ok(WorkspaceLintConfig {
          report: match root_config
            .json
            .lint
            .as_ref()
            .and_then(|l| l.get("report"))
          {
            Some(report) => match report {
              serde_json::Value::String(value) => Some(value.to_string()),
              serde_json::Value::Null => None,
              serde_json::Value::Bool(_)
              | serde_json::Value::Number(_)
              | serde_json::Value::Array(_)
              | serde_json::Value::Object(_) => {
                bail!("lint.report must be a string")
              }
            },
            None => None,
          },
        })
      })
      .unwrap_or(Ok(Default::default()))
  }

  pub fn resolve_ts_config_for_emit(
    &self,
    config_type: TsConfigType,
  ) -> Result<TsConfigForEmit, AnyError> {
    get_ts_config_for_emit(
      config_type,
      self.root_deno_json().map(|c| c.as_ref()),
    )
  }

  pub fn to_import_map_specifier(&self) -> Result<Option<Url>, AnyError> {
    self
      .with_root_config_only(|root_config| {
        root_config.to_import_map_specifier()
      })
      .unwrap_or(Ok(None))
  }

  pub fn resolve_lockfile_path(&self) -> Result<Option<PathBuf>, AnyError> {
    if let Some(deno_json) = self.root_deno_json() {
      Ok(deno_json.resolve_lockfile_path()?)
    } else if let Some(pkg_json) = self.root_pkg_json() {
      Ok(pkg_json.path.parent().map(|p| p.join("deno.lock")))
    } else {
      Ok(None)
    }
  }

  pub fn to_compiler_option_types(
    self: &WorkspaceRc,
  ) -> Result<Vec<(Url, Vec<String>)>, AnyError> {
    self
      .with_root_config_only(|root_config| {
        root_config.to_compiler_option_types()
      })
      .unwrap_or(Ok(Vec::new()))
  }

  pub fn to_maybe_jsx_import_source_config(
    self: &WorkspaceRc,
  ) -> Result<Option<JsxImportSourceConfig>, AnyError> {
    self
      .with_root_config_only(|root_config| {
        root_config.to_maybe_jsx_import_source_config()
      })
      .unwrap_or(Ok(None))
  }

  pub fn resolve_bench_config_for_members(
    self: &WorkspaceRc,
    cli_args: &FilePatterns,
  ) -> Result<Vec<(WorkspaceDirectory, BenchConfig)>, AnyError> {
    self.resolve_config_for_members(cli_args, |dir, patterns| {
      dir.to_bench_config(patterns)
    })
  }

  pub fn resolve_lint_config_for_members(
    self: &WorkspaceRc,
    cli_args: &FilePatterns,
  ) -> Result<Vec<(WorkspaceDirectory, LintConfig)>, AnyError> {
    self.resolve_config_for_members(cli_args, |dir, patterns| {
      dir.to_lint_config(patterns)
    })
  }

  pub fn resolve_fmt_config_for_members(
    self: &WorkspaceRc,
    cli_args: &FilePatterns,
  ) -> Result<Vec<(WorkspaceDirectory, FmtConfig)>, AnyError> {
    self.resolve_config_for_members(cli_args, |dir, patterns| {
      dir.to_fmt_config(patterns)
    })
  }

  pub fn resolve_test_config_for_members(
    self: &WorkspaceRc,
    cli_args: &FilePatterns,
  ) -> Result<Vec<(WorkspaceDirectory, TestConfig)>, AnyError> {
    self.resolve_config_for_members(cli_args, |dir, patterns| {
      dir.to_test_config(patterns)
    })
  }

  fn resolve_config_for_members<TConfig>(
    self: &WorkspaceRc,
    cli_args: &FilePatterns,
    resolve_config: impl Fn(
      &WorkspaceDirectory,
      FilePatterns,
    ) -> Result<TConfig, AnyError>,
  ) -> Result<Vec<(WorkspaceDirectory, TConfig)>, AnyError> {
    let cli_args_by_folder = self.split_cli_args_by_deno_json_folder(cli_args);
    let mut result = Vec::with_capacity(cli_args_by_folder.len());
    for (folder_url, patterns) in cli_args_by_folder {
      let dir = self.resolve_member_dir(&folder_url);
      let config = resolve_config(&dir, patterns)?;
      result.push((dir, config));
    }
    Ok(result)
  }

  fn split_cli_args_by_deno_json_folder(
    &self,
    cli_args: &FilePatterns,
  ) -> IndexMap<UrlRc, FilePatterns> {
    fn common_ancestor(a: &Path, b: &Path) -> PathBuf {
      a.components()
        .zip(b.components())
        .take_while(|(a, b)| a == b)
        .map(|(a, _)| a)
        .collect()
    }

    let cli_arg_patterns = cli_args.split_by_base();
    let deno_json_folders = self
      .config_folders
      .iter()
      .filter(|(_, folder)| folder.deno_json.is_some())
      .map(|(url, folder)| {
        let dir_path = url.to_file_path().unwrap();
        (dir_path, (url, folder))
      })
      .collect::<Vec<_>>();
    let mut results: IndexMap<_, FilePatterns> =
      IndexMap::with_capacity(deno_json_folders.len() + 1);
    for pattern in cli_arg_patterns {
      let mut matches = Vec::with_capacity(deno_json_folders.len());
      for (dir_path, v) in deno_json_folders.iter() {
        if pattern.base.starts_with(dir_path)
          || dir_path.starts_with(&pattern.base)
        {
          matches.push((dir_path, *v));
        }
      }
      // remove any non-sub/current folders that start with another folder
      let mut indexes_to_remove = VecDeque::with_capacity(matches.len());
      for (i, (m, _)) in matches.iter().enumerate() {
        if !m.starts_with(&pattern.base)
          && matches.iter().any(|(sub, _)| {
            sub.starts_with(m) && sub != m && pattern.base.starts_with(m)
          })
        {
          indexes_to_remove.push_back(i);
        }
      }
      let mut matched_folder_urls =
        Vec::with_capacity(std::cmp::max(1, matches.len()));
      if matches.is_empty() {
        // This will occur when someone specifies a file that's outside
        // the workspace directory. In this case, use the root directory's config
        // so that it's consistent across the workspace.
        matched_folder_urls.push(&self.root_dir);
      }
      for (i, (_dir_path, (folder_url, _config))) in matches.iter().enumerate()
      {
        if let Some(skip_index) = indexes_to_remove.front() {
          if i == *skip_index {
            indexes_to_remove.pop_front();
            continue;
          }
        }
        matched_folder_urls.push(folder_url);
      }
      for folder_url in matched_folder_urls {
        let entry = results.entry((*folder_url).clone());
        let folder_path = folder_url.to_file_path().unwrap();
        match entry {
          indexmap::map::Entry::Occupied(entry) => {
            let entry = entry.into_mut();
            let common_base = common_ancestor(&pattern.base, &entry.base);
            if common_base.starts_with(&folder_path)
              && entry.base.starts_with(&common_base)
            {
              entry.base = common_base;
            }
            match &mut entry.include {
              Some(set) => {
                if let Some(includes) = &pattern.include {
                  for include in includes.inner() {
                    if !set.inner().contains(include) {
                      set.push(include.clone())
                    }
                  }
                }
              }
              None => {
                entry.include.clone_from(&pattern.include);
              }
            }
          }
          indexmap::map::Entry::Vacant(entry) => {
            entry.insert(FilePatterns {
              base: if pattern.base.starts_with(&folder_path) {
                pattern.base.clone()
              } else {
                folder_path.clone()
              },
              include: pattern.include.clone(),
              exclude: pattern.exclude.clone(),
            });
          }
        }
      }
    }
    results
  }

  pub fn resolve_config_excludes(&self) -> Result<PathOrPatternSet, AnyError> {
    // have the root excludes at the front because they're lower priority
    let mut excludes = match &self.root_deno_json() {
      Some(c) => c.to_exclude_files_config()?.exclude.into_path_or_patterns(),
      None => Default::default(),
    };
    for (dir_url, folder) in self.config_folders.iter() {
      let Some(deno_json) = folder.deno_json.as_ref() else {
        continue;
      };
      if dir_url == &self.root_dir {
        continue;
      }
      excludes.extend(
        deno_json
          .to_exclude_files_config()?
          .exclude
          .into_path_or_patterns(),
      );
    }
    Ok(PathOrPatternSet::new(excludes))
  }

  pub fn unstable_features(&self) -> &[String] {
    self
      .with_root_config_only(|deno_json| {
        (&deno_json.json.unstable) as &[String]
      })
      .unwrap_or(&[])
  }

  pub fn has_unstable(&self, name: &str) -> bool {
    self
      .with_root_config_only(|deno_json| deno_json.has_unstable(name))
      .unwrap_or(false)
  }

  fn with_root_config_only<'a, R>(
    &'a self,
    with_root: impl Fn(&'a ConfigFile) -> R,
  ) -> Option<R> {
    self.root_deno_json().map(|c| with_root(c))
  }
}

#[derive(Debug, Clone)]
struct WorkspaceDirConfig<T> {
  #[allow(clippy::disallowed_types)]
  member: crate::sync::MaybeArc<T>,
  // will be None when it doesn't exist or the member config
  // is the root config
  #[allow(clippy::disallowed_types)]
  root: Option<crate::sync::MaybeArc<T>>,
}

#[derive(Debug, Clone)]
pub struct WorkspaceDirectory {
  pub workspace: WorkspaceRc,
  /// The directory that this context is for. This is generally the cwd.
  dir_url: UrlRc,
  pkg_json: Option<WorkspaceDirConfig<PackageJson>>,
  deno_json: Option<WorkspaceDirConfig<ConfigFile>>,
}

impl WorkspaceDirectory {
  pub fn empty(opts: WorkspaceDirectoryEmptyOptions) -> Self {
    WorkspaceDirectory::new(
      &opts.root_dir,
      new_rc(Workspace {
        config_folders: IndexMap::from([(
          opts.root_dir.clone(),
          FolderConfigs::default(),
        )]),
        root_dir: opts.root_dir.clone(),
        patches: BTreeMap::new(),
        removed_npm_patches: false,
        vendor_dir: match opts.use_vendor_dir {
          VendorEnablement::Enable { cwd } => Some(cwd.join("vendor")),
          VendorEnablement::Disable => None,
        },
      }),
    )
  }

  pub fn discover(
    start: WorkspaceDiscoverStart,
    opts: &WorkspaceDiscoverOptions,
  ) -> Result<Self, WorkspaceDiscoverError> {
    fn resolve_start_dir(
      start: &WorkspaceDiscoverStart,
      fs: &dyn crate::fs::DenoConfigFs,
    ) -> Result<Url, WorkspaceDiscoverError> {
      match start {
        WorkspaceDiscoverStart::Paths(paths) => {
          if paths.is_empty() {
            Err(
              WorkspaceDiscoverErrorKind::FailedResolvingStartDirectory(
                anyhow::anyhow!("No paths provided."),
              )
              .into(),
            )
          } else {
            // just select the first one... this doesn't matter too much
            // at the moment because we only use this for lint and fmt,
            // so this is ok for now
            let path = &paths[0];
            match fs.stat_sync(path) {
              Ok(info) => {
                return Ok(
                  Url::from_directory_path(if info.is_directory {
                    path
                  } else {
                    path.parent().unwrap()
                  })
                  .unwrap(),
                )
              }
              Err(_err) => {
                // assume the parent is a directory
                match path.parent() {
                  Some(parent) => Ok(Url::from_directory_path(parent).unwrap()),
                  None => Err(
                    WorkspaceDiscoverErrorKind::FailedResolvingStartDirectory(
                      anyhow::anyhow!(
                        "Could not resolve path: '{}'",
                        path.display()
                      ),
                    )
                    .into(),
                  ),
                }
              }
            }
          }
        }
        WorkspaceDiscoverStart::ConfigFile(path) => {
          let parent = path.parent().ok_or_else(|| {
            WorkspaceDiscoverErrorKind::FailedResolvingStartDirectory(
              anyhow::anyhow!(
                "Provided config file path ('{}') had no parent directory.",
                path.display()
              ),
            )
          })?;
          Ok(Url::from_directory_path(parent).unwrap())
        }
      }
    }

    let start_dir = resolve_start_dir(&start, opts.fs)?;
    let config_file_discovery = discover_workspace_config_files(start, opts)?;

    let context = match config_file_discovery {
      ConfigFileDiscovery::None {
        maybe_vendor_dir: vendor_dir,
      } => {
        let start_dir = new_rc(start_dir);
        let workspace = new_rc(Workspace {
          config_folders: IndexMap::from([(
            start_dir.clone(),
            FolderConfigs::default(),
          )]),
          root_dir: start_dir.clone(),
          patches: BTreeMap::new(),
          removed_npm_patches: false,
          vendor_dir,
        });
        WorkspaceDirectory::new(&start_dir, workspace)
      }
      ConfigFileDiscovery::Workspace { workspace } => {
        WorkspaceDirectory::new(&start_dir, workspace)
      }
    };
    debug_assert!(
      context
        .workspace
        .config_folders
        .contains_key(&context.workspace.root_dir),
      "root should always have a folder"
    );
    Ok(context)
  }

  fn new(specifier: &Url, workspace: WorkspaceRc) -> Self {
    let maybe_folder = workspace.resolve_folder(specifier);
    match maybe_folder {
      Some((member_url, folder)) => {
        if member_url == &workspace.root_dir {
          Self::create_from_root_folder(workspace)
        } else {
          let maybe_deno_json = folder
            .deno_json
            .as_ref()
            .map(|c| (member_url, c))
            .or_else(|| {
              let parent = parent_specifier_str(member_url.as_str())?;
              workspace.resolve_deno_json_from_str(parent)
            })
            .or_else(|| {
              let root =
                workspace.config_folders.get(&workspace.root_dir).unwrap();
              root.deno_json.as_ref().map(|c| (&workspace.root_dir, c))
            });
          let maybe_pkg_json = folder
            .pkg_json
            .as_ref()
            .map(|pkg_json| (member_url, pkg_json))
            .or_else(|| {
              let parent = parent_specifier_str(member_url.as_str())?;
              workspace.resolve_pkg_json_from_str(parent)
            })
            .or_else(|| {
              let root =
                workspace.config_folders.get(&workspace.root_dir).unwrap();
              root.pkg_json.as_ref().map(|c| (&workspace.root_dir, c))
            });
          Self {
            dir_url: member_url.clone(),
            pkg_json: maybe_pkg_json.map(|(member_url, pkg_json)| {
              WorkspaceDirConfig {
                root: if workspace.root_dir == *member_url {
                  None
                } else {
                  workspace
                    .config_folders
                    .get(&workspace.root_dir)
                    .unwrap()
                    .pkg_json
                    .clone()
                },
                member: pkg_json.clone(),
              }
            }),
            deno_json: maybe_deno_json.map(|(member_url, config)| {
              WorkspaceDirConfig {
                root: if workspace.root_dir == *member_url {
                  None
                } else {
                  workspace
                    .config_folders
                    .get(&workspace.root_dir)
                    .unwrap()
                    .deno_json
                    .clone()
                },
                member: config.clone(),
              }
            }),
            workspace,
          }
        }
      }
      None => Self::create_from_root_folder(workspace),
    }
  }

  fn create_from_root_folder(workspace: WorkspaceRc) -> Self {
    let root_folder =
      workspace.config_folders.get(&workspace.root_dir).unwrap();
    let dir_url = workspace.root_dir.clone();
    WorkspaceDirectory {
      dir_url,
      pkg_json: root_folder.pkg_json.as_ref().map(|config| {
        WorkspaceDirConfig {
          member: config.clone(),
          root: None,
        }
      }),
      deno_json: root_folder.deno_json.as_ref().map(|config| {
        WorkspaceDirConfig {
          member: config.clone(),
          root: None,
        }
      }),
      workspace,
    }
  }

  pub fn jsr_packages_for_publish(&self) -> Vec<JsrPackageConfig> {
    // only publish the current folder if it's a package
    if let Some(package_config) = self.maybe_package_config() {
      return vec![package_config];
    }
    if let Some(pkg_json) = &self.pkg_json {
      let dir_path = self.dir_url.to_file_path().unwrap();
      // don't publish anything if in a package.json only directory within
      // a workspace
      if pkg_json.member.dir_path().starts_with(&dir_path)
        && dir_path != pkg_json.member.dir_path()
      {
        return Vec::new();
      }
    }
    if self.dir_url == self.workspace.root_dir {
      self.workspace.jsr_packages().collect()
    } else {
      // nothing to publish
      Vec::new()
    }
  }

  pub fn dir_url(&self) -> &UrlRc {
    &self.dir_url
  }

  pub fn dir_path(&self) -> PathBuf {
    self.dir_url.to_file_path().unwrap()
  }

  pub fn has_deno_or_pkg_json(&self) -> bool {
    self.has_pkg_json() || self.has_deno_json()
  }

  pub fn has_deno_json(&self) -> bool {
    self.deno_json.is_some()
  }

  pub fn has_pkg_json(&self) -> bool {
    self.pkg_json.is_some()
  }

  pub fn maybe_deno_json(&self) -> Option<&ConfigFileRc> {
    self.deno_json.as_ref().map(|c| &c.member)
  }

  pub fn maybe_pkg_json(&self) -> Option<&PackageJsonRc> {
    self.pkg_json.as_ref().map(|c| &c.member)
  }

  pub fn maybe_package_config(&self) -> Option<JsrPackageConfig> {
    let deno_json = self.maybe_deno_json()?;
    let pkg_name = deno_json.json.name.as_ref()?;
    if !deno_json.is_package() {
      return None;
    }
    Some(JsrPackageConfig {
      name: pkg_name.clone(),
      config_file: deno_json.clone(),
      member_dir: self.clone(),
      license: deno_json.to_license(),
    })
  }

  pub fn to_lint_config(
    &self,
    cli_args: FilePatterns,
  ) -> Result<LintConfig, AnyError> {
    let mut config = self.to_lint_config_inner()?;
    self.exclude_includes_with_member_for_base_for_root(&mut config.files);
    combine_files_config_with_cli_args(&mut config.files, cli_args);
    self.append_workspace_members_to_exclude(&mut config.files);
    Ok(config)
  }

  fn to_lint_config_inner(&self) -> Result<LintConfig, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(LintConfig {
        options: Default::default(),
        files: FilePatterns::new_with_base(
          self.dir_url.to_file_path().unwrap(),
        ),
      });
    };
    let member_config = deno_json.member.to_lint_config()?;
    let root_config = match &deno_json.root {
      Some(root) => root.to_lint_config()?,
      None => return Ok(member_config),
    };
    // combine the configs
    Ok(LintConfig {
      options: LintOptionsConfig {
        rules: {
          let root_opts = root_config.options;
          let member_opts = member_config.options;
          LintRulesConfig {
            tags: combine_option_vecs(
              root_opts.rules.tags,
              member_opts.rules.tags,
            ),
            include: combine_option_vecs_with_override(
              CombineOptionVecsWithOverride {
                root: root_opts.rules.include,
                member: member_opts.rules.include.as_ref().map(Cow::Borrowed),
                member_override_root: member_opts.rules.exclude.as_ref(),
              },
            ),
            exclude: combine_option_vecs_with_override(
              CombineOptionVecsWithOverride {
                root: root_opts.rules.exclude,
                member: member_opts.rules.exclude.map(Cow::Owned),
                member_override_root: member_opts.rules.include.as_ref(),
              },
            ),
          }
        },
      },
      files: combine_patterns(root_config.files, member_config.files),
    })
  }

  pub fn to_fmt_config(
    &self,
    cli_args: FilePatterns,
  ) -> Result<FmtConfig, AnyError> {
    let mut config = self.to_fmt_config_inner()?;
    self.exclude_includes_with_member_for_base_for_root(&mut config.files);
    combine_files_config_with_cli_args(&mut config.files, cli_args);
    self.append_workspace_members_to_exclude(&mut config.files);
    Ok(config)
  }

  fn to_fmt_config_inner(&self) -> Result<FmtConfig, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(FmtConfig {
        files: FilePatterns::new_with_base(
          self.dir_url.to_file_path().unwrap(),
        ),
        options: Default::default(),
      });
    };
    let member_config = deno_json.member.to_fmt_config()?;
    let root_config = match &deno_json.root {
      Some(root) => root.to_fmt_config()?,
      None => return Ok(member_config),
    };

    Ok(FmtConfig {
      options: FmtOptionsConfig {
        use_tabs: member_config
          .options
          .use_tabs
          .or(root_config.options.use_tabs),
        line_width: member_config
          .options
          .line_width
          .or(root_config.options.line_width),
        indent_width: member_config
          .options
          .indent_width
          .or(root_config.options.indent_width),
        single_quote: member_config
          .options
          .single_quote
          .or(root_config.options.single_quote),
        prose_wrap: member_config
          .options
          .prose_wrap
          .or(root_config.options.prose_wrap),
        semi_colons: member_config
          .options
          .semi_colons
          .or(root_config.options.semi_colons),
      },
      files: combine_patterns(root_config.files, member_config.files),
    })
  }

  pub fn to_bench_config(
    &self,
    cli_args: FilePatterns,
  ) -> Result<BenchConfig, AnyError> {
    let mut config = self.to_bench_config_inner()?;
    self.exclude_includes_with_member_for_base_for_root(&mut config.files);
    combine_files_config_with_cli_args(&mut config.files, cli_args);
    self.append_workspace_members_to_exclude(&mut config.files);
    Ok(config)
  }

  fn to_bench_config_inner(&self) -> Result<BenchConfig, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(BenchConfig {
        files: FilePatterns::new_with_base(
          self.dir_url.to_file_path().unwrap(),
        ),
      });
    };
    let member_config = deno_json.member.to_bench_config()?;
    let root_config = match &deno_json.root {
      Some(root) => root.to_bench_config()?,
      None => return Ok(member_config),
    };
    Ok(BenchConfig {
      files: combine_patterns(root_config.files, member_config.files),
    })
  }

  pub fn to_tasks_config(&self) -> Result<WorkspaceTasksConfig, AnyError> {
    fn to_member_tasks_config(
      maybe_deno_json: Option<&ConfigFileRc>,
      maybe_pkg_json: Option<&PackageJsonRc>,
    ) -> Result<Option<WorkspaceMemberTasksConfig>, AnyError> {
      let config = WorkspaceMemberTasksConfig {
        deno_json: match maybe_deno_json {
          Some(deno_json) => deno_json
            .to_tasks_config()
            .map(|tasks| {
              tasks.map(|tasks| WorkspaceMemberTasksConfigFile {
                folder_url: Url::from_directory_path(deno_json.dir_path())
                  .unwrap(),
                tasks,
              })
            })
            .with_context(|| {
              format!("Failed parsing '{}'.", deno_json.specifier)
            })?,
          None => None,
        },
        package_json: match maybe_pkg_json {
          Some(pkg_json) => pkg_json.scripts.clone().map(|scripts| {
            WorkspaceMemberTasksConfigFile {
              folder_url: Url::from_directory_path(pkg_json.dir_path())
                .unwrap(),
              tasks: scripts,
            }
          }),
          None => None,
        },
      };
      if config.deno_json.is_none() && config.package_json.is_none() {
        return Ok(None);
      }
      Ok(Some(config))
    }

    Ok(WorkspaceTasksConfig {
      root: to_member_tasks_config(
        self.deno_json.as_ref().and_then(|d| d.root.as_ref()),
        self.pkg_json.as_ref().and_then(|d| d.root.as_ref()),
      )?,
      member: to_member_tasks_config(
        self.deno_json.as_ref().map(|d| &d.member),
        self.pkg_json.as_ref().map(|d| &d.member),
      )?,
    })
  }

  pub fn to_publish_config(&self) -> Result<PublishConfig, AnyError> {
    let mut config = self.to_publish_config_inner()?;
    self.exclude_includes_with_member_for_base_for_root(&mut config.files);
    self.append_workspace_members_to_exclude(&mut config.files);
    Ok(config)
  }

  fn to_publish_config_inner(&self) -> Result<PublishConfig, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(PublishConfig {
        files: FilePatterns::new_with_base(
          self.dir_url.to_file_path().unwrap(),
        ),
      });
    };
    let member_config = deno_json.member.to_publish_config()?;
    let root_config = match &deno_json.root {
      Some(root) => root.to_publish_config()?,
      None => return Ok(member_config),
    };
    Ok(PublishConfig {
      files: combine_patterns(root_config.files, member_config.files),
    })
  }

  pub fn to_test_config(
    &self,
    cli_args: FilePatterns,
  ) -> Result<TestConfig, AnyError> {
    let mut config = self.to_test_config_inner()?;
    self.exclude_includes_with_member_for_base_for_root(&mut config.files);
    combine_files_config_with_cli_args(&mut config.files, cli_args);
    self.append_workspace_members_to_exclude(&mut config.files);
    Ok(config)
  }

  fn to_test_config_inner(&self) -> Result<TestConfig, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(TestConfig {
        files: FilePatterns::new_with_base(
          self.dir_url.to_file_path().unwrap(),
        ),
      });
    };
    let member_config = deno_json.member.to_test_config()?;
    let root_config = match &deno_json.root {
      Some(root) => root.to_test_config()?,
      None => return Ok(member_config),
    };

    Ok(TestConfig {
      files: combine_patterns(root_config.files, member_config.files),
    })
  }

  /// Removes any "include" patterns from the root files that have
  /// a base in another workspace member.
  fn exclude_includes_with_member_for_base_for_root(
    &self,
    files: &mut FilePatterns,
  ) {
    let Some(include) = &mut files.include else {
      return;
    };
    let root_url = self.workspace.root_dir();
    if self.dir_url != *root_url {
      return; // only do this for the root config
    }

    let root_folder_configs = self.workspace.root_folder_configs();
    let maybe_root_deno_json = root_folder_configs.deno_json.as_ref();
    let non_root_deno_jsons = match maybe_root_deno_json {
      Some(root_deno_json) => self
        .workspace
        .deno_jsons()
        .filter(|d| d.specifier != root_deno_json.specifier)
        .collect::<Vec<_>>(),
      None => self.workspace.deno_jsons().collect::<Vec<_>>(),
    };

    let include = include.inner_mut();
    for i in (0..include.len()).rev() {
      let Some(path) = include[i].base_path() else {
        continue;
      };
      for deno_json in non_root_deno_jsons.iter() {
        if path.starts_with(deno_json.dir_path()) {
          include.remove(i);
          break;
        }
      }
    }
  }

  fn append_workspace_members_to_exclude(&self, files: &mut FilePatterns) {
    files.exclude.append(
      self
        .workspace
        .deno_jsons()
        .filter(|member_deno_json| {
          let member_dir = member_deno_json.dir_path();
          member_dir != files.base && member_dir.starts_with(&files.base)
        })
        .map(|d| PathOrPattern::Path(d.dir_path())),
    );
  }
}

pub enum TaskOrScript<'a> {
  /// A task from a deno.json.
  Task(&'a IndexMap<String, Task>, &'a str),
  /// A script from a package.json.
  Script(&'a IndexMap<String, String>, &'a str),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WorkspaceMemberTasksConfigFile<TValue> {
  pub folder_url: Url,
  pub tasks: IndexMap<String, TValue>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WorkspaceMemberTasksConfig {
  pub deno_json: Option<WorkspaceMemberTasksConfigFile<Task>>,
  pub package_json: Option<WorkspaceMemberTasksConfigFile<String>>,
}

impl WorkspaceMemberTasksConfig {
  pub fn with_only_pkg_json(self) -> Self {
    WorkspaceMemberTasksConfig {
      deno_json: None,
      package_json: self.package_json,
    }
  }

  pub fn is_empty(&self) -> bool {
    self
      .deno_json
      .as_ref()
      .map(|d| d.tasks.is_empty())
      .unwrap_or(true)
      && self
        .package_json
        .as_ref()
        .map(|d| d.tasks.is_empty())
        .unwrap_or(true)
  }

  pub fn tasks_count(&self) -> usize {
    self.deno_json.as_ref().map(|d| d.tasks.len()).unwrap_or(0)
      + self
        .package_json
        .as_ref()
        .map(|d| d.tasks.len())
        .unwrap_or(0)
  }

  pub fn task(&self, name: &str) -> Option<(&Url, TaskOrScript)> {
    self
      .deno_json
      .as_ref()
      .and_then(|config| {
        config.tasks.get(name).map(|t| {
          (
            &config.folder_url,
            TaskOrScript::Task(&config.tasks, t.definition()),
          )
        })
      })
      .or_else(|| {
        self.package_json.as_ref().and_then(|config| {
          config.tasks.get(name).map(|task| {
            (
              &config.folder_url,
              TaskOrScript::Script(&config.tasks, task),
            )
          })
        })
      })
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WorkspaceTasksConfig {
  pub root: Option<WorkspaceMemberTasksConfig>,
  pub member: Option<WorkspaceMemberTasksConfig>,
}

impl WorkspaceTasksConfig {
  pub fn with_only_pkg_json(self) -> Self {
    WorkspaceTasksConfig {
      root: self.root.map(|c| c.with_only_pkg_json()),
      member: self.member.map(|c| c.with_only_pkg_json()),
    }
  }

  pub fn task(&self, name: &str) -> Option<(&Url, TaskOrScript)> {
    self
      .member
      .as_ref()
      .and_then(|m| m.task(name))
      .or_else(|| self.root.as_ref().and_then(|r| r.task(name)))
  }

  pub fn is_empty(&self) -> bool {
    self.root.as_ref().map(|r| r.is_empty()).unwrap_or(true)
      && self.member.as_ref().map(|r| r.is_empty()).unwrap_or(true)
  }

  pub fn tasks_count(&self) -> usize {
    self.root.as_ref().map(|r| r.tasks_count()).unwrap_or(0)
      + self.member.as_ref().map(|r| r.tasks_count()).unwrap_or(0)
  }
}

fn combine_patterns(
  root_patterns: FilePatterns,
  member_patterns: FilePatterns,
) -> FilePatterns {
  FilePatterns {
    include: {
      match root_patterns.include {
        Some(root) => {
          let filtered_root =
            root.into_path_or_patterns().into_iter().filter(|p| {
              match p.base_path() {
                Some(base) => base.starts_with(&member_patterns.base),
                None => true,
              }
            });
          match member_patterns.include {
            Some(member) => Some(
              filtered_root
                .chain(member.into_path_or_patterns())
                .collect(),
            ),
            None => {
              let matching_root = filtered_root.collect::<Vec<_>>();
              if matching_root.is_empty() {
                // member was None and nothing in the root include list
                // has a base within this member, so use None to discover
                // files in here
                None
              } else {
                Some(matching_root)
              }
            }
          }
          .map(PathOrPatternSet::new)
        }
        None => member_patterns.include,
      }
    },
    exclude: {
      // have the root excludes at the front because they're lower priority
      let patterns = root_patterns
        .exclude
        .into_path_or_patterns()
        .into_iter()
        .filter(|p| match p {
            PathOrPattern::Path(path) |
            PathOrPattern::NegatedPath(path) => path.starts_with(&member_patterns.base),
            PathOrPattern::RemoteUrl(_) |
            // always include patterns because they may be something like ./**/*.ts in the root
            PathOrPattern::Pattern(_) => true,
        })
        .chain(member_patterns.exclude.into_path_or_patterns())
        .collect::<Vec<_>>();
      PathOrPatternSet::new(patterns)
    },
    base: member_patterns.base,
  }
}

fn combine_files_config_with_cli_args(
  files_config: &mut FilePatterns,
  cli_arg_patterns: FilePatterns,
) {
  if cli_arg_patterns.base.starts_with(&files_config.base)
    || !files_config.base.starts_with(&cli_arg_patterns.base)
  {
    files_config.base = cli_arg_patterns.base;
  }
  if let Some(include) = cli_arg_patterns.include {
    if !include.inner().is_empty() {
      files_config.include = Some(include);
    }
  }
  if !cli_arg_patterns.exclude.inner().is_empty() {
    files_config.exclude = cli_arg_patterns.exclude;
  }
}

struct CombineOptionVecsWithOverride<'a, T: Clone> {
  root: Option<Vec<T>>,
  member: Option<Cow<'a, Vec<T>>>,
  member_override_root: Option<&'a Vec<T>>,
}

fn combine_option_vecs_with_override<T: Eq + std::hash::Hash + Clone>(
  opts: CombineOptionVecsWithOverride<T>,
) -> Option<Vec<T>> {
  let root = opts.root.map(|r| {
    let member_override_root = opts
      .member_override_root
      .map(|p| p.iter().collect::<HashSet<_>>())
      .unwrap_or_default();
    r.into_iter()
      .filter(|p| !member_override_root.contains(p))
      .collect::<Vec<_>>()
  });
  match (root, opts.member) {
    (Some(root), Some(member)) => {
      let capacity = root.len() + member.len();
      Some(match member {
        Cow::Owned(m) => {
          remove_duplicates_iterator(root.into_iter().chain(m), capacity)
        }
        Cow::Borrowed(m) => remove_duplicates_iterator(
          root.into_iter().chain(m.iter().map(|c| (*c).clone())),
          capacity,
        ),
      })
    }
    (Some(root), None) => Some(root),
    (None, Some(member)) => Some(match member {
      Cow::Owned(m) => m,
      Cow::Borrowed(m) => m.iter().map(|c| (*c).clone()).collect(),
    }),
    (None, None) => None,
  }
}

fn combine_option_vecs<T: Eq + std::hash::Hash + Clone>(
  root_option: Option<Vec<T>>,
  member_option: Option<Vec<T>>,
) -> Option<Vec<T>> {
  match (root_option, member_option) {
    (Some(root), Some(member)) => {
      if root.is_empty() {
        return Some(member);
      }
      if member.is_empty() {
        return Some(root);
      }
      let capacity = root.len() + member.len();
      Some(remove_duplicates_iterator(
        root.into_iter().chain(member),
        capacity,
      ))
    }
    (Some(root), None) => Some(root),
    (None, Some(member)) => Some(member),
    (None, None) => None,
  }
}

fn remove_duplicates_iterator<T: Eq + std::hash::Hash + Clone>(
  iterator: impl IntoIterator<Item = T>,
  capacity: usize,
) -> Vec<T> {
  let mut seen = HashSet::with_capacity(capacity);
  let mut result = Vec::with_capacity(capacity);
  for item in iterator {
    if seen.insert(item.clone()) {
      result.push(item);
    }
  }
  result
}

fn parent_specifier_str(specifier: &str) -> Option<&str> {
  let specifier = specifier.strip_suffix('/').unwrap_or(specifier);
  if let Some(index) = specifier.rfind('/') {
    Some(&specifier[..index + 1])
  } else {
    None
  }
}

#[cfg(test)]
mod test {
  use std::cell::RefCell;
  use std::collections::HashMap;

  use pretty_assertions::assert_eq;
  use serde_json::json;

  use crate::assert_contains;
  use crate::deno_json::DenoJsonCache;
  use crate::deno_json::ProseWrap;
  use crate::deno_json::TsConfig;
  use crate::fs::TestFileSystem;
  use crate::glob::FileCollector;
  use crate::glob::GlobPattern;
  use crate::glob::PathKind;
  use crate::glob::PathOrPattern;
  use crate::util::normalize_path;

  use super::*;

  fn root_dir() -> PathBuf {
    if cfg!(windows) {
      PathBuf::from("C:\\Users\\user")
    } else {
      PathBuf::from("/home/user")
    }
  }

  #[test]
  fn test_empty_workspaces() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": []
      }),
    );
    fs.insert_json(
      root_dir().join("sub_dir").join("deno.json"),
      json!({
        "workspace": []
      }),
    );

    let workspace_dir = WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::Paths(&[root_dir().join("sub_dir")]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        ..Default::default()
      },
    )
    .unwrap();

    assert_eq!(
      workspace_dir
        .workspace
        .deno_jsons()
        .map(|d| d.specifier.to_file_path().unwrap())
        .collect::<Vec<_>>(),
      vec![root_dir().join("sub_dir").join("deno.json")]
    );
  }

  #[test]
  fn test_duplicate_members() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member/a", "./member/../member/a"],
      }),
    );
    fs.insert_json(root_dir().join("member/a/deno.json"), json!({}));

    let workspace_config_err = WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::Paths(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        ..Default::default()
      },
    )
    .err()
    .unwrap();

    assert_contains!(
      workspace_config_err.to_string(),
      "Cannot specify a workspace member twice ('./member/../member/a')."
    );
  }

  #[test]
  fn test_workspace_invalid_self_reference() {
    for reference in [".", "../sub_dir"] {
      let mut fs = TestFileSystem::default();
      fs.insert_json(
        root_dir().join("sub_dir").join("deno.json"),
        json!({
          "workspace": [reference],
        }),
      );

      let workspace_config_err = WorkspaceDirectory::discover(
        WorkspaceDiscoverStart::Paths(&[root_dir().join("sub_dir")]),
        &WorkspaceDiscoverOptions {
          fs: &fs,
          ..Default::default()
        },
      )
      .err()
      .unwrap();

      assert_contains!(
        workspace_config_err.to_string(),
        &format!("Remove the reference to the current config file (\"{reference}\") in \"workspaces\".")
      );
    }
  }

  #[test]
  fn test_workspaces_outside_root_config_dir() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["../a"]
      }),
    );

    let workspace_config_err = WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::Paths(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        ..Default::default()
      },
    )
    .err()
    .unwrap();

    assert_contains!(
      workspace_config_err.to_string(),
      "Workspace member must be nested in a directory under the workspace."
    );
  }

  #[test]
  fn test_workspaces_json_jsonc() {
    let mut fs = TestFileSystem::default();
    let config_text = json!({
      "workspace": [
        "./a",
        "./b",
      ],
    });
    let config_text_a = json!({
      "name": "a",
      "version": "0.1.0"
    });
    let config_text_b = json!({
      "name": "b",
      "version": "0.2.0"
    });

    fs.insert_json(root_dir().join("deno.json"), config_text);
    fs.insert_json(root_dir().join("a/deno.json"), config_text_a);
    fs.insert_json(root_dir().join("b/deno.jsonc"), config_text_b);

    let workspace_dir = WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::Paths(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(workspace_dir.workspace.config_folders.len(), 3);
  }

  #[test]
  fn test_tasks() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member", "./pkg_json"],
        "tasks": {
          "hi": "echo hi",
          "overwrite": "echo overwrite"
        }
      }),
    );
    fs.insert_json(
      root_dir().join("member/deno.json"),
      json!({
        "tasks": {
          "overwrite": "echo overwritten",
          "bye": "echo bye"
        }
      }),
    );
    fs.insert_json(
      root_dir().join("pkg_json/package.json"),
      json!({
        "scripts": {
          "script": "echo 1"
        }
      }),
    );
    let workspace_dir = WorkspaceDirectory::discover(
      // start at root for this test
      WorkspaceDiscoverStart::Paths(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        discover_pkg_json: true,
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
    let root_deno_json = Some(WorkspaceMemberTasksConfigFile {
      folder_url: Url::from_directory_path(root_dir()).unwrap(),
      tasks: IndexMap::from([
        ("hi".to_string(), Task::Definition("echo hi".to_string())),
        (
          "overwrite".to_string(),
          Task::Definition("echo overwrite".to_string()),
        ),
      ]),
    });
    let root = Some(WorkspaceMemberTasksConfig {
      deno_json: root_deno_json.clone(),
      package_json: None,
    });
    // root
    {
      let tasks_config = workspace_dir.to_tasks_config().unwrap();
      assert_eq!(
        tasks_config,
        WorkspaceTasksConfig {
          root: None,
          // the root context will have the root config as the member config
          member: root.clone(),
        }
      );
    }
    // member
    {
      let member_dir = workspace_dir.workspace.resolve_member_dir(
        &Url::from_directory_path(root_dir().join("member/deno.json")).unwrap(),
      );
      let tasks_config = member_dir.to_tasks_config().unwrap();
      assert_eq!(
        tasks_config,
        WorkspaceTasksConfig {
          root: root.clone(),
          member: Some(WorkspaceMemberTasksConfig {
            deno_json: Some(WorkspaceMemberTasksConfigFile {
              folder_url: Url::from_directory_path(root_dir().join("member"))
                .unwrap(),
              tasks: IndexMap::from([
                (
                  "overwrite".to_string(),
                  Task::Definition("echo overwritten".to_string())
                ),
                ("bye".to_string(), Task::Definition("echo bye".to_string())),
              ]),
            }),
            package_json: None,
          }),
        }
      );
    }
    // pkg json
    {
      let member_dir = workspace_dir.workspace.resolve_member_dir(
        &Url::from_directory_path(root_dir().join("pkg_json/package.json"))
          .unwrap(),
      );
      let tasks_config = member_dir.to_tasks_config().unwrap();
      assert_eq!(
        tasks_config,
        WorkspaceTasksConfig {
          root: None,
          member: Some(WorkspaceMemberTasksConfig {
            deno_json: root_deno_json.clone(),
            package_json: Some(WorkspaceMemberTasksConfigFile {
              folder_url: Url::from_directory_path(root_dir().join("pkg_json"))
                .unwrap(),
              tasks: IndexMap::from([(
                "script".to_string(),
                "echo 1".to_string()
              )]),
            }),
          })
        }
      );
    }
  }

  #[test]
  fn test_root_member_compiler_options() {
    let workspace_dir = workspace_for_root_and_member(
      json!({
        "compilerOptions": {
          "checkJs": true,
          "types": ["./types.d.ts"],
          "jsx": "react-jsx",
          "jsxImportSource": "npm:react",
          "jsxImportSourceTypes": "npm:@types/react",
        }
      }),
      json!({
        "compilerOptions": {
          "checkJs": false
        }
      }),
    );
    assert_eq!(
      workspace_dir
        .workspace
        .to_compiler_options()
        .unwrap()
        .unwrap()
        .0,
      json!({
        // ignores member config
        "checkJs": true,
        "jsx": "react-jsx",
        "jsxImportSource": "npm:react",
      })
    );
    assert_eq!(
      workspace_dir.workspace.to_compiler_option_types().unwrap(),
      vec![(
        Url::from_file_path(root_dir().join("deno.json")).unwrap(),
        vec!["./types.d.ts".to_string()]
      )]
    );
    assert_eq!(
      workspace_dir
        .workspace
        .to_maybe_jsx_import_source_config()
        .unwrap()
        .unwrap(),
      JsxImportSourceConfig {
        default_specifier: Some("npm:react".to_string()),
        default_types_specifier: Some("npm:@types/react".to_string()),
        module: "jsx-runtime".to_string(),
        base_url: Url::from_file_path(root_dir().join("deno.json")).unwrap(),
      }
    );
    assert_eq!(workspace_dir.workspace.check_js(), true);
    assert_eq!(
      workspace_dir
        .workspace
        .resolve_ts_config_for_emit(TsConfigType::Emit)
        .unwrap(),
      TsConfigForEmit {
        ts_config: TsConfig(json!({
          "allowImportingTsExtensions": true,
          "checkJs": true,
          "emitDecoratorMetadata": false,
          "experimentalDecorators": false,
          "importsNotUsedAsValues": "remove",
          "inlineSourceMap": true,
          "inlineSources": true,
          "sourceMap": false,
          "jsx": "react-jsx",
          "jsxFactory": "React.createElement",
          "jsxFragmentFactory": "React.Fragment",
          "resolveJsonModule": true,
          "jsxImportSource": "npm:react"
        })),
        maybe_ignored_options: None,
      }
    );
    assert_eq!(
      workspace_dir.workspace.diagnostics(),
      vec![WorkspaceDiagnostic {
        kind: WorkspaceDiagnosticKind::RootOnlyOption("compilerOptions"),
        config_url: Url::from_file_path(root_dir().join("member/deno.json"))
          .unwrap(),
      }]
    );
  }

  #[test]
  fn test_root_member_import_map() {
    let workspace_dir = workspace_for_root_and_member_with_fs(
      json!({
        "importMap": "./other.json",
      }),
      json!({
        "importMap": "./member.json",
      }),
      |fs| {
        fs.insert_json(root_dir().join("other.json"), json!({}));
        fs.insert_json(root_dir().join("member/member.json"), json!({}));
      },
    );
    assert_eq!(
      workspace_dir
        .workspace
        .to_import_map_specifier()
        .unwrap()
        .unwrap(),
      Url::from_file_path(root_dir().join("other.json")).unwrap()
    );
    assert_eq!(
      workspace_dir.workspace.diagnostics(),
      vec![WorkspaceDiagnostic {
        kind: WorkspaceDiagnosticKind::RootOnlyOption("importMap"),
        config_url: Url::from_file_path(root_dir().join("member/deno.json"))
          .unwrap(),
      }]
    );
  }

  #[test]
  fn test_root_member_patch() {
    let workspace_dir = workspace_for_root_and_member_with_fs(
      json!({
        "patch": ["../dir"],
      }),
      json!({
        "patch": [
          "../../dir"
        ],
      }),
      |fs| {
        fs.insert_json(root_dir().join("../dir/deno.json"), json!({}));
      },
    );
    assert_eq!(
      workspace_dir.workspace.diagnostics(),
      vec![WorkspaceDiagnostic {
        kind: WorkspaceDiagnosticKind::RootOnlyOption("patch"),
        config_url: Url::from_file_path(root_dir().join("member/deno.json"))
          .unwrap(),
      }]
    );
  }

  #[test]
  fn test_patch_of_patch() {
    let workspace_dir = workspace_for_root_and_member_with_fs(
      json!({
        "patch": ["../dir"],
      }),
      json!({}),
      |fs| {
        fs.insert_json(
          root_dir().join("../dir/deno.json"),
          json!({
            "patch": ["./subdir"] // will be ignored
          }),
        );
      },
    );
    assert_eq!(
      workspace_dir.workspace.diagnostics(),
      vec![WorkspaceDiagnostic {
        kind: WorkspaceDiagnosticKind::RootOnlyOption("patch"),
        config_url: Url::from_directory_path(root_dir())
          .unwrap()
          .join("../dir/deno.json")
          .unwrap(),
      }]
    );
  }

  #[test]
  fn test_patch_not_exists() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "patch": ["./member"]
      }),
    );
    let err = workspace_at_start_dir_err(&fs, &root_dir());
    match err.into_kind() {
      WorkspaceDiscoverErrorKind::ResolvePatch {
        patch,
        base,
        source,
      } => {
        assert_eq!(patch, "./member");
        assert_eq!(base, Url::from_directory_path(root_dir()).unwrap());
        match source {
          ResolveWorkspacePatchError::NotFound { dir_url } => {
            assert_eq!(
              dir_url,
              Url::from_directory_path(root_dir().join("member")).unwrap()
            );
          }
          _ => unreachable!(),
        }
      }
      _ => unreachable!(),
    }
  }

  #[test]
  fn test_patch_workspace_member() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member"],
        "patch": ["./member"]
      }),
    );
    fs.insert_json(root_dir().join("member/deno.json"), json!({}));
    let err = workspace_at_start_dir_err(&fs, &root_dir());
    match err.into_kind() {
      WorkspaceDiscoverErrorKind::ResolvePatch {
        patch,
        base,
        source,
      } => {
        assert_eq!(patch, "./member");
        assert_eq!(base, Url::from_directory_path(root_dir()).unwrap());
        assert!(matches!(
          source,
          ResolveWorkspacePatchError::WorkspaceMemberNotAllowed
        ));
      }
      _ => unreachable!(),
    }
  }

  #[tokio::test]
  async fn test_root_member_imports_and_scopes() {
    let workspace_dir = workspace_for_root_and_member(
      json!({
        "imports": {
          "@scope/pkg": "jsr:@scope/pkg@1"
        },
        "scopes": {
          "https://deno.land/x/": {
            "@scope/pkg": "jsr:@scope/pkg@2"
          }
        }
      }),
      json!({
        "imports": {
          "@scope/pkg": "jsr:@scope/pkg@3"
        },
        // will ignore this scopes because it's not in the root
        "scopes": {
          "https://deno.land/x/other": {
            "@scope/pkg": "jsr:@scope/pkg@4"
          }
        }
      }),
    );
    assert_eq!(
      workspace_dir.workspace.diagnostics(),
      vec![WorkspaceDiagnostic {
        kind: WorkspaceDiagnosticKind::RootOnlyOption("scopes"),
        config_url: Url::from_file_path(root_dir().join("member/deno.json"))
          .unwrap(),
      }]
    );
    let resolver = workspace_dir
      .workspace
      .create_resolver(Default::default(), |_| async move {
        unreachable!();
      })
      .await
      .unwrap();
    assert_eq!(
      serde_json::from_str::<serde_json::Value>(
        &resolver.maybe_import_map().unwrap().to_json()
      )
      .unwrap(),
      json!({
        "imports": {
          "@scope/pkg": "jsr:@scope/pkg@1",
          "@scope/pkg/": "jsr:/@scope/pkg@1/"
        },
        "scopes": {
          "https://deno.land/x/": {
            "@scope/pkg": "jsr:@scope/pkg@2",
            "@scope/pkg/": "jsr:/@scope/pkg@2/"
          },
          "./member/": {
            "@scope/pkg": "jsr:@scope/pkg@3",
            "@scope/pkg/": "jsr:/@scope/pkg@3/"
          }
        }
      })
    );
  }

  #[test]
  fn test_imports_with_import_map() {
    let workspace_dir = workspace_for_root_and_member_with_fs(
      json!({
        "imports": {},
        "importMap": "./other.json",
      }),
      json!({}),
      |fs| {
        fs.insert_json(root_dir().join("other.json"), json!({}));
      },
    );
    assert_eq!(
      workspace_dir
        .workspace
        .to_import_map_specifier()
        .unwrap()
        .unwrap(),
      Url::from_file_path(root_dir().join("other.json")).unwrap()
    );
    assert_eq!(
      workspace_dir.workspace.diagnostics(),
      vec![WorkspaceDiagnostic {
        kind: WorkspaceDiagnosticKind::ImportMapReferencingImportMap,
        config_url: Url::from_file_path(root_dir().join("deno.json")).unwrap(),
      }]
    );
  }

  #[test]
  fn test_root_member_exclude() {
    let workspace_dir = workspace_for_root_and_member(
      json!({
        "exclude": [
          "./root",
          "./member/vendor",
          "./**/*.js"
        ]
      }),
      json!({
        "exclude": [
          "./member_exclude",
          // unexclude from root
          "!./vendor"
        ]
      }),
    );
    assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
    let lint_config = workspace_dir
      .to_lint_config(FilePatterns::new_with_base(workspace_dir.dir_path()))
      .unwrap();
    assert_eq!(
      lint_config.files,
      FilePatterns {
        base: root_dir().join("member"),
        include: None,
        exclude: PathOrPatternSet::new(vec![
          PathOrPattern::Path(root_dir().join("member").join("vendor")),
          PathOrPattern::Pattern(
            GlobPattern::from_relative(&root_dir(), "./**/*.js").unwrap()
          ),
          PathOrPattern::Path(root_dir().join("member").join("member_exclude")),
          PathOrPattern::NegatedPath(root_dir().join("member").join("vendor")),
        ]),
      }
    );

    // will match because it was unexcluded in the member
    assert!(lint_config
      .files
      .matches_path(&root_dir().join("member/vendor"), PathKind::Directory))
  }

  #[test]
  fn test_root_member_lint_combinations() {
    let workspace_dir = workspace_for_root_and_member(
      json!({
        "lint": {
          "report": "json",
          "rules": {
            "tags": ["tag1"],
            "include": ["rule1"],
            "exclude": ["rule2"],
          },
        }
      }),
      json!({
        "lint": {
          "report": "pretty",
          "include": ["subdir"],
          "rules": {
            "tags": ["tag1"],
            "include": ["rule2"],
          }
        }
      }),
    );
    assert_eq!(
      workspace_dir.workspace.diagnostics(),
      vec![WorkspaceDiagnostic {
        kind: WorkspaceDiagnosticKind::RootOnlyOption("lint.report"),
        config_url: Url::from_file_path(root_dir().join("member/deno.json"))
          .unwrap(),
      }]
    );
    assert_eq!(
      workspace_dir.workspace.to_lint_config().unwrap(),
      WorkspaceLintConfig {
        report: Some("json".to_string()),
      }
    );
    let lint_config = workspace_dir
      .to_lint_config(FilePatterns::new_with_base(workspace_dir.dir_path()))
      .unwrap();
    assert_eq!(
      lint_config,
      LintConfig {
        options: LintOptionsConfig {
          rules: LintRulesConfig {
            tags: Some(vec!["tag1".to_string()]),
            include: Some(vec!["rule1".to_string(), "rule2".to_string()]),
            exclude: Some(vec![])
          },
        },
        files: FilePatterns {
          base: root_dir().join("member"),
          include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
            root_dir().join("member").join("subdir")
          )])),
          exclude: Default::default(),
        },
      }
    );

    // check the root context
    let root_ctx = workspace_dir
      .workspace
      .resolve_member_dir(&Url::from_directory_path(root_dir()).unwrap());
    let root_lint_config = root_ctx
      .to_lint_config(FilePatterns::new_with_base(root_ctx.dir_path()))
      .unwrap();
    assert_eq!(
      root_lint_config,
      LintConfig {
        options: LintOptionsConfig {
          rules: LintRulesConfig {
            tags: Some(vec!["tag1".to_string()]),
            include: Some(vec!["rule1".to_string()]),
            exclude: Some(vec!["rule2".to_string()])
          },
        },
        files: FilePatterns {
          base: root_dir(),
          include: None,
          // the workspace member will be excluded because that needs
          // to be resolved separately
          exclude: PathOrPatternSet::new(Vec::from([PathOrPattern::Path(
            root_dir().join("member")
          )])),
        },
      }
    );
  }

  #[test]
  fn test_root_member_fmt_combinations() {
    let workspace_dir = workspace_for_root_and_member(
      json!({
        "fmt": {
          "useTabs": true,
          "indentWidth": 4,
          "lineWidth": 80,
          "proseWrap": "never",
          "singleQuote": false,
          "semiColons": false,
        }
      }),
      json!({
        "fmt": {
          "exclude": ["subdir"],
          "useTabs": false,
          "indentWidth": 8,
          "lineWidth": 120,
          "proseWrap": "always",
          "singleQuote": true,
          "semiColons": true,
        }
      }),
    );
    assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
    let fmt_config = workspace_dir
      .to_fmt_config(FilePatterns::new_with_base(workspace_dir.dir_path()))
      .unwrap();
    assert_eq!(
      fmt_config,
      FmtConfig {
        options: FmtOptionsConfig {
          use_tabs: Some(false),
          line_width: Some(120),
          indent_width: Some(8),
          prose_wrap: Some(ProseWrap::Always),
          single_quote: Some(true),
          semi_colons: Some(true),
        },
        files: FilePatterns {
          base: root_dir().join("member"),
          include: None,
          exclude: PathOrPatternSet::new(vec![PathOrPattern::Path(
            root_dir().join("member").join("subdir")
          )]),
        },
      }
    );

    // check the root context
    let root_ctx = workspace_dir
      .workspace
      .resolve_member_dir(&Url::from_directory_path(root_dir()).unwrap());
    let root_fmt_config = root_ctx
      .to_fmt_config(FilePatterns::new_with_base(root_ctx.dir_path()))
      .unwrap();
    assert_eq!(
      root_fmt_config,
      FmtConfig {
        options: FmtOptionsConfig {
          use_tabs: Some(true),
          line_width: Some(80),
          indent_width: Some(4),
          prose_wrap: Some(ProseWrap::Never),
          single_quote: Some(false),
          semi_colons: Some(false),
        },
        files: FilePatterns {
          base: root_dir(),
          include: None,
          // the workspace member will be excluded because that needs
          // to be resolved separately
          exclude: PathOrPatternSet::new(Vec::from([PathOrPattern::Path(
            root_dir().join("member")
          )])),
        },
      }
    );
  }

  #[test]
  fn test_root_member_bench_combinations() {
    let workspace_dir = workspace_for_root_and_member(
      json!({}),
      json!({
        "bench": {
          "exclude": ["subdir"],
        }
      }),
    );
    assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
    let bench_config = workspace_dir
      .to_bench_config(FilePatterns::new_with_base(workspace_dir.dir_path()))
      .unwrap();
    assert_eq!(
      bench_config,
      BenchConfig {
        files: FilePatterns {
          base: root_dir().join("member"),
          include: None,
          exclude: PathOrPatternSet::new(vec![PathOrPattern::Path(
            root_dir().join("member").join("subdir")
          )]),
        },
      }
    );

    // check the root context
    let root_ctx = workspace_dir
      .workspace
      .resolve_member_dir(&Url::from_directory_path(root_dir()).unwrap());
    let root_bench_config = root_ctx
      .to_bench_config(FilePatterns::new_with_base(root_ctx.dir_path()))
      .unwrap();
    assert_eq!(
      root_bench_config,
      BenchConfig {
        files: FilePatterns {
          base: root_dir(),
          include: None,
          // the workspace member will be excluded because that needs
          // to be resolved separately
          exclude: PathOrPatternSet::new(Vec::from([PathOrPattern::Path(
            root_dir().join("member")
          )])),
        },
      }
    );
  }

  #[test]
  fn test_root_member_test_combinations() {
    let workspace_dir = workspace_for_root_and_member(
      json!({}),
      json!({
        "test": {
          "include": ["subdir"],
        }
      }),
    );
    assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
    let config = workspace_dir
      .to_test_config(FilePatterns::new_with_base(workspace_dir.dir_path()))
      .unwrap();
    assert_eq!(
      config,
      TestConfig {
        files: FilePatterns {
          base: root_dir().join("member"),
          include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
            root_dir().join("member").join("subdir")
          )])),
          exclude: Default::default(),
        },
      }
    );

    // check the root context
    let root_ctx = workspace_dir
      .workspace
      .resolve_member_dir(&Url::from_directory_path(root_dir()).unwrap());
    let root_test_config = root_ctx
      .to_test_config(FilePatterns::new_with_base(root_ctx.dir_path()))
      .unwrap();
    assert_eq!(
      root_test_config,
      TestConfig {
        files: FilePatterns {
          base: root_dir(),
          include: None,
          // the workspace member will be excluded because that needs
          // to be resolved separately
          exclude: PathOrPatternSet::new(Vec::from([PathOrPattern::Path(
            root_dir().join("member")
          )])),
        },
      }
    );
  }

  #[test]
  fn test_root_member_publish_combinations() {
    let workspace_dir = workspace_for_root_and_member(
      json!({
        "publish": {
          "exclude": ["other"]
        }
      }),
      json!({
        "publish": {
          "include": ["subdir"],
        },
        "exclude": [
          "./exclude_dir"
        ],
      }),
    );
    assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
    let config = workspace_dir.to_publish_config().unwrap();
    assert_eq!(
      config,
      PublishConfig {
        files: FilePatterns {
          base: root_dir().join("member"),
          include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
            root_dir().join("member").join("subdir")
          )])),
          exclude: PathOrPatternSet::new(vec![PathOrPattern::Path(
            root_dir().join("member").join("exclude_dir")
          ),]),
        },
      }
    );

    // check the root context
    let root_publish_config = workspace_dir
      .workspace
      .resolve_member_dir(&Url::from_directory_path(root_dir()).unwrap())
      .to_publish_config()
      .unwrap();
    assert_eq!(
      root_publish_config,
      PublishConfig {
        files: FilePatterns {
          base: root_dir(),
          include: None,
          exclude: PathOrPatternSet::new(Vec::from([
            PathOrPattern::Path(root_dir().join("other")),
            // the workspace member will be excluded because that needs
            // to be resolved separately
            PathOrPattern::Path(root_dir().join("member")),
          ])),
        },
      }
    );
  }

  #[test]
  fn test_root_member_empty_config_resolves_excluded_members() {
    let workspace_dir = workspace_for_root_and_member(json!({}), json!({}));
    assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
    let expected_root_files = FilePatterns {
      base: root_dir(),
      include: None,
      // the workspace member will be excluded because that needs
      // to be resolved separately
      exclude: PathOrPatternSet::new(Vec::from([PathOrPattern::Path(
        root_dir().join("member"),
      )])),
    };
    let root_ctx = workspace_dir
      .workspace
      .resolve_member_dir(&Url::from_directory_path(root_dir()).unwrap());
    let expected_member_files = FilePatterns {
      base: root_dir().join("member"),
      include: None,
      exclude: Default::default(),
    };

    for (expected_files, ctx) in [
      (expected_root_files, root_ctx),
      (expected_member_files, workspace_dir),
    ] {
      assert_eq!(
        ctx
          .to_bench_config(FilePatterns::new_with_base(ctx.dir_path()))
          .unwrap(),
        BenchConfig {
          files: expected_files.clone(),
        }
      );
      assert_eq!(
        ctx
          .to_fmt_config(FilePatterns::new_with_base(ctx.dir_path()))
          .unwrap(),
        FmtConfig {
          options: Default::default(),
          files: expected_files.clone(),
        }
      );
      assert_eq!(
        ctx
          .to_lint_config(FilePatterns::new_with_base(ctx.dir_path()))
          .unwrap(),
        LintConfig {
          files: expected_files.clone(),
          options: Default::default(),
        }
      );
      assert_eq!(
        ctx
          .to_test_config(FilePatterns::new_with_base(ctx.dir_path()))
          .unwrap(),
        TestConfig {
          files: expected_files.clone(),
        }
      );
      assert_eq!(
        ctx.to_publish_config().unwrap(),
        PublishConfig {
          files: expected_files.clone(),
        }
      );
    }
  }

  #[test]
  fn test_root_member_root_only_in_member() {
    let workspace_dir = workspace_for_root_and_member(
      json!({
        "unstable": ["byonm"],
        "lock": false,
        "nodeModulesDir": false,
        "vendor": true,
      }),
      json!({
        "unstable": ["sloppy-imports"],
        "lock": true,
        "nodeModulesDir": true,
        "vendor": false,
      }),
    );
    // ignores member config
    assert_eq!(
      workspace_dir.workspace.unstable_features(),
      &["byonm".to_string()]
    );
    assert!(workspace_dir.workspace.has_unstable("byonm"));
    assert!(!workspace_dir.workspace.has_unstable("sloppy-imports"));
    assert_eq!(
      workspace_dir.workspace.resolve_lockfile_path().unwrap(),
      None
    );
    assert_eq!(workspace_dir.workspace.node_modules_dir(), Some(false));
    assert_eq!(
      workspace_dir.workspace.resolve_lockfile_path().unwrap(),
      None
    );
    assert_eq!(
      workspace_dir.workspace.vendor_dir_path().unwrap(),
      &root_dir().join("vendor")
    );
    assert_eq!(
      workspace_dir.workspace.diagnostics(),
      vec![
        WorkspaceDiagnostic {
          kind: WorkspaceDiagnosticKind::RootOnlyOption("lock"),
          config_url: Url::from_file_path(root_dir().join("member/deno.json"))
            .unwrap(),
        },
        WorkspaceDiagnostic {
          kind: WorkspaceDiagnosticKind::RootOnlyOption("nodeModulesDir"),
          config_url: Url::from_file_path(root_dir().join("member/deno.json"))
            .unwrap(),
        },
        WorkspaceDiagnostic {
          kind: WorkspaceDiagnosticKind::RootOnlyOption("unstable"),
          config_url: Url::from_file_path(root_dir().join("member/deno.json"))
            .unwrap(),
        },
        WorkspaceDiagnostic {
          kind: WorkspaceDiagnosticKind::RootOnlyOption("vendor"),
          config_url: Url::from_file_path(root_dir().join("member/deno.json"))
            .unwrap(),
        }
      ]
    );
  }

  #[test]
  fn test_root_member_pkg_only_fields_on_workspace_root() {
    let workspace_dir = workspace_for_root_and_member(
      json!({
        "name": "@scope/name",
        "version": "1.0.0",
        "exports": "./main.ts"
      }),
      json!({}),
    );
    // this is fine because we can tell it's a package by it having name and exports fields
    assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
  }

  #[test]
  fn test_root_member_workspace_on_member() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member"]
      }),
    );
    fs.insert_json(
      root_dir().join("member/deno.json"),
      json!({
        "workspace": ["./other_dir"]
      }),
    );
    let workspace_dir = WorkspaceDirectory::discover(
      // start at root for this test
      WorkspaceDiscoverStart::Paths(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(
      workspace_dir.workspace.diagnostics(),
      vec![WorkspaceDiagnostic {
        kind: WorkspaceDiagnosticKind::RootOnlyOption("workspace"),
        config_url: Url::from_file_path(root_dir().join("member/deno.json"))
          .unwrap(),
      }]
    );
  }

  #[test]
  fn test_workspaces_property() {
    run_single_json_diagnostics_test(
      json!({
        "workspaces": ["./member"]
      }),
      vec![WorkspaceDiagnosticKind::InvalidWorkspacesOption],
    );
  }

  #[test]
  fn test_workspaces_missing_exports() {
    run_single_json_diagnostics_test(
      json!({
        "name": "@scope/name",
      }),
      vec![WorkspaceDiagnosticKind::MissingExports],
    );
  }

  fn run_single_json_diagnostics_test(
    json: serde_json::Value,
    kinds: Vec<WorkspaceDiagnosticKind>,
  ) {
    let mut fs = TestFileSystem::default();
    fs.insert_json(root_dir().join("deno.json"), json);
    let workspace_dir = WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::Paths(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(
      workspace_dir.workspace.diagnostics(),
      kinds
        .into_iter()
        .map(|kind| {
          WorkspaceDiagnostic {
            kind,
            config_url: Url::from_file_path(root_dir().join("deno.json"))
              .unwrap(),
          }
        })
        .collect::<Vec<_>>()
    );
  }

  #[test]
  fn test_multiple_pkgs_same_name() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member1", "./member2"]
      }),
    );
    let pkg = json!({
      "name": "@scope/pkg",
      "version": "1.0.0",
      "exports": "./main.ts",
    });
    fs.insert_json(root_dir().join("member1").join("deno.json"), pkg.clone());
    fs.insert_json(root_dir().join("member2").join("deno.json"), pkg.clone());
    let err = WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::Paths(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        ..Default::default()
      },
    )
    .unwrap_err();
    match err.into_kind() {
      WorkspaceDiscoverErrorKind::ResolveMember(
        ResolveWorkspaceMemberError::DuplicatePackageName {
          name,
          deno_json_url,
          other_deno_json_url,
        },
      ) => {
        assert_eq!(name, "@scope/pkg");
        assert_eq!(
          deno_json_url,
          Url::from_file_path(root_dir().join("member2").join("deno.json"))
            .unwrap()
        );
        assert_eq!(
          other_deno_json_url,
          Url::from_file_path(root_dir().join("member1").join("deno.json"))
            .unwrap()
        );
      }
      _ => unreachable!(),
    }
  }

  #[test]
  fn test_packages_for_publish_non_workspace() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "name": "@scope/pkg",
        "version": "1.0.0",
        "exports": "./main.ts",
      }),
    );
    let workspace_dir = workspace_at_start_dir(&fs, &root_dir().join("member"));
    assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
    let jsr_pkgs = workspace_dir.jsr_packages_for_publish();
    let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
    assert_eq!(names, vec!["@scope/pkg"]);
  }

  #[test]
  fn test_packages_for_publish_workspace() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./a", "./b", "./c", "./d"]
      }),
    );
    fs.insert_json(
      root_dir().join("a/deno.json"),
      json!({
        "name": "@scope/a",
        "version": "1.0.0",
        "exports": "./main.ts",
      }),
    );
    fs.insert_json(
      root_dir().join("b/deno.json"),
      json!({
        "name": "@scope/b",
        "version": "1.0.0",
        "exports": "./main.ts",
      }),
    );
    fs.insert_json(
      root_dir().join("c/deno.json"),
      // not a package
      json!({}),
    );
    fs.insert_json(
      root_dir().join("d/package.json"),
      json!({
        "name": "pkg",
        "version": "1.0.0",
      }),
    );
    // root
    {
      let workspace_dir = workspace_at_start_dir(&fs, &root_dir());
      assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace_dir.jsr_packages_for_publish();
      let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
      assert_eq!(names, vec!["@scope/a", "@scope/b"]);
    }
    // member
    {
      let workspace_dir = workspace_at_start_dir(&fs, &root_dir().join("a"));
      assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace_dir.jsr_packages_for_publish();
      let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
      assert_eq!(names, vec!["@scope/a"]);
    }
    // member, not a package
    {
      let workspace_dir = workspace_at_start_dir(&fs, &root_dir().join("c"));
      assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace_dir.jsr_packages_for_publish();
      assert!(jsr_pkgs.is_empty());
    }
    // package.json
    {
      let workspace_dir = workspace_at_start_dir(&fs, &root_dir().join("d"));
      assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace_dir.jsr_packages_for_publish();
      assert!(jsr_pkgs.is_empty());

      // while we're here, test this
      assert_eq!(
        workspace_dir
          .workspace
          .package_jsons()
          .map(|p| p.dir_path().to_path_buf())
          .collect::<Vec<_>>(),
        vec![root_dir().join("d")]
      );
      assert_eq!(
        workspace_dir
          .workspace
          .npm_packages()
          .into_iter()
          .map(|p| p.pkg_json.dir_path().to_path_buf())
          .collect::<Vec<_>>(),
        vec![root_dir().join("d")]
      );
    }
  }

  #[test]
  fn test_packages_for_publish_root_is_package() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "name": "@scope/root",
        "version": "1.0.0",
        "exports": "./main.ts",
        "workspace": ["./member"]
      }),
    );
    fs.insert_json(
      root_dir().join("member/deno.json"),
      json!({
        "name": "@scope/pkg",
        "version": "1.0.0",
        "exports": "./main.ts",
      }),
    );
    // in a member
    {
      let workspace_dir =
        workspace_at_start_dir(&fs, &root_dir().join("member"));
      assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace_dir.jsr_packages_for_publish();
      let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
      assert_eq!(names, vec!["@scope/pkg"]);
    }
    // at the root
    {
      let workspace_dir = workspace_at_start_dir(&fs, &root_dir());
      assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace_dir.jsr_packages_for_publish();
      let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
      // Only returns the root package because it allows for publishing
      // this individually. If someone wants the behaviour of publishing
      // the entire workspace then they should move each package to a descendant
      // directory.
      assert_eq!(names, vec!["@scope/root"]);
    }
  }

  #[test]
  fn test_packages_for_publish_root_not_package() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member"]
      }),
    );
    fs.insert_json(
      root_dir().join("member/deno.json"),
      json!({
        "name": "@scope/pkg",
        "version": "1.0.0",
        "exports": "./main.ts",
      }),
    );
    // the workspace is not a jsr package so publish the members
    let workspace_dir = workspace_at_start_dir(&fs, &root_dir());
    assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
    let jsr_pkgs = workspace_dir.jsr_packages_for_publish();
    let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
    assert_eq!(names, vec!["@scope/pkg"]);
  }

  #[test]
  fn test_packages_for_publish_npm_workspace() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["./a", "./b", "./c", "./d"]
      }),
    );
    fs.insert_json(root_dir().join("a/package.json"), json!({}));
    fs.insert_json(
      root_dir().join("a/deno.json"),
      json!({
        "name": "@scope/a",
        "version": "1.0.0",
        "exports": "./main.ts",
      }),
    );
    fs.insert_json(root_dir().join("b/package.json"), json!({}));
    fs.insert_json(
      root_dir().join("b/deno.json"),
      json!({
        "name": "@scope/b",
        "version": "1.0.0",
        "exports": "./main.ts",
      }),
    );
    fs.insert_json(root_dir().join("c/package.json"), json!({}));
    fs.insert_json(
      root_dir().join("c/deno.json"),
      // not a package
      json!({}),
    );
    fs.insert_json(
      root_dir().join("d/package.json"),
      json!({
        "name": "pkg",
        "version": "1.0.0",
      }),
    );
    // root
    {
      let workspace_dir = workspace_at_start_dir(&fs, &root_dir());
      assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace_dir.jsr_packages_for_publish();
      let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
      assert_eq!(names, vec!["@scope/a", "@scope/b"]);
    }
    // member
    {
      let workspace_dir = workspace_at_start_dir(&fs, &root_dir().join("a"));
      assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace_dir.jsr_packages_for_publish();
      let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
      assert_eq!(names, vec!["@scope/a"]);
    }
    // member, not a package
    {
      let workspace_dir = workspace_at_start_dir(&fs, &root_dir().join("c"));
      assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace_dir.jsr_packages_for_publish();
      assert!(jsr_pkgs.is_empty());
    }
    // package.json
    {
      let workspace_dir = workspace_at_start_dir(&fs, &root_dir().join("d"));
      assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace_dir.jsr_packages_for_publish();
      assert!(jsr_pkgs.is_empty());
      assert_eq!(
        workspace_dir
          .workspace
          .npm_packages()
          .into_iter()
          .map(|p| p.pkg_json.dir_path().to_path_buf())
          .collect::<Vec<_>>(),
        vec![root_dir().join("d")]
      );
    }
  }

  #[test]
  fn test_no_auto_discovery_node_modules_dir() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(root_dir().join("deno.json"), json!({}));
    fs.insert_json(
      root_dir().join("node_modules/package/package.json"),
      json!({
        "name": "@scope/pkg",
        "version": "1.0.0"
      }),
    );
    let workspace_dir = workspace_at_start_dir(
      &fs,
      &root_dir().join("node_modules/package/sub_dir"),
    );
    assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 0);
    assert_eq!(workspace_dir.workspace.deno_jsons().count(), 1);
  }

  #[test]
  fn test_deno_workspace_member_no_config_file_error() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member"]
      }),
    );
    // no deno.json in this folder, so should error
    let err = workspace_at_start_dir_err(&fs, &root_dir().join("package"));
    assert_eq!(err.to_string(), normalize_err_text("Could not find config file for workspace member in '[ROOT_DIR_URL]/member/'."));
  }

  #[test]
  fn test_deno_workspace_member_deno_json_member_name() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member/deno.json"]
      }),
    );
    // no deno.json in this folder and the name was deno.json so give an error
    let err = workspace_at_start_dir_err(&fs, &root_dir().join("package"));
    assert_eq!(err.to_string(), normalize_err_text(concat!(
      "Could not find config file for workspace member in '[ROOT_DIR_URL]/member/deno.json/'. ",
      "Ensure you specify the directory and not the configuration file in the workspace member."
    )));
  }

  #[test]
  fn test_deno_member_not_referenced_in_deno_workspace() {
    fn assert_err(err: &WorkspaceDiscoverError, config_file_path: &Path) {
      match err.as_kind() {
        WorkspaceDiscoverErrorKind::ConfigNotWorkspaceMember {
          workspace_url,
          config_url,
        } => {
          assert_eq!(
            workspace_url.as_ref(),
            &Url::from_directory_path(root_dir()).unwrap()
          );
          assert_eq!(
            config_url,
            &Url::from_file_path(config_file_path).unwrap()
          );
        }
        _ => unreachable!(),
      }
    }

    for file_name in ["deno.json", "deno.jsonc"] {
      let config_file_path = root_dir().join("member-b").join(file_name);
      let mut fs = TestFileSystem::default();
      fs.insert_json(
        root_dir().join("deno.json"),
        json!({
          "workspace": ["./member-a"],
        }),
      );
      fs.insert_json(root_dir().join("member-a/deno.json"), json!({}));
      fs.insert_json(config_file_path.clone(), json!({}));
      let err = workspace_at_start_dir_err(&fs, &root_dir().join("member-b"));
      assert_err(&err, &config_file_path);

      // try for when the config file is specified as well
      let err = WorkspaceDirectory::discover(
        WorkspaceDiscoverStart::ConfigFile(&config_file_path),
        &WorkspaceDiscoverOptions {
          fs: &fs,
          discover_pkg_json: true,
          ..Default::default()
        },
      )
      .unwrap_err();
      assert_err(&err, &config_file_path);
    }
  }

  #[test]
  fn test_config_not_deno_workspace_member_non_natural_config_file_name() {
    for file_name in ["other-name.json", "deno.jsonc"] {
      let mut fs = TestFileSystem::default();
      fs.insert_json(
        root_dir().join("deno.json"),
        json!({
          "workspace": ["./member-a", "./member-b"],
        }),
      );
      fs.insert_json(root_dir().join("member-a/deno.json"), json!({}));
      // this is the "natural" config file that would be discovered by
      // workspace discovery and since the file name specified does not
      // match it, the workspace is not discovered and an error does not
      // occur
      fs.insert_json(root_dir().join("member-b/deno.json"), json!({}));
      let config_file_path = root_dir().join("member-b").join(file_name);
      fs.insert_json(config_file_path.clone(), json!({}));
      let workspace_dir = WorkspaceDirectory::discover(
        WorkspaceDiscoverStart::ConfigFile(&config_file_path),
        &WorkspaceDiscoverOptions {
          fs: &fs,
          discover_pkg_json: true,
          ..Default::default()
        },
      )
      .unwrap();
      assert_eq!(
        workspace_dir
          .workspace
          .deno_jsons()
          .map(|c| c.specifier.to_file_path().unwrap())
          .collect::<Vec<_>>(),
        vec![config_file_path]
      );
    }
  }

  #[test]
  fn test_npm_package_not_referenced_in_deno_workspace() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member"]
      }),
    );
    fs.insert_json(root_dir().join("member/deno.json"), json!({}));
    fs.insert_json(root_dir().join("package/package.json"), json!({}));
    // npm package needs to be a member of the deno workspace
    let err = workspace_at_start_dir_err(&fs, &root_dir().join("package"));
    assert_eq!(
      err.to_string(),
      normalize_err_text(
        "Config file must be a member of the workspace.
  Config: [ROOT_DIR_URL]/package/package.json
  Workspace: [ROOT_DIR_URL]/"
      )
    );
  }

  #[test]
  fn test_multiple_workspaces_npm_package_referenced_in_package_json_workspace()
  {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member"]
      }),
    );
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["./package"]
      }),
    );
    fs.insert_json(root_dir().join("member/deno.json"), json!({}));
    fs.insert_json(root_dir().join("package/package.json"), json!({}));
    let workspace_dir =
      workspace_at_start_dir(&fs, &root_dir().join("package"));
    assert_eq!(workspace_dir.workspace.diagnostics(), Vec::new());
    assert_eq!(workspace_dir.workspace.deno_jsons().count(), 2);
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 2);
  }

  #[test]
  fn test_npm_workspace_package_json_and_deno_json_ok() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["./member"]
      }),
    );
    fs.insert_json(root_dir().join("member/deno.json"), json!({}));
    fs.insert_json(root_dir().join("member/package.json"), json!({}));
    let workspace_dir =
      workspace_at_start_dir(&fs, &root_dir().join("package"));
    assert_eq!(workspace_dir.workspace.diagnostics(), Vec::new());
    assert_eq!(workspace_dir.workspace.deno_jsons().count(), 1);
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 2);
  }

  #[test]
  fn test_npm_workspace_member_deno_json_error() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["./member"]
      }),
    );
    // no package.json in this folder, so should error
    fs.insert_json(root_dir().join("member/deno.json"), json!({}));
    let err = workspace_at_start_dir_err(&fs, &root_dir().join("package"));
    assert_eq!(err.to_string(), normalize_err_text("Could not find package.json for workspace member in '[ROOT_DIR_URL]/member/'."));
  }

  #[test]
  fn test_npm_workspace_member_no_config_file_error() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["./member"]
      }),
    );
    // no package.json in this folder, so should error
    let err = workspace_at_start_dir_err(&fs, &root_dir().join("package"));
    assert_eq!(err.to_string(), normalize_err_text("Could not find package.json for workspace member in '[ROOT_DIR_URL]/member/'."));
  }

  #[test]
  fn test_npm_workspace_globs() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["./packages/*"]
      }),
    );
    fs.insert_json(
      root_dir().join("packages/package-a/package.json"),
      json!({}),
    );
    fs.insert_json(
      root_dir().join("packages/package-b/package.json"),
      json!({}),
    );
    let workspace_dir =
      workspace_at_start_dir(&fs, &root_dir().join("packages"));
    assert_eq!(workspace_dir.workspace.diagnostics(), Vec::new());
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 3);
  }

  #[test]
  fn test_npm_workspace_ignores_vendor_folder() {
    for (is_vendor, expected_count) in [(true, 3), (false, 4)] {
      let mut fs = TestFileSystem::default();
      fs.insert_json(
        root_dir().join("deno.json"),
        json!({
          "vendor": is_vendor,
        }),
      );
      fs.insert_json(
        root_dir().join("package.json"),
        json!({
          "workspaces": ["./**/*"]
        }),
      );
      fs.insert_json(
        root_dir().join("packages/package-a/package.json"),
        json!({}),
      );
      fs.insert_json(
        root_dir().join("packages/package-b/package.json"),
        json!({}),
      );
      fs.insert_json(
        root_dir().join("vendor/package-c/package.json"),
        json!({}),
      );
      let workspace_dir = workspace_at_start_dir(&fs, &root_dir());
      assert_eq!(workspace_dir.workspace.diagnostics(), Vec::new());
      assert_eq!(
        workspace_dir.workspace.package_jsons().count(),
        expected_count
      );
    }
  }

  #[test]
  fn test_npm_workspace_negations() {
    for negation in ["!ignored/package-c", "!ignored/**"] {
      let mut fs = TestFileSystem::default();
      fs.insert_json(
        root_dir().join("package.json"),
        json!({
          "workspaces": [
            "**/*",
            negation,
          ]
        }),
      );
      fs.insert_json(
        root_dir().join("packages/package-a/package.json"),
        json!({}),
      );
      fs.insert_json(
        root_dir().join("packages/package-b/package.json"),
        json!({}),
      );
      fs.insert_json(
        root_dir().join("ignored/package-c/package.json"),
        json!({}),
      );
      let workspace_dir = workspace_at_start_dir(&fs, &root_dir());
      assert_eq!(workspace_dir.workspace.diagnostics(), Vec::new());
      assert_eq!(workspace_dir.workspace.package_jsons().count(), 3);
    }
  }

  #[test]
  fn test_npm_workspace_self_reference_and_duplicate_references_ok() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": [
          ".",
          "./member",
          "./member",
          "**/*"
        ]
      }),
    );
    fs.insert_json(root_dir().join("member/package.json"), json!({}));
    let workspace_dir = workspace_at_start_dir(&fs, &root_dir());
    assert_eq!(workspace_dir.workspace.diagnostics(), Vec::new());
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 2);
  }

  #[test]
  fn test_npm_workspace_start_deno_json_not_in_workspace() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["./package"]
      }),
    );
    fs.insert_json(
      root_dir().join("member/deno.json"),
      json!({
        "unstable": ["byonm"],
      }),
    );
    fs.insert_json(root_dir().join("package/package.json"), json!({}));
    // only resolves the member because it's not part of the workspace
    let workspace_dir = workspace_at_start_dir(&fs, &root_dir().join("member"));
    assert_eq!(workspace_dir.workspace.diagnostics(), Vec::new());
    assert_eq!(workspace_dir.workspace.deno_jsons().count(), 1);
    assert_eq!(
      workspace_dir.workspace.root_dir().to_file_path().unwrap(),
      root_dir().join("member")
    );
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 0);
    assert!(workspace_dir.workspace.has_unstable("byonm"));
    assert_eq!(
      workspace_dir.workspace.resolve_lockfile_path().unwrap(),
      Some(root_dir().join("member/deno.lock"))
    );
  }

  #[test]
  fn test_npm_workspace_start_deno_json_part_of_workspace() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["./member"]
      }),
    );
    fs.insert_json(
      root_dir().join("member/deno.json"),
      json!({
        "lock": false,
        "unstable": ["byonm"],
      }),
    );
    fs.insert_json(root_dir().join("member/package.json"), json!({}));
    let workspace_dir = workspace_at_start_dir(&fs, &root_dir().join("member"));
    assert_eq!(
      workspace_dir
        .workspace
        .diagnostics()
        .into_iter()
        .map(|d| d.kind)
        .collect::<Vec<_>>(),
      vec![
        WorkspaceDiagnosticKind::RootOnlyOption("lock"),
        WorkspaceDiagnosticKind::RootOnlyOption("unstable")
      ]
    );
    assert_eq!(workspace_dir.workspace.deno_jsons().count(), 1);
    assert_eq!(
      workspace_dir.workspace.root_dir().to_file_path().unwrap(),
      root_dir()
    );
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 2);
    assert!(!workspace_dir.workspace.has_unstable("byonm"));
    assert_eq!(
      workspace_dir.workspace.resolve_lockfile_path().unwrap(),
      Some(root_dir().join("deno.lock"))
    );
  }

  #[test]
  fn test_npm_workspace_start_deno_json_part_of_workspace_sub_folder() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["./member"]
      }),
    );
    fs.insert_json(
      root_dir().join("member/deno.json"),
      json!({
        "unstable": ["byonm"],
      }),
    );
    fs.insert_json(root_dir().join("member/package.json"), json!({}));
    fs.insert("member/sub/sub_folder/sub/file.ts", "");
    let workspace_dir = workspace_at_start_dir(
      &fs,
      // note how we're starting in a sub folder of the member
      &root_dir().join("member/sub/sub_folder/sub/"),
    );
    assert_eq!(
      workspace_dir
        .workspace
        .diagnostics()
        .into_iter()
        .map(|d| d.kind)
        .collect::<Vec<_>>(),
      vec![WorkspaceDiagnosticKind::RootOnlyOption("unstable")]
    );
    assert_eq!(workspace_dir.workspace.deno_jsons().count(), 1);
    assert_eq!(
      workspace_dir.workspace.root_dir().to_file_path().unwrap(),
      root_dir()
    );
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 2);
    assert!(!workspace_dir.workspace.has_unstable("byonm"));
  }

  #[test]
  fn test_npm_workspace_start_deno_json_part_of_workspace_sub_folder_other_deno_json(
  ) {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["./member", "./member/sub"]
      }),
    );
    fs.insert_json(
      root_dir().join("member/deno.json"),
      json!({ "unstable": ["sloppy-imports"] }),
    );
    fs.insert_json(root_dir().join("member/package.json"), json!({}));
    fs.insert_json(
      root_dir().join("member/sub/deno.json"),
      json!({ "unstable": ["byonm"] }),
    );
    fs.insert_json(root_dir().join("member/sub/package.json"), json!({}));
    fs.insert("member/sub/sub_folder/sub/file.ts", "");
    let workspace_dir = workspace_at_start_dir(
      &fs,
      // note how we're starting in a sub folder of the member
      &root_dir().join("member/sub/sub_folder/sub/"),
    );
    assert_eq!(workspace_dir.workspace.diagnostics().len(), 2); // for each unstable
    assert_eq!(workspace_dir.workspace.deno_jsons().count(), 2);
    assert_eq!(
      workspace_dir.workspace.root_dir.to_file_path().unwrap(),
      root_dir()
    );
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 3);
    assert!(!workspace_dir.workspace.has_unstable("sloppy-imports"));
    assert!(!workspace_dir.workspace.has_unstable("byonm"));
  }

  #[test]
  fn test_npm_workspace_start_package_json_not_in_workspace() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["./package"]
      }),
    );
    fs.insert_json(root_dir().join("member/package.json"), json!({}));
    fs.insert_json(root_dir().join("package/package.json"), json!({}));
    // only resolves the member because it's not part of the workspace
    let workspace_dir = workspace_at_start_dir(&fs, &root_dir().join("member"));
    assert_eq!(workspace_dir.workspace.diagnostics(), Vec::new());
    assert_eq!(workspace_dir.workspace.deno_jsons().count(), 0);
    assert_eq!(
      workspace_dir.workspace.root_dir().to_file_path().unwrap(),
      root_dir().join("member")
    );
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 1);
  }

  #[test]
  fn test_resolve_multiple_dirs() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("workspace").join("deno.json"),
      json!({
        "workspace": ["./member"]
      }),
    );
    fs.insert_json(
      root_dir().join("workspace").join("member/deno.json"),
      json!({
        "name": "@scope/pkg",
        "version": "1.0.0",
        "exports": "./main.ts",
      }),
    );
    let workspace_dir = workspace_at_start_dirs(
      &fs,
      &[
        root_dir().join("workspace/member"),
        root_dir().join("other_dir"), // will be ignored because it's not in the workspace
      ],
    )
    .unwrap();
    assert_eq!(workspace_dir.workspace.diagnostics(), vec![]);
    let jsr_pkgs = workspace_dir.jsr_packages_for_publish();
    let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
    assert_eq!(names, vec!["@scope/pkg"]);
  }

  #[test]
  fn test_npm_workspace_ignore_pkg_json_between_member_and_root() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["./member/nested"]
      }),
    );
    // will ignore this one
    fs.insert_json(root_dir().join("member/package.json"), json!({}));
    fs.insert_json(root_dir().join("member/nested/package.json"), json!({}));
    // only resolves the member because it's not part of the workspace
    let workspace_dir =
      workspace_at_start_dir(&fs, &root_dir().join("member/nested"));
    assert_eq!(workspace_dir.workspace.diagnostics(), Vec::new());
    assert_eq!(workspace_dir.workspace.deno_jsons().count(), 0);
    assert_eq!(
      workspace_dir
        .workspace
        .package_jsons()
        .map(|p| p.path.clone())
        .collect::<Vec<_>>(),
      vec![
        root_dir().join("package.json"),
        root_dir().join("member/nested/package.json"),
      ]
    );
  }

  #[test]
  fn test_npm_workspace_ignore_deno_json_between_member_and_root() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("package.json"),
      json!({
        "workspaces": ["./member/nested"]
      }),
    );
    // will ignore this one
    fs.insert_json(root_dir().join("member/deno.json"), json!({}));
    fs.insert_json(root_dir().join("member/nested/package.json"), json!({}));
    // only resolves the member because it's not part of the workspace
    let workspace_dir =
      workspace_at_start_dir(&fs, &root_dir().join("member/nested"));
    assert_eq!(workspace_dir.workspace.diagnostics(), Vec::new());
    assert_eq!(workspace_dir.workspace.deno_jsons().count(), 0);
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 2);
  }

  #[test]
  fn test_resolve_multiple_dirs_outside_config() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("workspace/deno.json"),
      json!({
        "workspace": {
          "members": ["./member"]
        },
      }),
    );
    fs.insert_json(root_dir().join("workspace/member/deno.json"), json!({}));
    // this one will cause issues because it's not in the workspace
    fs.insert_json(root_dir().join("other_dir/deno.json"), json!({}));
    let err = workspace_at_start_dirs(
      &fs,
      &[
        root_dir().join("workspace/member"),
        root_dir().join("other_dir"),
      ],
    )
    .unwrap_err();
    assert_eq!(err.to_string(), normalize_err_text("Command resolved to multiple config files. Ensure all specified paths are within the same workspace.
  First: [ROOT_DIR_URL]/workspace/deno.json
  Second: [ROOT_DIR_URL]/other_dir/deno.json"));
  }

  #[test]
  fn test_resolve_multiple_dirs_outside_workspace() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("workspace/deno.json"),
      json!({
        "workspace": ["./member"]
      }),
    );
    fs.insert_json(root_dir().join("workspace/member/deno.json"), json!({}));
    // this one will cause issues because it's not in the workspace
    fs.insert_json(
      root_dir().join("other_dir/deno.json"),
      json!({
        "workspace": ["./member"]
      }),
    );
    fs.insert_json(root_dir().join("other_dir/member/deno.json"), json!({}));
    let err = workspace_at_start_dirs(
      &fs,
      &[
        root_dir().join("workspace/member"),
        root_dir().join("other_dir"),
      ],
    )
    .unwrap_err();
    assert_eq!(err.to_string(), normalize_err_text("Command resolved to multiple config files. Ensure all specified paths are within the same workspace.
  First: [ROOT_DIR_URL]/workspace/deno.json
  Second: [ROOT_DIR_URL]/other_dir/deno.json"));
  }

  #[test]
  fn test_specified_config_file_same_dir_discoverable_config_file() {
    let mut fs = TestFileSystem::default();
    // should not start discovering this deno.json because it
    // should search for a workspace in the parent dir
    fs.insert_json(root_dir().join("sub_dir/deno.json"), json!({}));
    let other_deno_json = root_dir().join("sub_dir/deno_other_name.json");
    fs.insert_json(&other_deno_json, json!({}));
    let workspace_dir = WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::ConfigFile(&other_deno_json),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        discover_pkg_json: true,
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(
      workspace_dir
        .workspace
        .deno_jsons()
        .map(|d| d.specifier.clone())
        .collect::<Vec<_>>(),
      vec![Url::from_file_path(&other_deno_json).unwrap()]
    );
  }

  #[test]
  fn test_split_cli_args_by_deno_json_folder() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member-a", "./member-b"],
      }),
    );
    fs.insert_json(root_dir().join("member-a/deno.json"), json!({}));
    fs.insert_json(root_dir().join("member-b/deno.json"), json!({}));
    let workspace_dir = workspace_at_start_dir(&fs, &root_dir());
    // single member
    {
      let split = workspace_dir.workspace.split_cli_args_by_deno_json_folder(
        &FilePatterns {
          base: root_dir(),
          include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
            root_dir().join("member-a"),
          )])),
          exclude: Default::default(),
        },
      );
      assert_eq!(
        split,
        IndexMap::from([(
          new_rc(
            Url::from_directory_path(root_dir().join("member-a")).unwrap()
          ),
          FilePatterns {
            base: root_dir().join("member-a"),
            include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
              root_dir().join("member-a")
            )])),
            exclude: Default::default(),
          }
        )])
      );
    }
    // root and in single member
    {
      let split = workspace_dir.workspace.split_cli_args_by_deno_json_folder(
        &FilePatterns {
          base: root_dir(),
          include: Some(PathOrPatternSet::new(vec![
            PathOrPattern::Path(root_dir().join("member-a").join("sub")),
            PathOrPattern::Path(root_dir().join("file")),
          ])),
          exclude: Default::default(),
        },
      );
      assert_eq!(
        split,
        IndexMap::from([
          (
            new_rc(
              Url::from_directory_path(root_dir().join("member-a")).unwrap()
            ),
            FilePatterns {
              base: root_dir().join("member-a/sub"),
              include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
                root_dir().join("member-a").join("sub")
              )])),
              exclude: Default::default(),
            }
          ),
          (
            new_rc(Url::from_directory_path(root_dir()).unwrap()),
            FilePatterns {
              base: root_dir().join("file"),
              include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
                root_dir().join("file")
              )])),
              exclude: Default::default(),
            }
          ),
        ])
      );
    }
    // multiple members (one with glob) and outside folder
    {
      let split = workspace_dir.workspace.split_cli_args_by_deno_json_folder(
        &FilePatterns {
          base: root_dir(),
          include: Some(PathOrPatternSet::new(vec![
            PathOrPattern::Path(root_dir().join("member-a")),
            PathOrPattern::Pattern(
              GlobPattern::from_relative(&root_dir().join("member-b"), "**/*")
                .unwrap(),
            ),
            PathOrPattern::Path(root_dir().join("other_dir")),
          ])),
          exclude: Default::default(),
        },
      );
      assert_eq!(
        split,
        IndexMap::from([
          (
            new_rc(Url::from_directory_path(root_dir()).unwrap()),
            FilePatterns {
              base: root_dir().join("other_dir"),
              include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
                root_dir().join("other_dir")
              )])),
              exclude: Default::default(),
            }
          ),
          (
            new_rc(
              Url::from_directory_path(root_dir().join("member-a")).unwrap()
            ),
            FilePatterns {
              base: root_dir().join("member-a"),
              include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
                root_dir().join("member-a")
              )])),
              exclude: Default::default(),
            }
          ),
          (
            new_rc(
              Url::from_directory_path(root_dir().join("member-b")).unwrap()
            ),
            FilePatterns {
              base: root_dir().join("member-b"),
              include: Some(PathOrPatternSet::new(vec![
                PathOrPattern::Pattern(
                  GlobPattern::from_relative(
                    &root_dir().join("member-b"),
                    "**/*"
                  )
                  .unwrap(),
                )
              ])),
              exclude: Default::default(),
            }
          ),
        ])
      );
    }
    // glob at root dir
    {
      let root_glob = PathOrPattern::Pattern(
        GlobPattern::from_relative(&root_dir(), "**/*").unwrap(),
      );
      let split = workspace_dir.workspace.split_cli_args_by_deno_json_folder(
        &FilePatterns {
          base: root_dir(),
          include: Some(PathOrPatternSet::new(vec![root_glob.clone()])),
          exclude: Default::default(),
        },
      );
      assert_eq!(
        split,
        IndexMap::from([
          (
            new_rc(Url::from_directory_path(root_dir()).unwrap()),
            FilePatterns {
              base: root_dir(),
              include: Some(PathOrPatternSet::new(vec![root_glob.clone()])),
              exclude: Default::default(),
            }
          ),
          (
            new_rc(
              Url::from_directory_path(root_dir().join("member-a")).unwrap()
            ),
            FilePatterns {
              base: root_dir().join("member-a"),
              include: Some(PathOrPatternSet::new(vec![root_glob.clone()])),
              exclude: Default::default(),
            }
          ),
          (
            new_rc(
              Url::from_directory_path(root_dir().join("member-b")).unwrap()
            ),
            FilePatterns {
              base: root_dir().join("member-b"),
              include: Some(PathOrPatternSet::new(vec![root_glob])),
              exclude: Default::default(),
            }
          ),
        ])
      );
    }
    // single path in descendant of member
    {
      let split = workspace_dir.workspace.split_cli_args_by_deno_json_folder(
        &FilePatterns {
          base: root_dir(),
          include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
            root_dir().join("member-a/sub-dir/descendant/further"),
          )])),
          exclude: Default::default(),
        },
      );
      assert_eq!(
        split,
        IndexMap::from([(
          new_rc(
            Url::from_directory_path(root_dir().join("member-a")).unwrap()
          ),
          FilePatterns {
            base: root_dir().join("member-a/sub-dir/descendant/further"),
            include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
              root_dir().join("member-a/sub-dir/descendant/further"),
            )])),
            exclude: Default::default(),
          }
        ),])
      );
    }
    // path in descendant of member then second path that goes to a parent folder
    {
      let split = workspace_dir.workspace.split_cli_args_by_deno_json_folder(
        &FilePatterns {
          base: root_dir(),
          include: Some(PathOrPatternSet::new(vec![
            PathOrPattern::Path(
              root_dir().join("member-a/sub-dir/descendant/further"),
            ),
            PathOrPattern::Path(root_dir().join("member-a/sub-dir/other")),
          ])),
          exclude: Default::default(),
        },
      );
      assert_eq!(
        split,
        IndexMap::from([(
          new_rc(
            Url::from_directory_path(root_dir().join("member-a")).unwrap()
          ),
          FilePatterns {
            // should use common base here
            base: root_dir().join("member-a/sub-dir"),
            include: Some(PathOrPatternSet::new(vec![
              PathOrPattern::Path(
                root_dir().join("member-a/sub-dir/descendant/further"),
              ),
              PathOrPattern::Path(root_dir().join("member-a/sub-dir/other"),)
            ])),
            exclude: Default::default(),
          }
        )])
      );
    }
    // path outside the root directory
    {
      let dir_outside = normalize_path(root_dir().join("../dir_outside"));
      let split = workspace_dir.workspace.split_cli_args_by_deno_json_folder(
        &FilePatterns {
          base: root_dir(),
          include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
            dir_outside.clone(),
          )])),
          exclude: Default::default(),
        },
      );
      assert_eq!(
        split,
        IndexMap::from([(
          new_rc(Url::from_directory_path(root_dir()).unwrap()),
          FilePatterns {
            base: root_dir(),
            include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
              dir_outside.clone(),
            ),])),
            exclude: Default::default(),
          }
        )])
      );
    }
    // multiple paths outside the root directory
    {
      let dir_outside_1 = normalize_path(root_dir().join("../dir_outside_1"));
      let dir_outside_2 = normalize_path(root_dir().join("../dir_outside_2"));
      let split = workspace_dir.workspace.split_cli_args_by_deno_json_folder(
        &FilePatterns {
          base: root_dir(),
          include: Some(PathOrPatternSet::new(vec![
            PathOrPattern::Path(dir_outside_1.clone()),
            PathOrPattern::Path(dir_outside_2.clone()),
          ])),
          exclude: Default::default(),
        },
      );
      assert_eq!(
        split,
        IndexMap::from([(
          new_rc(Url::from_directory_path(root_dir()).unwrap()),
          FilePatterns {
            base: root_dir(),
            include: Some(PathOrPatternSet::new(vec![
              PathOrPattern::Path(dir_outside_1.clone()),
              PathOrPattern::Path(dir_outside_2.clone()),
            ])),
            exclude: Default::default(),
          }
        )])
      );
    }
  }

  #[test]
  fn test_split_cli_args_by_deno_json_folder_no_config() {
    let mut fs = TestFileSystem::default();
    fs.insert(root_dir().join("path"), ""); // create the root directory
    let workspace_dir = workspace_at_start_dir(&fs, &root_dir());
    // two paths, looped to ensure that the order is maintained on
    // the output and not sorted
    let path1 = normalize_path(root_dir().join("./path-longer"));
    let path2 = normalize_path(root_dir().join("./path"));
    for (path1, path2) in [(&path1, &path2), (&path2, &path1)] {
      let split = workspace_dir.workspace.split_cli_args_by_deno_json_folder(
        &FilePatterns {
          base: root_dir(),
          include: Some(PathOrPatternSet::new(vec![
            PathOrPattern::Path(path1.clone()),
            PathOrPattern::Path(path2.clone()),
          ])),
          exclude: Default::default(),
        },
      );
      assert_eq!(
        split,
        IndexMap::from([(
          new_rc(Url::from_directory_path(root_dir()).unwrap()),
          FilePatterns {
            base: root_dir(),
            include: Some(PathOrPatternSet::new(vec![
              PathOrPattern::Path(path1.clone()),
              PathOrPattern::Path(path2.clone()),
            ])),
            exclude: Default::default(),
          }
        )])
      );
    }
  }

  #[test]
  fn test_resolve_config_for_members_include_root_and_sub_member() {
    fn run_test(
      config_key: &str,
      workspace_to_file_patterns: impl Fn(&WorkspaceDirectory) -> Vec<FilePatterns>,
    ) {
      let mut fs = TestFileSystem::default();
      fs.insert_json(
        root_dir().join("deno.json"),
        json!({
          "workspace": ["./member-a", "./member-b", "member-c"],
          config_key: {
            "include": ["./file.ts", "./member-c/file.ts"]
          }
        }),
      );
      fs.insert_json(
        root_dir().join("member-a/deno.json"),
        json!({
          config_key: {
            "include": ["./member-a-file.ts"]
          }
        }),
      );
      fs.insert_json(root_dir().join("member-b/deno.json"), json!({}));
      fs.insert_json(root_dir().join("member-c/deno.json"), json!({}));
      let workspace = workspace_at_start_dir(&fs, &root_dir());
      assert_eq!(
        workspace_to_file_patterns(&workspace),
        vec![
          FilePatterns {
            base: root_dir(),
            include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
              root_dir().join("file.ts")
            )])),
            exclude: PathOrPatternSet::new(vec![
              PathOrPattern::Path(root_dir().join("member-a")),
              PathOrPattern::Path(root_dir().join("member-b")),
              PathOrPattern::Path(root_dir().join("member-c")),
            ])
          },
          FilePatterns {
            base: root_dir().join("member-a"),
            include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
              root_dir().join("member-a").join("member-a-file.ts")
            )])),
            exclude: Default::default(),
          },
          FilePatterns {
            base: root_dir().join("member-b"),
            include: None,
            exclude: Default::default(),
          },
          FilePatterns {
            base: root_dir().join("member-c"),
            include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
              root_dir().join("member-c").join("file.ts")
            )])),
            exclude: Default::default(),
          }
        ]
      );
    }

    run_test("bench", |workspace_dir| {
      let config_for_members = workspace_dir
        .workspace
        .resolve_bench_config_for_members(&FilePatterns::new_with_base(
          root_dir(),
        ))
        .unwrap();
      config_for_members
        .into_iter()
        .map(|(_ctx, config)| config.files)
        .collect::<Vec<_>>()
    });

    run_test("fmt", |workspace_dir| {
      let config_for_members = workspace_dir
        .workspace
        .resolve_fmt_config_for_members(
          &FilePatterns::new_with_base(root_dir()),
        )
        .unwrap();
      config_for_members
        .into_iter()
        .map(|(_ctx, config)| config.files)
        .collect::<Vec<_>>()
    });

    run_test("lint", |workspace_dir| {
      let config_for_members = workspace_dir
        .workspace
        .resolve_lint_config_for_members(&FilePatterns::new_with_base(
          root_dir(),
        ))
        .unwrap();
      config_for_members
        .into_iter()
        .map(|(_ctx, config)| config.files)
        .collect::<Vec<_>>()
    });

    run_test("test", |workspace_dir| {
      let config_for_members = workspace_dir
        .workspace
        .resolve_test_config_for_members(&FilePatterns::new_with_base(
          root_dir(),
        ))
        .unwrap();
      config_for_members
        .into_iter()
        .map(|(_ctx, config)| config.files)
        .collect::<Vec<_>>()
    });
  }

  #[test]
  fn test_resolve_config_for_members_excluded_member() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member-a", "./member-b"],
        "lint": {
          "exclude": ["./member-a"]
        }
      }),
    );
    fs.insert_json(root_dir().join("member-a/deno.json"), json!({}));
    fs.insert_json(root_dir().join("member-b/deno.json"), json!({}));
    let workspace_dir = workspace_at_start_dir(&fs, &root_dir());
    let config_for_members = workspace_dir
      .workspace
      .resolve_lint_config_for_members(&FilePatterns::new_with_base(root_dir()))
      .unwrap();
    let mut file_patterns = config_for_members
      .into_iter()
      .map(|(_ctx, config)| config.files)
      .collect::<Vec<_>>();
    assert_eq!(
      file_patterns,
      vec![
        FilePatterns {
          base: root_dir(),
          include: None,
          exclude: PathOrPatternSet::new(vec![
            PathOrPattern::Path(root_dir().join("member-a")),
            // It will be in here twice because it's excluded from being
            // traversed for this set of FilePatterns and also it's excluded
            // in the "exclude". This is not a big deal because it's an edge
            // case and the end behaviour is the same. It's probably not worth
            // the complexity and perf to ensure only unique items are in here
            PathOrPattern::Path(root_dir().join("member-a")),
            PathOrPattern::Path(root_dir().join("member-b")),
          ])
        },
        // This item is effectively a no-op as it excludes itself.
        // It would be nice to have this not even included as a member,
        // but doing that in a maintainable way would require a bit of
        // refactoring to get resolve_config_for_members to understand
        // that configs return FilePatterns.
        FilePatterns {
          base: root_dir().join("member-a"),
          include: None,
          exclude: PathOrPatternSet::new(vec![PathOrPattern::Path(
            root_dir().join("member-a")
          ),]),
        },
        FilePatterns {
          base: root_dir().join("member-b"),
          include: None,
          exclude: Default::default(),
        },
      ]
    );

    // ensure the second file patterns is a no-op
    fs.insert(root_dir().join("member-a/file.ts"), "");
    fs.insert(root_dir().join("member-a/sub-dir/file.ts"), "");
    let files = FileCollector::new(|_| true)
      .collect_file_patterns(&fs, file_patterns.remove(1))
      .unwrap();
    assert!(files.is_empty());
  }

  #[test]
  fn test_resolve_config_for_members_excluded_member_unexcluded_sub_dir() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member-a"],
        "lint": {
          "exclude": ["./member-a"]
        }
      }),
    );
    fs.insert_json(
      root_dir().join("member-a/deno.json"),
      json!({
        "lint": {
          // unexclude this sub dir so it's linted
          "exclude": ["!./sub-dir"]
        }
      }),
    );
    let workspace_dir = workspace_at_start_dir(&fs, &root_dir());
    let config_for_members = workspace_dir
      .workspace
      .resolve_lint_config_for_members(&FilePatterns::new_with_base(root_dir()))
      .unwrap();
    let mut file_patterns = config_for_members
      .into_iter()
      .map(|(_ctx, config)| config.files)
      .collect::<Vec<_>>();
    assert_eq!(
      file_patterns,
      vec![
        FilePatterns {
          base: root_dir(),
          include: None,
          exclude: PathOrPatternSet::new(vec![
            PathOrPattern::Path(root_dir().join("member-a")),
            // see note in previous test about this being here twice
            PathOrPattern::Path(root_dir().join("member-a")),
          ])
        },
        FilePatterns {
          base: root_dir().join("member-a"),
          include: None,
          exclude: PathOrPatternSet::new(vec![
            // self will be excluded, but then sub dir will be unexcluded
            PathOrPattern::Path(root_dir().join("member-a")),
            PathOrPattern::NegatedPath(
              root_dir().join("member-a").join("sub-dir")
            ),
          ]),
        },
      ]
    );
    fs.insert(root_dir().join("member-a/file.ts"), "");
    fs.insert(root_dir().join("member-a/sub-dir/file.ts"), "");
    let files = FileCollector::new(|_| true)
      .collect_file_patterns(&fs, file_patterns.remove(1))
      .unwrap();
    // should only have member-a/sub-dir/file.ts and not member-a/file.ts
    assert_eq!(files, vec![root_dir().join("member-a/sub-dir/file.ts")]);
  }

  #[test]
  fn test_lock_path() {
    let workspace_dir = workspace_for_root_and_member(
      json!({
        "lock": "other.lock",
      }),
      json!({}),
    );
    assert_eq!(
      workspace_dir.workspace.resolve_lockfile_path().unwrap(),
      Some(root_dir().join("other.lock"))
    );
  }

  #[derive(Default)]
  struct DenoJsonMemCache(RefCell<HashMap<PathBuf, ConfigFileRc>>);

  impl DenoJsonCache for DenoJsonMemCache {
    fn get(&self, path: &Path) -> Option<ConfigFileRc> {
      self.0.borrow().get(path).cloned()
    }

    fn set(&self, path: PathBuf, deno_json: ConfigFileRc) {
      self.0.borrow_mut().insert(path, deno_json);
    }
  }

  #[derive(Default)]
  struct PkgJsonMemCache(RefCell<HashMap<PathBuf, PackageJsonRc>>);

  impl deno_package_json::PackageJsonCache for PkgJsonMemCache {
    fn get(&self, path: &Path) -> Option<PackageJsonRc> {
      self.0.borrow().get(path).cloned()
    }

    fn set(&self, path: PathBuf, value: PackageJsonRc) {
      self.0.borrow_mut().insert(path, value);
    }
  }

  #[derive(Default)]
  struct WorkspaceMemCache(RefCell<HashMap<PathBuf, WorkspaceRc>>);

  impl WorkspaceCache for WorkspaceMemCache {
    fn get(&self, dir_path: &Path) -> Option<WorkspaceRc> {
      self.0.borrow().get(dir_path).cloned()
    }

    fn set(&self, dir_path: PathBuf, workspace: WorkspaceRc) {
      self.0.borrow_mut().insert(dir_path, workspace);
    }
  }

  #[test]
  fn workspace_discovery_deno_json_cache() {
    let mut fs = TestFileSystem::default();
    fs.insert(root_dir().join("deno.json"), "{ \"nodeModulesDir\": true }");
    let cache = DenoJsonMemCache::default();
    let workspace_dir = WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::Paths(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        discover_pkg_json: true,
        deno_json_cache: Some(&cache),
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(cache.0.borrow().len(), 1); // writes to the cache
    assert_eq!(workspace_dir.workspace.node_modules_dir(), Some(true));
    let new_config_file = ConfigFile::new(
      r#"{ "nodeModulesDir": false }"#,
      Url::from_file_path(root_dir().join("deno.json")).unwrap(),
      &Default::default(),
    )
    .unwrap();
    cache
      .0
      .borrow_mut()
      .insert(root_dir().join("deno.json"), new_rc(new_config_file));
    let workspace_dir = WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::Paths(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        discover_pkg_json: true,
        deno_json_cache: Some(&cache),
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(workspace_dir.workspace.node_modules_dir(), Some(false)); // reads from the cache
  }

  #[test]
  fn workspace_discovery_pkg_json_cache() {
    let mut fs = TestFileSystem::default();
    fs.insert(root_dir().join("package.json"), "{ \"name\": \"member\" }");
    let cache = PkgJsonMemCache::default();
    let workspace_dir = WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::Paths(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        discover_pkg_json: true,
        pkg_json_cache: Some(&cache),
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(cache.0.borrow().len(), 1); // writes to the cache
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 1);
    let new_pkg_json = PackageJson::load_from_string(
      root_dir().join("package.json"),
      r#"{ "name": "cached-name" }"#.to_string(),
    )
    .unwrap();
    cache
      .0
      .borrow_mut()
      .insert(root_dir().join("package.json"), new_rc(new_pkg_json));
    let workspace_dir = WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::Paths(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        discover_pkg_json: true,
        pkg_json_cache: Some(&cache),
        ..Default::default()
      },
    )
    .unwrap();
    // reads from the cache
    assert_eq!(
      workspace_dir
        .workspace
        .package_jsons()
        .map(|p| p.name.as_deref().unwrap())
        .collect::<Vec<_>>(),
      vec!["cached-name"]
    );
  }

  #[test]
  fn workspace_discovery_workspace_cache() {
    let mut fs = TestFileSystem::default();
    fs.insert(
      root_dir().join("member/package-a/package.json"),
      r#"{ "name": "member-a" }"#,
    );
    fs.insert(
      root_dir().join("member/package-b/deno.json"),
      r#"{ "name": "member-b" }"#,
    );
    fs.insert(
      root_dir().join("deno.json"),
      r#"{ "workspace": ["member/package-a", "member/package-b"] }"#,
    );
    let deno_json_cache = DenoJsonMemCache::default();
    let pkg_json_cache = PkgJsonMemCache::default();
    let workspace_cache = WorkspaceMemCache::default();
    let workspace_dir = WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::Paths(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        discover_pkg_json: true,
        deno_json_cache: Some(&deno_json_cache),
        pkg_json_cache: Some(&pkg_json_cache),
        workspace_cache: Some(&workspace_cache),
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 1);
    // writes to the caches
    assert_eq!(pkg_json_cache.0.borrow().len(), 1);
    assert_eq!(deno_json_cache.0.borrow().len(), 2);
    assert_eq!(workspace_cache.0.borrow().len(), 1);
    // now delete from the deno json and pkg json caches
    deno_json_cache.0.borrow_mut().clear();
    pkg_json_cache.0.borrow_mut().clear();
    // should load and not write to the caches
    let workspace_dir = WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::Paths(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        discover_pkg_json: true,
        deno_json_cache: Some(&deno_json_cache),
        pkg_json_cache: Some(&pkg_json_cache),
        workspace_cache: Some(&workspace_cache),
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(workspace_dir.workspace.package_jsons().count(), 1);
    assert_eq!(workspace_dir.workspace.deno_jsons().count(), 2);
    // it wouldn't have written to these because it just
    // loads from the workspace cache
    assert_eq!(pkg_json_cache.0.borrow().len(), 0);
    assert_eq!(deno_json_cache.0.borrow().len(), 0);
  }

  #[test]
  fn deno_workspace_discovery_workspace_cache() {
    let mut fs = TestFileSystem::default();
    fs.insert(
      root_dir().join("member/package-a/deno.json"),
      r#"{ "name": "member-a" }"#,
    );
    fs.insert(
      root_dir().join("member/package-b/deno.json"),
      r#"{ "name": "member-b" }"#,
    );
    fs.insert(
      root_dir().join("deno.json"),
      r#"{ "workspace": ["member/package-a", "member/package-b"] }"#,
    );
    let deno_json_cache = DenoJsonMemCache::default();
    let pkg_json_cache = PkgJsonMemCache::default();
    let workspace_cache = WorkspaceMemCache::default();
    for start_dir in [
      root_dir(),
      root_dir().join("member/package-a"),
      root_dir().join("member/package-b"),
    ] {
      let workspace_dir = WorkspaceDirectory::discover(
        WorkspaceDiscoverStart::Paths(&[start_dir]),
        &WorkspaceDiscoverOptions {
          fs: &fs,
          discover_pkg_json: true,
          deno_json_cache: Some(&deno_json_cache),
          pkg_json_cache: Some(&pkg_json_cache),
          workspace_cache: Some(&workspace_cache),
          ..Default::default()
        },
      )
      .unwrap();
      assert_eq!(workspace_dir.workspace.deno_jsons().count(), 3);
    }
  }

  #[test]
  fn npm_workspace_discovery_workspace_cache() {
    let mut fs = TestFileSystem::default();
    fs.insert(
      root_dir().join("member/package-a/package.json"),
      r#"{ "name": "member-a" }"#,
    );
    fs.insert(
      root_dir().join("member/package-b/package.json"),
      r#"{ "name": "member-b" }"#,
    );
    fs.insert(
      root_dir().join("package.json"),
      r#"{ "workspaces": ["member/*"] }"#,
    );
    let deno_json_cache = DenoJsonMemCache::default();
    let pkg_json_cache = PkgJsonMemCache::default();
    let workspace_cache = WorkspaceMemCache::default();
    for start_dir in [
      root_dir(),
      root_dir().join("member/package-a"),
      root_dir().join("member/package-b"),
    ] {
      let workspace_dir = WorkspaceDirectory::discover(
        WorkspaceDiscoverStart::Paths(&[start_dir]),
        &WorkspaceDiscoverOptions {
          fs: &fs,
          discover_pkg_json: true,
          deno_json_cache: Some(&deno_json_cache),
          pkg_json_cache: Some(&pkg_json_cache),
          workspace_cache: Some(&workspace_cache),
          ..Default::default()
        },
      )
      .unwrap();
      assert_eq!(workspace_dir.workspace.package_jsons().count(), 3);
    }
  }

  fn workspace_for_root_and_member(
    root: serde_json::Value,
    member: serde_json::Value,
  ) -> WorkspaceDirectory {
    workspace_for_root_and_member_with_fs(root, member, |_| {})
  }

  fn workspace_for_root_and_member_with_fs(
    mut root: serde_json::Value,
    member: serde_json::Value,
    with_fs: impl FnOnce(&mut TestFileSystem),
  ) -> WorkspaceDirectory {
    root
      .as_object_mut()
      .unwrap()
      .insert("workspace".to_string(), json!(["./member"]));
    let mut fs = TestFileSystem::default();
    fs.insert_json(root_dir().join("deno.json"), root);
    fs.insert_json(root_dir().join("member/deno.json"), member);
    with_fs(&mut fs);
    // start in the member
    workspace_at_start_dir(&fs, &root_dir().join("member"))
  }

  fn workspace_at_start_dir(
    fs: &TestFileSystem,
    start_dir: &Path,
  ) -> WorkspaceDirectory {
    workspace_at_start_dir_result(fs, start_dir).unwrap()
  }

  fn workspace_at_start_dir_err(
    fs: &TestFileSystem,
    start_dir: &Path,
  ) -> WorkspaceDiscoverError {
    workspace_at_start_dir_result(fs, start_dir).unwrap_err()
  }

  fn workspace_at_start_dir_result(
    fs: &TestFileSystem,
    start_dir: &Path,
  ) -> Result<WorkspaceDirectory, WorkspaceDiscoverError> {
    workspace_at_start_dirs(fs, &[start_dir.to_path_buf()])
  }

  fn workspace_at_start_dirs(
    fs: &TestFileSystem,
    start_dirs: &[PathBuf],
  ) -> Result<WorkspaceDirectory, WorkspaceDiscoverError> {
    WorkspaceDirectory::discover(
      WorkspaceDiscoverStart::Paths(start_dirs),
      &WorkspaceDiscoverOptions {
        fs,
        discover_pkg_json: true,
        ..Default::default()
      },
    )
  }

  fn normalize_err_text(text: &str) -> String {
    text.replace(
      "[ROOT_DIR_URL]",
      Url::from_directory_path(root_dir())
        .unwrap()
        .to_string()
        .trim_end_matches('/'),
    )
  }
}
