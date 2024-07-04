// Copyright 2018-2024 the Deno authors. MIT license.

use std::borrow::Cow;
use std::collections::HashSet;
use std::future::Future;
use std::path::Path;
use std::path::PathBuf;

use anyhow::bail;
use anyhow::Context;
use anyhow::Error as AnyError;
use deno_semver::package::PackageNv;
use deno_semver::package::PackageReq;
use deno_semver::RangeSetOrTag;
use deno_semver::VersionReq;
use discovery::discover_workspace_config_files;
use discovery::ConfigFileDiscovery;
use discovery::ConfigFolder;
use discovery::DenoOrPkgJson;
use indexmap::IndexMap;
use thiserror::Error;
use url::Url;

use crate::deno_json::ConfigFile;
use crate::deno_json::ConfigFileReadError;
use crate::deno_json::ConfigParseOptions;
use crate::get_ts_config_for_emit;
use crate::glob::FilePatterns;
use crate::glob::PathKind;
use crate::glob::PathOrPattern;
use crate::glob::PathOrPatternSet;
use crate::package_json::PackageJson;
use crate::package_json::PackageJsonLoadError;
use crate::package_json::PackageJsonRc;
use crate::sync::new_rc;
use crate::util::CheckedSet;
use crate::BenchConfig;
use crate::ConfigFileRc;
use crate::FmtConfig;
use crate::FmtOptionsConfig;
use crate::IgnoredCompilerOptions;
use crate::JsxImportSourceConfig;
use crate::LintConfig;
use crate::LintRulesConfig;
use crate::LockConfig;
use crate::PublishConfig;
use crate::SpecifierToFilePathError;
use crate::Task;
use crate::TestConfig;
use crate::TsConfigForEmit;
use crate::TsConfigType;
use crate::WorkspaceLintConfig;

mod discovery;
mod resolver;

pub use resolver::CreateResolverOptions;
pub use resolver::MappedResolution;
pub use resolver::MappedResolutionError;
pub use resolver::PackageJsonDepResolution;
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
  pub member_ctx: WorkspaceMemberContext,
  pub config_file: ConfigFileRc,
}

#[derive(Debug, Clone)]
pub struct NpmPackageConfig {
  pub nv: PackageNv,
  pub member_ctx: WorkspaceMemberContext,
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

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum WorkspaceDiagnosticKind {
  #[error("The \"{0}\" field can only be specified in the root workspace deno.json file.")]
  RootOnlyOption(&'static str),
  #[error("The \"{0}\" field can only be specified in a workspace member deno.json file and not the root workspace file.")]
  MemberOnlyOption(&'static str),
  #[error("The \"workspaces\" field was ignored. Use \"workspace\" instead.")]
  InvalidWorkspacesOption,
  #[error(
    "The \"exports\" field should be specified when specifying a \"name\"."
  )]
  MissingExports,
}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[error("{}\n    at {}", .kind, .config_url)]
pub struct WorkspaceDiagnostic {
  pub kind: WorkspaceDiagnosticKind,
  pub config_url: Url,
}

#[derive(Debug, Error)]
pub enum ResolveWorkspaceMemberError {
  #[error("Could not find config file for workspace member in '{}'.", .dir_url)]
  NotFound { dir_url: Url },
  #[error("Could not find package.json for workspace member in '{}'.", .dir_url)]
  NotFoundPackageJson { dir_url: Url },
  #[error("Could not find config file for workspace member in '{}'. Ensure you specify the directory and not the configuration file in the workspace member.", .dir_url)]
  NotFoundMaybeSpecifiedFile { dir_url: Url },
  #[error(transparent)]
  ConfigReadError(#[from] ConfigFileReadError),
  #[error(transparent)]
  PackageJsonReadError(#[from] PackageJsonLoadError),
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
  ConfigRead(#[from] ConfigFileReadError),
  #[error(transparent)]
  PackageJsonReadError(#[from] PackageJsonLoadError),
  #[error("Workspace members cannot be empty.\n  Workspace: {0}")]
  MembersEmpty(Url),
  #[error(transparent)]
  ResolveMember(#[from] ResolveWorkspaceMemberError),
  #[error("Command resolved to multiple config files. Ensure all specified paths are within the same workspace.\n  First: {base_workspace_url}\n  Second: {other_workspace_url}")]
  MultipleWorkspaces {
    base_workspace_url: Url,
    other_workspace_url: Url,
  },
  #[error(transparent)]
  SpecifierToFilePath(#[from] SpecifierToFilePathError),
  #[error("Config file must be a member of the workspace.\n  Config: {config_url}\n  Workspace: {workspace_url}")]
  ConfigNotWorkspaceMember { workspace_url: Url, config_url: Url },
}

#[derive(Debug, Clone, Copy)]
pub enum WorkspaceDiscoverStart<'a> {
  Dirs(&'a [PathBuf]),
  ConfigFile(&'a Path),
}

#[derive(Default)]
pub struct WorkspaceDiscoverOptions<'a> {
  pub fs: &'a dyn crate::fs::DenoConfigFs,
  pub pkg_json_cache: Option<&'a dyn crate::package_json::PackageJsonCache>,
  pub config_parse_options: ConfigParseOptions,
  pub additional_config_file_names: &'a [&'a str],
  pub discover_pkg_json: bool,
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
  /// The directory the user started the workspace discovery from.
  start_dir: UrlRc,
  config_folders: IndexMap<UrlRc, FolderConfigs>,
}

impl Workspace {
  pub fn empty(root_dir: UrlRc) -> Self {
    Workspace {
      config_folders: IndexMap::from([(
        root_dir.clone(),
        FolderConfigs::default(),
      )]),
      start_dir: root_dir.clone(),
      root_dir,
    }
  }

  pub fn discover(
    start: WorkspaceDiscoverStart,
    opts: &WorkspaceDiscoverOptions,
  ) -> Result<Self, WorkspaceDiscoverError> {
    fn resolve_start_dir(
      start: &WorkspaceDiscoverStart,
    ) -> Result<Url, WorkspaceDiscoverError> {
      match start {
        WorkspaceDiscoverStart::Dirs(dirs) => {
          if dirs.is_empty() {
            Err(
              WorkspaceDiscoverErrorKind::FailedResolvingStartDirectory(
                anyhow::anyhow!("No directories provided."),
              )
              .into(),
            )
          } else {
            // just select the first one... this doesn't matter too much
            // at the moment because we only use this for lint and fmt,
            // so this is ok for now
            Ok(Url::from_directory_path(&dirs[0]).unwrap())
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

    let start_dir = new_rc(resolve_start_dir(&start)?);
    let config_file_discovery = discover_workspace_config_files(start, opts)?;

    let workspace = match config_file_discovery {
      ConfigFileDiscovery::None => Workspace {
        config_folders: IndexMap::from([(
          start_dir.clone(),
          FolderConfigs::default(),
        )]),
        root_dir: start_dir.clone(),
        start_dir,
      },
      ConfigFileDiscovery::Single(config_folder) => {
        let root_dir = new_rc(config_folder.folder_url());
        Workspace {
          config_folders: IndexMap::from([(
            root_dir.clone(),
            FolderConfigs::from_config_folder(config_folder),
          )]),
          start_dir,
          root_dir,
        }
      }
      ConfigFileDiscovery::Workspace { root, members } => {
        let root_dir = new_rc(root.folder_url());
        let mut config_folders = members
          .into_iter()
          .map(|(folder_url, config_folder)| {
            (folder_url, FolderConfigs::from_config_folder(config_folder))
          })
          .collect::<IndexMap<_, _>>();
        config_folders
          .insert(root_dir.clone(), FolderConfigs::from_config_folder(root));
        Workspace {
          root_dir,
          start_dir,
          config_folders,
        }
      }
    };
    debug_assert!(
      workspace.config_folders.contains_key(&workspace.root_dir),
      "root should always have a folder"
    );
    Ok(workspace)
  }

  pub async fn create_resolver<
    TReturn: Future<Output = Result<String, AnyError>>,
  >(
    &self,
    options: CreateResolverOptions,
    fetch_text: impl Fn(&Url) -> TReturn,
  ) -> Result<WorkspaceResolver, WorkspaceResolverCreateError> {
    WorkspaceResolver::from_workspace(self, options, fetch_text).await
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
    }

    let mut diagnostics = Vec::new();
    let root_deno_json = self.root_folder().1.deno_json.as_ref();
    let is_deno_workspace = root_deno_json
      .map(|d| d.json.workspace.is_some())
      .unwrap_or(false);
    for (url, folder) in &self.config_folders {
      if let Some(config) = &folder.deno_json {
        let is_root = url == &self.root_dir;
        if is_deno_workspace && !is_root {
          check_member_diagnostics(config, &mut diagnostics);
        }

        check_all_configs(config, &mut diagnostics);
      }
    }
    diagnostics
  }

  /// Resolves the `WorkspaceMemberContext` from the directory that workspace discovery
  /// started from.
  pub fn resolve_start_ctx(self: &WorkspaceRc) -> WorkspaceMemberContext {
    self.resolve_member_ctx(&self.start_dir)
  }

  /// Resolves a workspace member's context, which can be used for deriving
  /// configuration specific to a member.
  pub fn resolve_member_ctx(
    self: &WorkspaceRc,
    specifier: &Url,
  ) -> WorkspaceMemberContext {
    let maybe_folder = self.resolve_folder(specifier);
    match maybe_folder {
      Some((member_url, folder)) => {
        if member_url == &self.root_dir {
          WorkspaceMemberContext::create_from_root_folder(
            self.clone(),
            self.root_dir.clone(),
            folder,
          )
        } else {
          let maybe_deno_json = folder
            .deno_json
            .as_ref()
            .map(|c| (member_url, c))
            .or_else(|| {
              let parent = parent_specifier_str(member_url.as_str())?;
              self.resolve_deno_json_from_str(parent)
            })
            .or_else(|| {
              let root = self.config_folders.get(&self.root_dir).unwrap();
              root.deno_json.as_ref().map(|c| (&self.root_dir, c))
            });
          let maybe_pkg_json = folder
            .pkg_json
            .as_ref()
            .map(|pkg_json| (member_url, pkg_json))
            .or_else(|| {
              let parent = parent_specifier_str(member_url.as_str())?;
              self.resolve_pkg_json_from_str(parent)
            })
            .or_else(|| {
              let root = self.config_folders.get(&self.root_dir).unwrap();
              root.pkg_json.as_ref().map(|c| (&self.root_dir, c))
            });
          WorkspaceMemberContext {
            workspace: self.clone(),
            dir_url: member_url.clone(),
            pkg_json: maybe_pkg_json.map(|(member_url, pkg_json)| {
              WorkspaceMemberContextConfig {
                root: if self.root_dir == *member_url {
                  None
                } else {
                  self
                    .config_folders
                    .get(&self.root_dir)
                    .unwrap()
                    .pkg_json
                    .clone()
                },
                member: pkg_json.clone(),
              }
            }),
            deno_json: maybe_deno_json.map(|(member_url, config)| {
              WorkspaceMemberContextConfig {
                root: if self.root_dir == *member_url {
                  None
                } else {
                  self
                    .config_folders
                    .get(&self.root_dir)
                    .unwrap()
                    .deno_json
                    .clone()
                },
                member: config.clone(),
              }
            }),
          }
        }
      }
      None => {
        let root = self.config_folders.get(&self.root_dir).unwrap();
        WorkspaceMemberContext::create_from_root_folder(
          self.clone(),
          self.root_dir.clone(),
          root,
        )
      }
    }
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

  pub fn jsr_packages(self: &WorkspaceRc) -> Vec<JsrPackageConfig> {
    self
      .deno_jsons()
      .filter_map(|c| {
        if !c.is_package() {
          return None;
        }
        Some(JsrPackageConfig {
          member_ctx: self.resolve_member_ctx(&c.specifier),
          name: c.json.name.clone()?,
          config_file: c.clone(),
        })
      })
      .collect()
  }

  pub fn jsr_packages_for_publish(self: &WorkspaceRc) -> Vec<JsrPackageConfig> {
    let ctx = self.resolve_start_ctx();
    let Some(config) = &ctx.deno_json else {
      return Vec::new();
    };
    let deno_json = &config.member;
    if let Some(pkg_json) = &ctx.pkg_json {
      // don't publish anything if in a package.json only directory within
      // a workspace
      if pkg_json.member.dir_path().starts_with(deno_json.dir_path())
        && deno_json.dir_path() != pkg_json.member.dir_path()
      {
        return Vec::new();
      }
    }
    if deno_json.dir_path() == self.root_dir.to_file_path().unwrap()
      && !(deno_json.is_workspace() && deno_json.is_package())
    {
      return self.jsr_packages();
    }
    match ctx.maybe_package_config() {
      Some(pkg) => vec![pkg],
      None => Vec::new(),
    }
  }

  pub fn npm_packages(self: &WorkspaceRc) -> Vec<NpmPackageConfig> {
    self
      .package_jsons()
      .filter_map(|c| {
        Some(NpmPackageConfig {
          member_ctx: self.resolve_member_ctx(&c.specifier()),
          nv: PackageNv {
            name: c.name.clone()?,
            version: {
              let version = c.version.as_ref()?;
              deno_semver::Version::parse_from_npm(version).ok()?
            },
          },
          pkg_json: c.clone(),
        })
      })
      .collect()
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

  pub fn root_folder(&self) -> (&UrlRc, &FolderConfigs) {
    (
      &self.root_dir,
      self.config_folders.get(&self.root_dir).unwrap(),
    )
  }

  pub fn config_folders(&self) -> &IndexMap<UrlRc, FolderConfigs> {
    &self.config_folders
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

  pub fn vendor_dir_path(&self) -> Option<PathBuf> {
    self
      .with_root_config_only(|root_config| root_config.vendor_dir_path())
      .unwrap_or(None)
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
      self.root_folder().1.deno_json.as_deref(),
    )
  }

  pub fn to_import_map_specifier(&self) -> Result<Option<Url>, AnyError> {
    self
      .with_root_config_only(|root_config| {
        root_config.to_import_map_specifier()
      })
      .unwrap_or(Ok(None))
  }

  pub fn to_lock_config(&self) -> Result<Option<LockConfig>, AnyError> {
    self
      .with_root_config_only(|root_config| root_config.to_lock_config())
      .unwrap_or(Ok(None))
  }

  pub fn to_maybe_imports(&self) -> Result<Vec<(Url, Vec<String>)>, AnyError> {
    self
      .with_root_config_only(|root_config| root_config.to_maybe_imports())
      .unwrap_or(Ok(Vec::new()))
  }

  pub fn to_maybe_jsx_import_source_config(
    &self,
  ) -> Result<Option<JsxImportSourceConfig>, AnyError> {
    self
      .with_root_config_only(|root_config| {
        root_config.to_maybe_jsx_import_source_config()
      })
      .unwrap_or(Ok(None))
  }

  pub fn resolve_ctxs_from_patterns(
    self: &WorkspaceRc,
    patterns: &FilePatterns,
  ) -> Vec<WorkspaceMemberContext> {
    let context = self.resolve_start_ctx();
    let mut ctxs = Vec::with_capacity(self.config_folders.len());
    ctxs.push(context);

    // sub configs
    for (dir_url, folder) in self.config_folders.iter() {
      let config = match &folder.deno_json {
        Some(c) => c,
        None => continue,
      };
      if *dir_url != self.start_dir
        && dir_url.as_str().starts_with(self.start_dir.as_str())
        && patterns.matches_path(&config.dir_path(), PathKind::Directory)
      {
        let member_ctx = self.resolve_member_ctx(dir_url);
        ctxs.push(member_ctx);
      }
    }

    ctxs
  }

  pub fn resolve_config_excludes(&self) -> Result<PathOrPatternSet, AnyError> {
    // have the root excludes at the front because they're lower priority
    let mut excludes = match &self.root_folder().1.deno_json {
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
      .root_folder()
      .1
      .deno_json
      .as_ref()
      .map(|c| (&c.json.unstable) as &[String])
      .unwrap_or(&[])
  }

  pub fn has_unstable(&self, name: &str) -> bool {
    self
      .root_folder()
      .1
      .deno_json
      .as_ref()
      .map(|c| c.has_unstable(name))
      .unwrap_or(false)
  }

  fn with_root_config_only<R>(
    &self,
    with_root: impl Fn(&ConfigFile) -> R,
  ) -> Option<R> {
    let configs = self.config_folders.get(&self.root_dir).unwrap();
    configs.deno_json.as_ref().map(|c| with_root(c))
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

#[derive(Debug, Clone)]
struct WorkspaceMemberContextConfig<T> {
  #[allow(clippy::disallowed_types)]
  member: crate::sync::MaybeArc<T>,
  // will be None when it doesn't exist or the member config
  // is the root config
  #[allow(clippy::disallowed_types)]
  root: Option<crate::sync::MaybeArc<T>>,
}

#[derive(Debug, Clone)]
pub struct WorkspaceMemberContext {
  workspace: WorkspaceRc,
  dir_url: UrlRc,
  pkg_json: Option<WorkspaceMemberContextConfig<PackageJson>>,
  deno_json: Option<WorkspaceMemberContextConfig<ConfigFile>>,
}

impl WorkspaceMemberContext {
  fn create_from_root_folder(
    workspace: WorkspaceRc,
    dir_url: UrlRc,
    root_folder: &FolderConfigs,
  ) -> Self {
    WorkspaceMemberContext {
      workspace,
      dir_url,
      pkg_json: root_folder.pkg_json.as_ref().map(|config| {
        WorkspaceMemberContextConfig {
          member: config.clone(),
          root: None,
        }
      }),
      deno_json: root_folder.deno_json.as_ref().map(|config| {
        WorkspaceMemberContextConfig {
          member: config.clone(),
          root: None,
        }
      }),
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
      member_ctx: self.clone(),
    })
  }

  pub fn to_lint_config(&self) -> Result<LintConfig, AnyError> {
    let mut config = self.to_lint_config_inner()?;
    self.append_workspace_members_to_exclude(&mut config.files);
    Ok(config)
  }

  fn to_lint_config_inner(&self) -> Result<LintConfig, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(LintConfig {
        rules: Default::default(),
        files: FilePatterns::new_with_base(self.dir_url.to_file_path().unwrap()),
      });
    };
    let member_config = deno_json.member.to_lint_config()?;
    let root_config = match &deno_json.root {
      Some(root) => root.to_lint_config()?,
      None => return Ok(member_config),
    };
    // combine the configs
    Ok(LintConfig {
      rules: LintRulesConfig {
        tags: combine_option_vecs(
          root_config.rules.tags,
          member_config.rules.tags,
        ),
        include: combine_option_vecs_with_override(
          CombineOptionVecsWithOverride {
            root: root_config.rules.include,
            member: member_config.rules.include.as_ref().map(Cow::Borrowed),
            member_override_root: member_config.rules.exclude.as_ref(),
          },
        ),
        exclude: combine_option_vecs_with_override(
          CombineOptionVecsWithOverride {
            root: root_config.rules.exclude,
            member: member_config.rules.exclude.map(Cow::Owned),
            member_override_root: member_config.rules.include.as_ref(),
          },
        ),
      },
      files: combine_patterns(root_config.files, member_config.files),
    })
  }

  pub fn to_fmt_config(&self) -> Result<FmtConfig, AnyError> {
    let mut config = self.to_fmt_config_inner()?;
    self.append_workspace_members_to_exclude(&mut config.files);
    Ok(config)
  }

  fn to_fmt_config_inner(&self) -> Result<FmtConfig, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(FmtConfig {
        files: FilePatterns::new_with_base(self.dir_url.to_file_path().unwrap()),
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

  pub fn to_bench_config(&self) -> Result<BenchConfig, AnyError> {
    let mut config = self.to_bench_config_inner()?;
    self.append_workspace_members_to_exclude(&mut config.files);
    Ok(config)
  }

  fn to_bench_config_inner(&self) -> Result<BenchConfig, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(BenchConfig {
        files: FilePatterns::new_with_base(self.dir_url.to_file_path().unwrap()),
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
    self.append_workspace_members_to_exclude(&mut config.files);
    Ok(config)
  }

  fn to_publish_config_inner(&self) -> Result<PublishConfig, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(PublishConfig {
        files: FilePatterns::new_with_base(self.dir_url.to_file_path().unwrap()),
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

  pub fn to_test_config(&self) -> Result<TestConfig, AnyError> {
    let mut config = self.to_test_config_inner()?;
    self.append_workspace_members_to_exclude(&mut config.files);
    Ok(config)
  }

  fn to_test_config_inner(&self) -> Result<TestConfig, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(TestConfig {
        files: FilePatterns::new_with_base(self.dir_url.to_file_path().unwrap()),
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

  fn append_workspace_members_to_exclude(&self, files: &mut FilePatterns) {
    let maybe_root_dir = self.maybe_deno_json().map(|d| d.dir_path());
    files.exclude.append(
      self
        .workspace
        .deno_jsons()
        .filter(|member_deno_json| {
          if let Some(root_dir) = &maybe_root_dir {
            let member_dir = member_deno_json.dir_path();
            member_dir != *root_dir && member_dir.starts_with(root_dir)
          } else {
            true // ok, this is just a perf optimization
          }
        })
        .map(|d| PathOrPattern::Path(d.dir_path())),
    );
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
          Some(PathOrPatternSet::new(match member_patterns.include {
            Some(member) => filtered_root
              .chain(member.into_path_or_patterns())
              .collect(),
            None => filtered_root.collect(),
          }))
        }
        None => member_patterns.include,
      }
    },
    exclude: {
      // have the root excludes at the front because they're lower priority
      let mut root_excludes = root_patterns.exclude.into_path_or_patterns();
      let member_excludes = member_patterns.exclude.into_path_or_patterns();
      root_excludes.extend(member_excludes);
      PathOrPatternSet::new(root_excludes)
    },
    base: member_patterns.base,
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
        Cow::Owned(m) => remove_duplicates_iterator(
          root.into_iter().chain(m.into_iter()),
          capacity,
        ),
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

fn combine_option_vecs<T: Eq + std::hash::Hash>(
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

fn remove_duplicates_iterator<T: Eq + std::hash::Hash>(
  iterator: impl IntoIterator<Item = T>,
  capacity: usize,
) -> Vec<T> {
  let mut seen = CheckedSet::with_capacity(capacity);
  let mut result = Vec::with_capacity(capacity);
  for item in iterator {
    if seen.insert(&item) {
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
  use pretty_assertions::assert_eq;
  use serde_json::json;

  use crate::assert_contains;
  use crate::fs::TestFileSystem;
  use crate::glob::PathOrPattern;
  use crate::TsConfig;

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

    let workspace_config_err = Workspace::discover(
      WorkspaceDiscoverStart::Dirs(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        ..Default::default()
      },
    )
    .err()
    .unwrap();

    assert_contains!(
      workspace_config_err.to_string(),
      "Workspace members cannot be empty"
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

    let workspace_config_err = Workspace::discover(
      WorkspaceDiscoverStart::Dirs(&[root_dir()]),
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

      let workspace_config_err = Workspace::discover(
        WorkspaceDiscoverStart::Dirs(&[root_dir().join("sub_dir")]),
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

    let workspace_config_err = Workspace::discover(
      WorkspaceDiscoverStart::Dirs(&[root_dir()]),
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

    let workspace = Workspace::discover(
      WorkspaceDiscoverStart::Dirs(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(workspace.config_folders.len(), 3);
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
    let workspace = new_rc(
      Workspace::discover(
        // start at root for this test
        WorkspaceDiscoverStart::Dirs(&[root_dir()]),
        &WorkspaceDiscoverOptions {
          fs: &fs,
          discover_pkg_json: true,
          ..Default::default()
        },
      )
      .unwrap(),
    );
    assert_eq!(workspace.diagnostics(), vec![]);
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
      let tasks_config =
        workspace.resolve_start_ctx().to_tasks_config().unwrap();
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
      let member_ctx = workspace.resolve_member_ctx(
        &Url::from_directory_path(root_dir().join("member/deno.json")).unwrap(),
      );
      let tasks_config = member_ctx.to_tasks_config().unwrap();
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
      let member_ctx = workspace.resolve_member_ctx(
        &Url::from_directory_path(root_dir().join("pkg_json/package.json"))
          .unwrap(),
      );
      let tasks_config = member_ctx.to_tasks_config().unwrap();
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
    let workspace = workspace_for_root_and_member(
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
      workspace.to_compiler_options().unwrap().unwrap().0,
      json!({
        // ignores member config
        "checkJs": true,
        "jsx": "react-jsx",
        "jsxImportSource": "npm:react",
      })
    );
    assert_eq!(
      workspace.to_maybe_imports().unwrap(),
      vec![(
        Url::from_file_path(root_dir().join("deno.json")).unwrap(),
        vec!["./types.d.ts".to_string()]
      )]
    );
    assert_eq!(
      workspace
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
    assert_eq!(workspace.check_js(), true);
    assert_eq!(
      workspace
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
      workspace.diagnostics(),
      vec![WorkspaceDiagnostic {
        kind: WorkspaceDiagnosticKind::RootOnlyOption("compilerOptions"),
        config_url: Url::from_file_path(root_dir().join("member/deno.json"))
          .unwrap(),
      }]
    );
  }

  #[test]
  fn test_root_member_import_map() {
    let workspace = workspace_for_root_and_member_with_fs(
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
      workspace.to_import_map_specifier().unwrap().unwrap(),
      Url::from_file_path(root_dir().join("other.json")).unwrap()
    );
    assert_eq!(
      workspace.diagnostics(),
      vec![WorkspaceDiagnostic {
        kind: WorkspaceDiagnosticKind::RootOnlyOption("importMap"),
        config_url: Url::from_file_path(root_dir().join("member/deno.json"))
          .unwrap(),
      }]
    );
  }

  #[tokio::test]
  async fn test_root_member_imports_and_scopes() {
    let workspace = workspace_for_root_and_member(
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
      workspace.diagnostics(),
      vec![WorkspaceDiagnostic {
        kind: WorkspaceDiagnosticKind::RootOnlyOption("scopes"),
        config_url: Url::from_file_path(root_dir().join("member/deno.json"))
          .unwrap(),
      }]
    );
    let resolver = workspace
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
  fn test_root_member_exclude() {
    let workspace = workspace_for_root_and_member(
      json!({
        "exclude": [
          "./root",
          "./member/vendor"
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
    assert_eq!(workspace.diagnostics(), vec![]);
    let ctx = workspace.resolve_start_ctx();
    let lint_config = ctx.to_lint_config().unwrap();
    assert_eq!(
      lint_config.files,
      FilePatterns {
        base: root_dir().join("member"),
        include: None,
        exclude: PathOrPatternSet::new(vec![
          // maybe this shouldn't contain excludes in a root directory, but this is ok
          PathOrPattern::Path(root_dir().join("root")),
          PathOrPattern::Path(root_dir().join("member").join("vendor")),
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
    let workspace = workspace_for_root_and_member(
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
      workspace.diagnostics(),
      vec![WorkspaceDiagnostic {
        kind: WorkspaceDiagnosticKind::RootOnlyOption("lint.report"),
        config_url: Url::from_file_path(root_dir().join("member/deno.json"))
          .unwrap(),
      }]
    );
    assert_eq!(
      workspace.to_lint_config().unwrap(),
      WorkspaceLintConfig {
        report: Some("json".to_string()),
      }
    );
    let lint_config = workspace.resolve_start_ctx().to_lint_config().unwrap();
    assert_eq!(
      lint_config,
      LintConfig {
        rules: LintRulesConfig {
          tags: Some(vec!["tag1".to_string()]),
          include: Some(vec!["rule1".to_string(), "rule2".to_string()]),
          exclude: Some(vec![])
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
    let root_lint_config = workspace
      .resolve_member_ctx(&Url::from_directory_path(root_dir()).unwrap())
      .to_lint_config()
      .unwrap();
    assert_eq!(
      root_lint_config,
      LintConfig {
        rules: LintRulesConfig {
          tags: Some(vec!["tag1".to_string()]),
          include: Some(vec!["rule1".to_string()]),
          exclude: Some(vec!["rule2".to_string()])
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
    let workspace = workspace_for_root_and_member(
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
    assert_eq!(workspace.diagnostics(), vec![]);
    let fmt_config = workspace.resolve_start_ctx().to_fmt_config().unwrap();
    assert_eq!(
      fmt_config,
      FmtConfig {
        options: FmtOptionsConfig {
          use_tabs: Some(false),
          line_width: Some(120),
          indent_width: Some(8),
          prose_wrap: Some(crate::ProseWrap::Always),
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
    let root_fmt_config = workspace
      .resolve_member_ctx(&Url::from_directory_path(root_dir()).unwrap())
      .to_fmt_config()
      .unwrap();
    assert_eq!(
      root_fmt_config,
      FmtConfig {
        options: FmtOptionsConfig {
          use_tabs: Some(true),
          line_width: Some(80),
          indent_width: Some(4),
          prose_wrap: Some(crate::ProseWrap::Never),
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
    let workspace = workspace_for_root_and_member(
      json!({}),
      json!({
        "bench": {
          "exclude": ["subdir"],
        }
      }),
    );
    assert_eq!(workspace.diagnostics(), vec![]);
    let bench_config = workspace.resolve_start_ctx().to_bench_config().unwrap();
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
    let root_bench_config = workspace
      .resolve_member_ctx(&Url::from_directory_path(root_dir()).unwrap())
      .to_bench_config()
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
    let workspace = workspace_for_root_and_member(
      json!({}),
      json!({
        "test": {
          "include": ["subdir"],
        }
      }),
    );
    assert_eq!(workspace.diagnostics(), vec![]);
    let config = workspace.resolve_start_ctx().to_test_config().unwrap();
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
    let root_test_config = workspace
      .resolve_member_ctx(&Url::from_directory_path(root_dir()).unwrap())
      .to_test_config()
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
    let workspace = workspace_for_root_and_member(
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
    assert_eq!(workspace.diagnostics(), vec![]);
    let config = workspace.resolve_start_ctx().to_publish_config().unwrap();
    assert_eq!(
      config,
      PublishConfig {
        files: FilePatterns {
          base: root_dir().join("member"),
          include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
            root_dir().join("member").join("subdir")
          )])),
          exclude: PathOrPatternSet::new(vec![
            PathOrPattern::Path(root_dir().join("other")),
            PathOrPattern::Path(root_dir().join("member").join("exclude_dir")),
          ]),
        },
      }
    );

    // check the root context
    let root_publish_config = workspace
      .resolve_member_ctx(&Url::from_directory_path(root_dir()).unwrap())
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
    let workspace = workspace_for_root_and_member(json!({}), json!({}));
    assert_eq!(workspace.diagnostics(), vec![]);
    let root_files = FilePatterns {
      base: root_dir(),
      include: None,
      // the workspace member will be excluded because that needs
      // to be resolved separately
      exclude: PathOrPatternSet::new(Vec::from([PathOrPattern::Path(
        root_dir().join("member"),
      )])),
    };
    let root_ctx = workspace
      .resolve_member_ctx(&Url::from_directory_path(root_dir()).unwrap());
    let member_files = FilePatterns {
      base: root_dir().join("member"),
      include: None,
      exclude: Default::default(),
    };
    let member_ctx = workspace.resolve_start_ctx();

    for (files, ctx) in [(root_files, root_ctx), (member_files, member_ctx)] {
      assert_eq!(
        ctx.to_bench_config().unwrap(),
        BenchConfig {
          files: files.clone(),
        }
      );
      assert_eq!(
        ctx.to_fmt_config().unwrap(),
        FmtConfig {
          options: Default::default(),
          files: files.clone(),
        }
      );
      assert_eq!(
        ctx.to_lint_config().unwrap(),
        LintConfig {
          files: files.clone(),
          rules: Default::default(),
        }
      );
      assert_eq!(
        ctx.to_test_config().unwrap(),
        TestConfig {
          files: files.clone(),
        }
      );
      assert_eq!(
        ctx.to_publish_config().unwrap(),
        PublishConfig {
          files: files.clone(),
        }
      );
    }
  }

  #[test]
  fn test_root_member_root_only_in_member() {
    let workspace = workspace_for_root_and_member(
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
    assert_eq!(workspace.unstable_features(), &["byonm".to_string()]);
    assert!(workspace.has_unstable("byonm"));
    assert!(!workspace.has_unstable("sloppy-imports"));
    assert_eq!(
      workspace.to_lock_config().unwrap().unwrap(),
      LockConfig::Bool(false),
    );
    assert_eq!(workspace.node_modules_dir(), Some(false));
    assert_eq!(workspace.vendor_dir_path(), Some(root_dir().join("vendor")));
    assert_eq!(
      workspace.diagnostics(),
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
    let workspace = workspace_for_root_and_member(
      json!({
        "name": "@scope/name",
        "version": "1.0.0",
        "exports": "./main.ts"
      }),
      json!({}),
    );
    // this is fine because we can tell it's a package by it having name and exports fields
    assert_eq!(workspace.diagnostics(), vec![]);
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
    let workspace = Workspace::discover(
      // start at root for this test
      WorkspaceDiscoverStart::Dirs(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(
      workspace.diagnostics(),
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
    let workspace = Workspace::discover(
      WorkspaceDiscoverStart::Dirs(&[root_dir()]),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(
      workspace.diagnostics(),
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
    let err = Workspace::discover(
      WorkspaceDiscoverStart::Dirs(&[root_dir()]),
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
    let workspace = workspace_at_start_dir(&fs, &root_dir().join("member"));
    assert_eq!(workspace.diagnostics(), vec![]);
    let jsr_pkgs = workspace.jsr_packages_for_publish();
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
      let workspace = workspace_at_start_dir(&fs, &root_dir());
      assert_eq!(workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace.jsr_packages_for_publish();
      let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
      assert_eq!(names, vec!["@scope/a", "@scope/b"]);
    }
    // member
    {
      let workspace = workspace_at_start_dir(&fs, &root_dir().join("a"));
      assert_eq!(workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace.jsr_packages_for_publish();
      let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
      assert_eq!(names, vec!["@scope/a"]);
    }
    // member, not a package
    {
      let workspace = workspace_at_start_dir(&fs, &root_dir().join("c"));
      assert_eq!(workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace.jsr_packages_for_publish();
      assert!(jsr_pkgs.is_empty());
    }
    // package.json
    {
      let workspace = workspace_at_start_dir(&fs, &root_dir().join("d"));
      assert_eq!(workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace.jsr_packages_for_publish();
      assert!(jsr_pkgs.is_empty());

      // while we're here, test this
      assert_eq!(
        workspace
          .package_jsons()
          .map(|p| p.dir_path().to_path_buf())
          .collect::<Vec<_>>(),
        vec![root_dir().join("d")]
      );
      assert_eq!(
        workspace
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
      let workspace = workspace_at_start_dir(&fs, &root_dir().join("member"));
      assert_eq!(workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace.jsr_packages_for_publish();
      let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
      assert_eq!(names, vec!["@scope/pkg"]);
    }
    // at the root
    {
      let workspace = workspace_at_start_dir(&fs, &root_dir());
      assert_eq!(workspace.diagnostics(), vec![]);
      let jsr_pkgs = workspace.jsr_packages_for_publish();
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
    let workspace = workspace_at_start_dir(&fs, &root_dir());
    assert_eq!(workspace.diagnostics(), vec![]);
    let jsr_pkgs = workspace.jsr_packages_for_publish();
    let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
    assert_eq!(names, vec!["@scope/pkg"]);
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
    let workspace = workspace_at_start_dir(
      &fs,
      &root_dir().join("node_modules/package/sub_dir"),
    );
    assert_eq!(workspace.diagnostics(), vec![]);
    assert_eq!(workspace.package_jsons().count(), 0);
    assert_eq!(workspace.deno_jsons().count(), 1);
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
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("deno.json"),
      json!({
        "workspace": ["./member"]
      }),
    );
    fs.insert_json(root_dir().join("member/deno.json"), json!({}));
    fs.insert_json(root_dir().join("package/deno.json"), json!({}));
    let err = workspace_at_start_dir_err(&fs, &root_dir().join("package"));
    assert_eq!(
      err.to_string(),
      normalize_err_text(
        "Config file must be a member of the workspace.
  Config: [ROOT_DIR_URL]/package/deno.json
  Workspace: [ROOT_DIR_URL]/"
      )
    );
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
    let workspace = workspace_at_start_dir(&fs, &root_dir().join("package"));
    assert_eq!(workspace.diagnostics(), Vec::new());
    assert_eq!(workspace.deno_jsons().count(), 2);
    assert_eq!(workspace.package_jsons().count(), 2);
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
    let workspace = workspace_at_start_dir(&fs, &root_dir().join("package"));
    assert_eq!(workspace.diagnostics(), Vec::new());
    assert_eq!(workspace.deno_jsons().count(), 1);
    assert_eq!(workspace.package_jsons().count(), 2);
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
    let workspace = workspace_at_start_dirs(
      &fs,
      &[
        root_dir().join("workspace/member"),
        root_dir().join("other_dir"), // will be ignored because it's not in the workspace
      ],
    )
    .unwrap();
    assert_eq!(workspace.diagnostics(), vec![]);
    let jsr_pkgs = workspace.jsr_packages_for_publish();
    let names = jsr_pkgs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>();
    assert_eq!(names, vec!["@scope/pkg"]);
  }

  #[test]
  fn test_resolve_multiple_dirs_outside_config() {
    let mut fs = TestFileSystem::default();
    fs.insert_json(
      root_dir().join("workspace/deno.json"),
      json!({
        "workspace": ["./member"]
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
    let workspace = Workspace::discover(
      WorkspaceDiscoverStart::ConfigFile(&other_deno_json),
      &WorkspaceDiscoverOptions {
        fs: &fs,
        discover_pkg_json: true,
        ..Default::default()
      },
    )
    .unwrap();
    assert_eq!(
      workspace
        .deno_jsons()
        .map(|d| d.specifier.clone())
        .collect::<Vec<_>>(),
      vec![Url::from_file_path(&other_deno_json).unwrap()]
    );
  }

  fn workspace_for_root_and_member(
    root: serde_json::Value,
    member: serde_json::Value,
  ) -> WorkspaceRc {
    workspace_for_root_and_member_with_fs(root, member, |_| {})
  }

  fn workspace_for_root_and_member_with_fs(
    mut root: serde_json::Value,
    member: serde_json::Value,
    with_fs: impl FnOnce(&mut TestFileSystem),
  ) -> WorkspaceRc {
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
  ) -> WorkspaceRc {
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
  ) -> Result<WorkspaceRc, WorkspaceDiscoverError> {
    workspace_at_start_dirs(fs, &[start_dir.to_path_buf()])
  }

  fn workspace_at_start_dirs(
    fs: &TestFileSystem,
    start_dirs: &[PathBuf],
  ) -> Result<WorkspaceRc, WorkspaceDiscoverError> {
    Workspace::discover(
      WorkspaceDiscoverStart::Dirs(start_dirs),
      &WorkspaceDiscoverOptions {
        fs,
        discover_pkg_json: true,
        ..Default::default()
      },
    )
    .map(new_rc)
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
