// Copyright 2018-2024 the Deno authors. MIT license.

use std::borrow::Cow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::future::Future;
use std::path::Path;
use std::path::PathBuf;

use anyhow::bail;
use anyhow::Context;
use anyhow::Error as AnyError;
use deno_semver::package::PackageNv;
use discovery::discover_with_npm;
use discovery::discover_workspace_config_files;
use discovery::ConfigFileDiscovery;
use discovery::DenoOrPkgJson;
use discovery::PackageJsonDiscovery;
use indexmap::IndexMap;
use thiserror::Error;
use url::Url;

use crate::deno_json::ConfigFile;
use crate::deno_json::ConfigFileReadError;
use crate::deno_json::ConfigParseOptions;
use crate::get_ts_config_for_emit;
use crate::glob::FilePatterns;
use crate::glob::PathKind;
use crate::glob::PathOrPatternSet;
use crate::package_json::PackageJson;
use crate::package_json::PackageJsonLoadError;
use crate::package_json::PackageJsonRc;
use crate::sync::new_rc;
use crate::util::specifier_to_file_path;
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
pub use resolver::SpecifiedImportMap;
pub use resolver::WorkspaceResolver;
pub use resolver::WorkspaceResolverCreateError;

#[allow(clippy::disallowed_types)]
type UrlRc = crate::sync::MaybeArc<Url>;

#[derive(Debug, Clone)]
pub struct JsrPackageConfig {
  pub package_name: String,
  pub member_ctx: WorkspaceMemberContext,
  pub config_file: ConfigFileRc,
}

#[derive(Debug, Clone)]
pub struct NpmPackageConfig {
  pub package_nv: PackageNv,
  pub member_ctx: WorkspaceMemberContext,
  pub package_json: PackageJsonRc,
}

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum WorkspaceDiagnosticKind {
  #[error("The '{0}' option can only be specified in the root workspace deno.json file.")]
  RootOnlyOption(&'static str),
  #[error("The '{0}' option can only be specified in a workspace member deno.json file and not the root workspace file.")]
  MemberOnlyOption(&'static str),
  #[error("The '{name}' member cannot have the same name as the member at '{other_member}'.")]
  DuplicateMemberName { name: String, other_member: Url },
  #[error("The 'workspaces' option should be called 'workspace'.")]
  DeprecatedWorkspacesOption,
}

impl WorkspaceDiagnosticKind {
  /// If the diagnostic should cause the process to shut down.
  pub fn is_fatal(&self) -> bool {
    match self {
      Self::RootOnlyOption { .. }
      | Self::MemberOnlyOption { .. }
      | Self::DeprecatedWorkspacesOption => false,
      Self::DuplicateMemberName { .. } => true,
    }
  }
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
  #[error(transparent)]
  ConfigReadError(#[from] ConfigFileReadError),
  #[error(transparent)]
  PackageJsonReadError(#[from] PackageJsonLoadError),
  #[error("Workspace member must be nested in a directory under the workspace.\n  Member: {member_url}\n  Workspace: {workspace_url}")]
  NonDescendant { workspace_url: Url, member_url: Url },
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
  #[error(transparent)]
  ConfigRead(#[from] ConfigFileReadError),
  #[error(transparent)]
  PackageJsonReadError(#[from] PackageJsonLoadError),
  #[error("Workspace members cannot be empty.\n  Workspace: {0}")]
  MembersEmpty(Url),
  #[error(transparent)]
  ResolveMember(#[from] ResolveWorkspaceMemberError),
  #[error("Invalid workspace member '{}' for config '{}'.", member, base)]
  InvalidMember {
    base: Url,
    member: String,
    #[source]
    source: url::ParseError,
  },
  #[error(transparent)]
  SpecifierToFilePath(#[from] SpecifierToFilePathError),
  #[error("Config file must be a member of the workspace.\n  Config: {config_url}\n  Workspace: {workspace_url}")]
  ConfigNotWorkspaceMember { workspace_url: Url, config_url: Url },
}

#[derive(Debug, Clone, Copy)]
pub enum WorkspaceDiscoverStart<'a> {
  Dir(&'a Path),
  ConfigFile(&'a Path),
}

impl<'a> WorkspaceDiscoverStart<'a> {
  pub fn dir_path(&self) -> &Path {
    match self {
      Self::Dir(dir) => dir,
      Self::ConfigFile(file) => file.parent().unwrap(),
    }
  }
}

pub struct WorkspaceDiscoverOptions<'a> {
  pub fs: &'a dyn crate::fs::DenoConfigFs,
  pub pkg_json_cache: Option<&'a dyn crate::package_json::PackageJsonCache>,
  pub start: WorkspaceDiscoverStart<'a>,
  pub config_parse_options: &'a ConfigParseOptions,
  pub additional_config_file_names: &'a [&'a str],
  pub discover_pkg_json: bool,
}

/// Configuration files found in a specific folder.
#[derive(Debug, Default, Clone)]
pub struct FolderConfigs {
  pub deno_json: Option<ConfigFileRc>,
  pub pkg_json: Option<PackageJsonRc>,
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
    opts: &WorkspaceDiscoverOptions,
  ) -> Result<Self, WorkspaceDiscoverError> {
    let start_dir =
      new_rc(Url::from_directory_path(opts.start.dir_path()).unwrap());
    let config_file_discovery = discover_workspace_config_files(opts)?;
    let maybe_npm_discovery = if opts.discover_pkg_json {
      discover_with_npm(&config_file_discovery, opts)?
    } else {
      PackageJsonDiscovery::None
    };

    let mut workspace = match config_file_discovery {
      ConfigFileDiscovery::None => Workspace {
        config_folders: IndexMap::from([(
          start_dir.clone(),
          FolderConfigs::default(),
        )]),
        root_dir: start_dir.clone(),
        start_dir,
      },
      ConfigFileDiscovery::Single(config) => {
        let config_file_path = specifier_to_file_path(&config.specifier)?;
        let root_dir = config_file_path.parent().unwrap();
        let root_dir = new_rc(Url::from_directory_path(root_dir).unwrap());
        Workspace {
          config_folders: IndexMap::from([(
            root_dir.clone(),
            FolderConfigs {
              deno_json: Some(config),
              pkg_json: None,
            },
          )]),
          start_dir,
          root_dir,
        }
      }
      ConfigFileDiscovery::Workspace { root, members } => {
        let root_config_file_path = specifier_to_file_path(&root.specifier)?;
        let root_dir = root_config_file_path.parent().unwrap();
        let root_dir = new_rc(Url::from_directory_path(root_dir).unwrap());
        let mut config_folders = members
          .into_iter()
          .map(|(folder_url, config)| {
            (
              folder_url,
              match config {
                DenoOrPkgJson::Deno(config_file) => FolderConfigs {
                  deno_json: Some(config_file),
                  pkg_json: None,
                },
                DenoOrPkgJson::PkgJson(pkg_json) => FolderConfigs {
                  deno_json: None,
                  pkg_json: Some(pkg_json),
                },
              },
            )
          })
          .collect::<IndexMap<_, _>>();
        config_folders
          .entry(root_dir.clone())
          .or_default()
          .deno_json = Some(root);
        Workspace {
          root_dir,
          start_dir,
          config_folders,
        }
      }
    };
    match maybe_npm_discovery {
      PackageJsonDiscovery::Single(pkg_json) => {
        let pkg_json_dir = new_rc(
          Url::from_directory_path(pkg_json.path.parent().unwrap()).unwrap(),
        );
        if workspace
          .root_dir
          .as_str()
          .starts_with(pkg_json_dir.as_str())
        {
          // the package.json was in a higher up directory
          workspace.root_dir = pkg_json_dir.clone();
        }

        workspace
          .config_folders
          .entry(pkg_json_dir)
          .or_default()
          .pkg_json = Some(pkg_json);
      }
      PackageJsonDiscovery::Workspace { root, members } => {
        let pkg_json_dir = new_rc(
          Url::from_directory_path(root.path.parent().unwrap()).unwrap(),
        );
        if workspace
          .root_dir
          .as_str()
          .starts_with(pkg_json_dir.as_str())
        {
          // the package.json was in a higher up directory
          workspace.root_dir = pkg_json_dir.clone();
        }

        workspace
          .config_folders
          .entry(pkg_json_dir)
          .or_default()
          .pkg_json = Some(root);

        for (member_dir, pkg_json) in members {
          workspace
            .config_folders
            .entry(member_dir)
            .or_default()
            .pkg_json = Some(pkg_json);
        }
      }
      PackageJsonDiscovery::None => {
        // do nothing
      }
    }

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
    fn check_root_diagnostics(
      root_config: &ConfigFile,
      diagnostics: &mut Vec<WorkspaceDiagnostic>,
    ) {
      if root_config.json.name.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: root_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::MemberOnlyOption("name"),
        });
      }
      if root_config.json.version.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: root_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::MemberOnlyOption("version"),
        });
      }
      if root_config.json.exports.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: root_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::MemberOnlyOption("exports"),
        });
      }
      if root_config.json.deprecated_workspaces.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: root_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::DeprecatedWorkspacesOption,
        });
      }
    }

    fn check_member_diagnostics<'a>(
      member_config: &'a ConfigFile,
      diagnostics: &mut Vec<WorkspaceDiagnostic>,
      seen_names: &mut HashMap<&'a str, &'a Url>,
    ) {
      if member_config.json.compiler_options.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("compilerOptions"),
        });
      }
      if member_config.json.node_modules_dir.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("nodeModulesDir"),
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
      if member_config.json.scopes.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("scopes"),
        });
      }
      if member_config.json.vendor.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("vendor"),
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
      if !member_config.json.unstable.is_empty() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("unstable"),
        });
      }
      if member_config.json.workspace.is_some() {
        diagnostics.push(WorkspaceDiagnostic {
          config_url: member_config.specifier.clone(),
          kind: WorkspaceDiagnosticKind::RootOnlyOption("workspace"),
        });
      }
      if let Some(name) = member_config.json.name.as_deref() {
        if let Some(other_member_url) = seen_names.get(name) {
          diagnostics.push(WorkspaceDiagnostic {
            config_url: member_config.specifier.clone(),
            kind: WorkspaceDiagnosticKind::DuplicateMemberName {
              name: name.to_string(),
              other_member: (*other_member_url).clone(),
            },
          });
        } else {
          seen_names.insert(name, &member_config.specifier);
        }
      }
    }

    let mut diagnostics = Vec::new();
    if self.config_folders.len() == 1 {
      // no diagnostics to surface because the root is the only config
      return diagnostics;
    }
    let mut seen_names = HashMap::with_capacity(self.config_folders.len());
    for (url, folder) in &self.config_folders {
      if let Some(config) = &folder.deno_json {
        if url == &self.root_dir {
          check_root_diagnostics(config, &mut diagnostics);
        } else {
          check_member_diagnostics(config, &mut diagnostics, &mut seen_names);
        }
      }
    }
    diagnostics
  }

  /// Resolves the `WorkspaceMemberContext` from the directory that workspace discovery
  /// started from.
  pub fn resolve_start_ctx(&self) -> WorkspaceMemberContext {
    self.resolve_member_ctx(&self.start_dir)
  }

  /// Resolves a workspace member's context, which can be used for deriving
  /// configuration specific to a member.
  pub fn resolve_member_ctx(&self, specifier: &Url) -> WorkspaceMemberContext {
    let maybe_folder = self.resolve_folder(specifier);
    match maybe_folder {
      Some((member_url, folder)) => {
        if member_url == &self.root_dir {
          WorkspaceMemberContext::create_from_root_folder(
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

  pub fn jsr_packages(&self) -> Vec<JsrPackageConfig> {
    self
      .deno_jsons()
      .filter_map(|c| {
        if !c.is_package() {
          return None;
        }
        Some(JsrPackageConfig {
          member_ctx: self.resolve_member_ctx(&c.specifier),
          package_name: c.json.name.clone()?,
          config_file: c.clone(),
        })
      })
      .collect()
  }

  pub fn jsr_packages_for_publish(&self) -> Vec<JsrPackageConfig> {
    let ctx = self.resolve_start_ctx();
    let Some(config) = &ctx.deno_json else {
      return Vec::new();
    };
    let deno_json = &config.member;
    if deno_json.dir_path() == self.root_dir.to_file_path().unwrap() {
      return self.jsr_packages();
    }
    match ctx.maybe_package_config() {
      Some(pkg) => vec![pkg],
      None => Vec::new(),
    }
  }

  pub fn npm_packages(&self) -> Vec<NpmPackageConfig> {
    self
      .package_jsons()
      .filter_map(|c| {
        Some(NpmPackageConfig {
          member_ctx: self.resolve_member_ctx(&c.specifier()),
          package_nv: PackageNv {
            name: c.name.clone()?,
            version: {
              let version = c.version.as_ref()?;
              deno_semver::Version::parse_from_npm(version).ok()?
            },
          },
          package_json: c.clone(),
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
    &self,
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
      Some(c) => c.to_files_config()?.exclude.into_path_or_patterns(),
      None => Default::default(),
    };
    for (dir_url, folder) in self.config_folders.iter() {
      let Some(deno_json) = folder.deno_json.as_ref() else {
        continue;
      };
      if dir_url == &self.root_dir {
        continue;
      }
      excludes
        .extend(deno_json.to_files_config()?.exclude.into_path_or_patterns());
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

#[derive(Debug, Clone)]
pub struct WorkspaceMemberTasksConfig {
  pub folder_url: Url,
  pub deno_json: Option<IndexMap<String, Task>>,
  pub package_json: Option<IndexMap<String, String>>,
}

impl WorkspaceMemberTasksConfig {
  pub fn with_only_pkg_json(self) -> Self {
    WorkspaceMemberTasksConfig {
      folder_url: self.folder_url,
      deno_json: None,
      package_json: self.package_json,
    }
  }

  pub fn is_empty(&self) -> bool {
    self
      .deno_json
      .as_ref()
      .map(|d| d.is_empty())
      .unwrap_or(true)
      && self
        .package_json
        .as_ref()
        .map(|d| d.is_empty())
        .unwrap_or(true)
  }

  pub fn tasks_count(&self) -> usize {
    self.deno_json.as_ref().map(|d| d.len()).unwrap_or(0)
      + self.package_json.as_ref().map(|d| d.len()).unwrap_or(0)
  }

  pub fn task(&self, name: &str) -> Option<(&Url, TaskOrScript)> {
    self
      .deno_json
      .as_ref()
      .and_then(|tasks| {
        tasks.get(name).map(|t| {
          (&self.folder_url, TaskOrScript::Task(tasks, t.definition()))
        })
      })
      .or_else(|| {
        self.package_json.as_ref().and_then(|scripts| {
          scripts
            .get(name)
            .map(|s| (&self.folder_url, TaskOrScript::Script(scripts, s)))
        })
      })
  }
}

#[derive(Debug, Clone)]
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
  dir_url: UrlRc,
  pkg_json: Option<WorkspaceMemberContextConfig<PackageJson>>,
  deno_json: Option<WorkspaceMemberContextConfig<ConfigFile>>,
}

impl WorkspaceMemberContext {
  fn create_from_root_folder(
    dir_url: UrlRc,
    root_folder: &FolderConfigs,
  ) -> Self {
    WorkspaceMemberContext {
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
      package_name: pkg_name.clone(),
      config_file: deno_json.clone(),
      member_ctx: self.clone(),
    })
  }

  pub fn to_lint_config(&self) -> Result<Option<LintConfig>, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(None);
    };
    let maybe_member_config = deno_json.member.to_lint_config()?;
    let maybe_root_config = match &deno_json.root {
      Some(root) => root.to_lint_config()?,
      None => None,
    };
    let Some(member_config) = maybe_member_config else {
      return Ok(maybe_root_config.map(|c| LintConfig {
        files: c.files.with_new_base(self.dir_url.to_file_path().unwrap()),
        ..c
      }));
    };
    let Some(root_config) = maybe_root_config else {
      return Ok(Some(member_config));
    };
    // combine the configs
    Ok(Some(LintConfig {
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
    }))
  }

  pub fn to_fmt_config(&self) -> Result<Option<FmtConfig>, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(None);
    };
    let maybe_member_config = deno_json.member.to_fmt_config()?;
    let maybe_root_config = match &deno_json.root {
      Some(root) => root.to_fmt_config()?,
      None => None,
    };
    let Some(member_config) = maybe_member_config else {
      return Ok(maybe_root_config.map(|c| FmtConfig {
        files: c.files.with_new_base(self.dir_url.to_file_path().unwrap()),
        ..c
      }));
    };
    let Some(root_config) = maybe_root_config else {
      return Ok(Some(member_config));
    };

    Ok(Some(FmtConfig {
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
    }))
  }

  pub fn to_bench_config(&self) -> Result<Option<BenchConfig>, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(None);
    };
    let maybe_member_config = deno_json.member.to_bench_config()?;
    let maybe_root_config = match &deno_json.root {
      Some(root) => root.to_bench_config()?,
      None => None,
    };
    let Some(member_config) = maybe_member_config else {
      return Ok(maybe_root_config.map(|c| BenchConfig {
        files: c.files.with_new_base(self.dir_url.to_file_path().unwrap()),
      }));
    };
    let Some(root_config) = maybe_root_config else {
      return Ok(Some(member_config));
    };

    Ok(Some(BenchConfig {
      files: combine_patterns(root_config.files, member_config.files),
    }))
  }

  pub fn to_tasks_config(&self) -> Result<WorkspaceTasksConfig, AnyError> {
    fn to_member_tasks_config(
      maybe_deno_json: Option<&ConfigFileRc>,
      maybe_pkg_json: Option<&PackageJsonRc>,
    ) -> Result<Option<WorkspaceMemberTasksConfig>, AnyError> {
      Ok(Some(WorkspaceMemberTasksConfig {
        folder_url: match maybe_deno_json {
          Some(deno_json) => Url::from_directory_path(
            specifier_to_file_path(&deno_json.specifier)?
              .parent()
              .unwrap(),
          )
          .unwrap(),
          None => match maybe_pkg_json {
            Some(pkg_json) => {
              Url::from_directory_path(pkg_json.path.parent().unwrap()).unwrap()
            }
            None => return Ok(None),
          },
        },
        deno_json: match maybe_deno_json {
          Some(deno_json) => {
            deno_json.to_tasks_config().with_context(|| {
              format!("Failed parsing '{}'.", deno_json.specifier)
            })?
          }
          None => None,
        },
        package_json: match maybe_pkg_json {
          Some(pkg_json) => pkg_json.scripts.clone(),
          None => None,
        },
      }))
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

  pub fn to_publish_config(&self) -> Result<Option<PublishConfig>, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(None);
    };
    let maybe_member_config = deno_json.member.to_publish_config()?;
    let maybe_root_config = match &deno_json.root {
      Some(root) => root.to_publish_config()?,
      None => None,
    };
    let Some(member_config) = maybe_member_config else {
      return Ok(maybe_root_config.map(|c| PublishConfig {
        files: c.files.with_new_base(self.dir_url.to_file_path().unwrap()),
      }));
    };
    let Some(root_config) = maybe_root_config else {
      return Ok(Some(member_config));
    };

    Ok(Some(PublishConfig {
      files: combine_patterns(root_config.files, member_config.files),
    }))
  }

  pub fn to_test_config(&self) -> Result<Option<TestConfig>, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(None);
    };
    let maybe_member_config = deno_json.member.to_test_config()?;
    let maybe_root_config = match &deno_json.root {
      Some(root) => root.to_test_config()?,
      None => None,
    };
    let Some(member_config) = maybe_member_config else {
      return Ok(maybe_root_config.map(|c| TestConfig {
        files: c.files.with_new_base(self.dir_url.to_file_path().unwrap()),
      }));
    };
    let Some(root_config) = maybe_root_config else {
      return Ok(Some(member_config));
    };

    Ok(Some(TestConfig {
      files: combine_patterns(root_config.files, member_config.files),
    }))
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
  use crate::fs::DenoConfigFs;
  use crate::glob::PathOrPattern;

  use super::*;

  #[derive(Debug, Default)]
  struct TestFileSystem(pub HashMap<PathBuf, String>);

  impl TestFileSystem {
    fn insert_json(
      &mut self,
      path: impl AsRef<Path>,
      contents: serde_json::Value,
    ) {
      self.insert(path, contents.to_string())
    }

    fn insert(&mut self, path: impl AsRef<Path>, contents: impl AsRef<str>) {
      self
        .0
        .insert(path.as_ref().to_path_buf(), contents.as_ref().to_string());
    }
  }

  impl DenoConfigFs for TestFileSystem {
    fn read_to_string(&self, path: &Path) -> Result<String, std::io::Error> {
      self.0.get(path).cloned().ok_or_else(|| {
        std::io::Error::new(std::io::ErrorKind::NotFound, "file not found")
      })
    }
  }

  fn root_dir() -> PathBuf {
    if cfg!(windows) {
      PathBuf::from("C:\\Users\\User")
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

    let workspace_config_err = Workspace::discover(&WorkspaceDiscoverOptions {
      fs: &fs,
      pkg_json_cache: None,
      start: WorkspaceDiscoverStart::Dir(&root_dir()),
      config_parse_options: &ConfigParseOptions::default(),
      additional_config_file_names: &[],
      discover_pkg_json: false,
    })
    .err()
    .unwrap();

    assert_contains!(
      workspace_config_err.to_string(),
      "Workspace members cannot be empty"
    );
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

    let workspace_config_err = Workspace::discover(&WorkspaceDiscoverOptions {
      fs: &fs,
      pkg_json_cache: None,
      start: WorkspaceDiscoverStart::Dir(&root_dir()),
      config_parse_options: &ConfigParseOptions::default(),
      additional_config_file_names: &[],
      discover_pkg_json: false,
    })
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

    let workspace = Workspace::discover(&WorkspaceDiscoverOptions {
      fs: &fs,
      pkg_json_cache: None,
      start: WorkspaceDiscoverStart::Dir(&root_dir()),
      config_parse_options: &ConfigParseOptions::default(),
      additional_config_file_names: &[],
      discover_pkg_json: false,
    })
    .unwrap();
    assert_eq!(workspace.config_folders.len(), 3);
  }

  #[test]
  fn test_root_member_compiler_options() {
    let workspace = workspace_for_root_and_member(
      json!({
        "compilerOptions": {
          "checkJs": true
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
        "checkJs": true
      })
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
      .create_resolver(
        CreateResolverOptions {
          pkg_json_dep_resolution: true,
          specified_import_map: None,
        },
        |_| async move {
          unreachable!();
        },
      )
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
    let lint_config = ctx.to_lint_config().unwrap().unwrap();
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
          "report": "json"
        }
      }),
      json!({
        "lint": {
          "report": "pretty"
        }
      }),
    );
    assert_eq!(workspace.diagnostics(), vec![]);
    let ctx = workspace.resolve_start_ctx();
    let lint_config = ctx.to_lint_config().unwrap().unwrap();
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

  fn workspace_for_root_and_member(
    root: serde_json::Value,
    member: serde_json::Value,
  ) -> Workspace {
    workspace_for_root_and_member_with_fs(root, member, |_| {})
  }

  fn workspace_for_root_and_member_with_fs(
    mut root: serde_json::Value,
    member: serde_json::Value,
    with_fs: impl FnOnce(&mut TestFileSystem),
  ) -> Workspace {
    root
      .as_object_mut()
      .unwrap()
      .insert("workspace".to_string(), json!(["./member"]));
    let mut fs = TestFileSystem::default();
    fs.insert_json(root_dir().join("deno.json"), root);
    fs.insert_json(root_dir().join("member/deno.json"), member);
    with_fs(&mut fs);
    Workspace::discover(&WorkspaceDiscoverOptions {
      fs: &fs,
      pkg_json_cache: None,
      // start in the member
      start: WorkspaceDiscoverStart::Dir(&root_dir().join("member")),
      config_parse_options: &ConfigParseOptions::default(),
      additional_config_file_names: &[],
      discover_pkg_json: false,
    })
    .unwrap()
  }
}
