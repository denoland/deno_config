// Copyright 2018-2024 the Deno authors. MIT license.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::path::Path;
use std::sync::Arc;

use anyhow::Error as AnyError;
use indexmap::IndexMap;
use thiserror::Error;
use url::Url;

use crate::deno_json::ConfigFile;
use crate::deno_json::ConfigFileReadError;
use crate::deno_json::ConfigParseOptions;
use crate::glob::FilePatterns;
use crate::glob::PathOrPatternSet;
use crate::package_json::PackageJson;
use crate::package_json::PackageJsonReadError;
use crate::util::is_skippable_io_error;
use crate::util::specifier_to_file_path;
use crate::LintConfig;
use crate::LintRulesConfig;
use crate::SpecifierToFilePathError;

#[derive(Debug, Error)]
pub enum ResolveWorkspaceMemberError {
  #[error("Could not find config file for workspace member in '{}'.", .dir_url)]
  NotFound { dir_url: Url },
  #[error(transparent)]
  ConfigReadError(#[from] ConfigFileReadError),
  #[error(transparent)]
  PackageJsonReadError(#[from] PackageJsonReadError),
}

#[derive(Debug, Error)]
pub enum WorkspaceDiscoverError {
  #[error(transparent)]
  ConfigRead(#[from] ConfigFileReadError),
  #[error(transparent)]
  PackageJsonReadError(#[from] PackageJsonReadError),
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

pub struct WorkspaceDiscoverOptions<'a> {
  pub fs: &'a dyn crate::fs::DenoConfigFs,
  pub start: &'a Path,
  pub config_parse_options: &'a ConfigParseOptions,
  pub additional_config_file_names: &'a [&'a str],
  pub discover_pkg_json: bool,
}

#[derive(Debug, Default, Clone)]
pub struct FolderConfigs {
  pub config: Option<Arc<ConfigFile>>,
  pub pkg_json: Option<Arc<PackageJson>>,
}

#[derive(Debug)]
pub struct Workspace {
  root_dir: Url,
  config_folders: IndexMap<Url, FolderConfigs>,
}

impl Workspace {
  pub fn discover(
    opts: &WorkspaceDiscoverOptions,
  ) -> Result<Self, WorkspaceDiscoverError> {
    let config_file_discovery = discover_workspace_config_files(opts)?;
    let maybe_npm_discovery = if opts.discover_pkg_json {
      discover_with_npm(&config_file_discovery, opts)?
    } else {
      PackageJsonDiscovery::None
    };

    // todo(THIS PR): REMOVE
    // let root_dir = match &config_file_discovery {
    //   ConfigFileDiscovery::None => {
    //     //
    //     match &maybe_npm_discovery {
    //       PackageJsonDiscovery::None => {
    //         Url::from_directory_path(opts.start).unwrap()
    //       }
    //       PackageJsonDiscovery::Single(pkg_json)
    //       | PackageJsonDiscovery::Workspace { root: pkg_json, .. } => {
    //         Url::from_directory_path(&pkg_json.path.parent().unwrap()).unwrap()
    //       }
    //     }
    //   }
    //   ConfigFileDiscovery::Workspace { root: config, .. }
    //   | ConfigFileDiscovery::Single(config) => {
    //     // the npm lookup won't look further than this directory
    //     let config_file_path = specifier_to_file_path(&config.specifier)?;
    //     Url::from_directory_path(&config_file_path.parent().unwrap()).unwrap()
    //   }
    // };

    let mut workspace = match config_file_discovery {
      ConfigFileDiscovery::None => {
        let root_dir = Url::from_directory_path(opts.start).unwrap();
        Workspace {
          config_folders: IndexMap::from([(
            root_dir.clone(),
            FolderConfigs::default(),
          )]),
          root_dir,
        }
      }
      ConfigFileDiscovery::Single(config) => {
        let config_file_path = specifier_to_file_path(&config.specifier)?;
        let root_dir = config_file_path.parent().unwrap();
        let root_dir = Url::from_directory_path(&root_dir).unwrap();
        Workspace {
          config_folders: IndexMap::from([(
            root_dir.clone(),
            FolderConfigs {
              config: Some(config),
              pkg_json: None,
            },
          )]),
          root_dir,
        }
      }
      ConfigFileDiscovery::Workspace { root, members } => {
        let root_config_file_path = specifier_to_file_path(&root.specifier)?;
        let root_dir = root_config_file_path.parent().unwrap();
        let root_dir = Url::from_directory_path(&root_dir).unwrap();
        let mut config_folders = members
          .into_iter()
          .map(|(folder_url, config)| {
            (
              folder_url,
              match config {
                DenoOrPkgJson::Deno(config_file) => FolderConfigs {
                  config: Some(config_file),
                  pkg_json: None,
                },
                DenoOrPkgJson::PkgJson(pkg_json) => FolderConfigs {
                  config: None,
                  pkg_json: Some(pkg_json),
                },
              },
            )
          })
          .collect::<IndexMap<_, _>>();
        config_folders.entry(root_dir.clone()).or_default().config = Some(root);
        Workspace {
          root_dir,
          config_folders,
        }
      }
    };
    match maybe_npm_discovery {
      PackageJsonDiscovery::Single(pkg_json) => {
        let pkg_json_dir =
          Url::from_directory_path(&pkg_json.path.parent().unwrap()).unwrap();
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
        let pkg_json_dir =
          Url::from_directory_path(&root.path.parent().unwrap()).unwrap();
        if workspace
          .root_dir
          .as_str()
          .starts_with(pkg_json_dir.as_str())
        {
          // the package.json was in a higher up directory
          workspace.root_dir = pkg_json_dir;
        }

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

    Ok(workspace)
  }

  /// Resolves a workspace member's context, which can be used for deriving
  /// configuration specific to a member.
  pub fn resolve_member_ctxt(
    &self,
    specifier: &Url,
  ) -> WorkspaceMemberContext<'_> {
    let maybe_folder = self.resolve_folder(specifier);
    match maybe_folder {
      Some((member_url, folder)) => {
        if member_url == &self.root_dir {
          WorkspaceMemberContext::create_from_root_folder(folder)
        } else {
          let maybe_deno_json = folder
            .config
            .as_ref()
            .map(|c| (member_url, c))
            .or_else(|| {
              let parent = parent_specifier_str(member_url.as_str())?;
              self.resolve_deno_json_str(parent)
            })
            .or_else(|| {
              let root = self.config_folders.get(&self.root_dir).unwrap();
              root.config.as_ref().map(|c| (&self.root_dir, c))
            });
          WorkspaceMemberContext {
            pkg_json: folder.pkg_json.as_ref(),
            deno_json: maybe_deno_json.map(|(member_url, config)| {
              DenoJsonWorkspaceMemberContext {
                root: if self.root_dir == *member_url {
                  None
                } else {
                  self
                    .config_folders
                    .get(&self.root_dir)
                    .unwrap()
                    .config
                    .as_ref()
                },
                member: config,
              }
            }),
          }
        }
      }
      None => {
        let root = self.config_folders.get(&self.root_dir).unwrap();
        WorkspaceMemberContext::create_from_root_folder(root)
      }
    }
  }

  pub fn resolve_deno_json(
    &self,
    specifier: &Url,
  ) -> Option<(&Url, &Arc<ConfigFile>)> {
    self.resolve_deno_json_str(specifier.as_str())
  }

  fn resolve_deno_json_str<'a>(
    &self,
    specifier: &str,
  ) -> Option<(&Url, &Arc<ConfigFile>)> {
    let mut specifier = specifier;
    if !specifier.ends_with('/') {
      specifier = parent_specifier_str(specifier)?;
    }
    loop {
      let (folder_url, config) = self.resolve_folder_str(specifier)?;
      if let Some(config) = config.config.as_ref() {
        return Some((folder_url, config));
      }
      specifier = parent_specifier_str(folder_url.as_str())?;
    }
  }

  pub fn root_folder(&self) -> (&Url, &FolderConfigs) {
    (
      &self.root_dir,
      self.config_folders.get(&self.root_dir).unwrap(),
    )
  }

  pub fn resolve_folder(
    &self,
    specifier: &Url,
  ) -> Option<(&Url, &FolderConfigs)> {
    self.resolve_folder_str(specifier.as_str())
  }

  fn resolve_folder_str(
    &self,
    specifier: &str,
  ) -> Option<(&Url, &FolderConfigs)> {
    let mut best_match: Option<(&Url, &FolderConfigs)> = None;
    // it would be nice if we could store this config_folders relative to
    // the root, but the members might appear outside the root folder
    for (dir_url, config) in &self.config_folders {
      if specifier.starts_with(dir_url.as_str()) {
        if best_match.is_none()
          || dir_url.as_str().len() > best_match.unwrap().0.as_str().len()
        {
          best_match = Some((dir_url, config));
        }
      }
    }
    best_match
  }

  pub fn to_import_map_specifier(&self) -> Result<Option<Url>, AnyError> {
    // only allowed workspace and not in any package
    self
      .with_root_config_only(|found_config| {
        found_config.to_import_map_specifier()
      }, |other_config| {
        if other_config.json.import_map.is_some() {
          log::warn!(
            "{}",
            deno_terminal::colors::yellow(
              format!(
                "The 'importMap' option can only be specified in the root workspace deno.json file.\n    at {}",
                other_config.specifier
              )
            )
          );
        }
      })
      .unwrap_or(Ok(None))
  }

  fn with_root_config_only<R>(
    &self,
    on_found: impl Fn(&ConfigFile) -> R,
    on_other: impl Fn(&ConfigFile) -> (),
  ) -> Option<R> {
    let mut maybe_result = None;
    let mut found_result = false;
    for (dir_url, config) in &self.config_folders {
      if !found_result && dir_url == &self.root_dir {
        maybe_result = config.config.as_ref().map(|c| on_found(c));
        found_result = true;
      } else {
        if let Some(config) = &config.config {
          on_other(config);
        }
      }
    }
    maybe_result
  }
}

struct DenoJsonWorkspaceMemberContext<'a> {
  member: &'a Arc<ConfigFile>,
  // will be None when it doesn't exist or the member deno.json
  // is the root deno.json
  root: Option<&'a Arc<ConfigFile>>,
}

pub struct WorkspaceMemberContext<'a> {
  pkg_json: Option<&'a Arc<PackageJson>>,
  deno_json: Option<DenoJsonWorkspaceMemberContext<'a>>,
}

impl<'a> WorkspaceMemberContext<'a> {
  fn create_from_root_folder(root_folder: &'a FolderConfigs) -> Self {
    WorkspaceMemberContext {
      pkg_json: root_folder.pkg_json.as_ref(),
      deno_json: root_folder.config.as_ref().map(|config| {
        DenoJsonWorkspaceMemberContext {
          member: config,
          root: None,
        }
      }),
    }
  }

  pub fn to_lint_config(&self) -> Result<Option<LintConfig>, AnyError> {
    let Some(deno_json) = self.deno_json.as_ref() else {
      return Ok(None);
    };
    let mut maybe_member_config = deno_json.member.to_lint_config()?;
    let mut maybe_root_config = match &deno_json.root {
      Some(root) => root.to_lint_config()?,
      None => None,
    };
    let Some(member_config) = maybe_member_config else {
      return Ok(maybe_root_config);
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
        include: combine_option_vecs(
          root_config.rules.include,
          member_config.rules.include,
        ),
        exclude: combine_option_vecs(
          root_config.rules.exclude,
          member_config.rules.exclude,
        ),
      },
      files: combine_patterns(root_config.files, member_config.files),
      report: member_config.report.or(root_config.report),
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

fn combine_option_vecs<T>(
  root_option: Option<Vec<T>>,
  member_option: Option<Vec<T>>,
) -> Option<Vec<T>> {
  match (root_option, member_option) {
    (Some(root), Some(member)) => {
      Some(root.into_iter().chain(member).collect())
    }
    (Some(root), None) => Some(root),
    (None, Some(member)) => Some(member),
    (None, None) => None,
  }
}

#[derive(Debug)]
pub enum DenoOrPkgJson {
  Deno(Arc<ConfigFile>),
  PkgJson(Arc<crate::package_json::PackageJson>),
}

enum ConfigFileDiscovery {
  None,
  Single(Arc<ConfigFile>),
  Workspace {
    root: Arc<ConfigFile>,
    members: BTreeMap<Url, DenoOrPkgJson>,
  },
}

fn discover_workspace_config_files(
  opts: &WorkspaceDiscoverOptions,
) -> Result<ConfigFileDiscovery, WorkspaceDiscoverError> {
  // todo(dsherret): we can remove this checked hashset
  let mut checked = HashSet::new();
  let mut start = Some(Cow::Borrowed(opts.start));
  let mut first_config_file: Option<Url> = None;
  let mut found_configs: HashMap<_, ConfigFile> = HashMap::new();
  loop {
    let config_file = ConfigFile::discover_from(
      opts.fs,
      start.as_ref().unwrap(),
      &mut checked,
      opts.additional_config_file_names,
      opts.config_parse_options,
    )?;
    if let Some(workspace_config_file) = config_file {
      if let Some(members) = &workspace_config_file.json.workspace {
        if members.is_empty() {
          return Err(WorkspaceDiscoverError::MembersEmpty(
            workspace_config_file.specifier.clone(),
          ));
        }
        let config_file_path =
          specifier_to_file_path(&workspace_config_file.specifier).unwrap();
        let config_file_directory = config_file_path.parent().unwrap();
        let config_file_directory_url =
          Url::from_directory_path(config_file_directory).unwrap();
        let mut final_members = BTreeMap::new();
        for raw_member in members {
          let mut find_config = |member_dir_url: &Url| {
            let config_file_names = ConfigFile::resolve_config_file_names(
              opts.additional_config_file_names,
            );
            let config_file_urls = config_file_names
              .iter()
              .map(|name| member_dir_url.join(name).unwrap())
              .collect::<Vec<_>>();
            // try to find the config in memory from the configs we already
            // found on the file system
            if !found_configs.is_empty() {
              for url in &config_file_urls {
                if let Some(config_file) = found_configs.remove(url) {
                  return Ok(DenoOrPkgJson::Deno(Arc::new(config_file)));
                }
              }
            }

            // now search the file system
            for url in config_file_urls {
              let result = ConfigFile::from_specifier(
                opts.fs,
                url,
                opts.config_parse_options,
              );
              match result {
                Ok(config_file) => {
                  return Ok(DenoOrPkgJson::Deno(Arc::new(config_file)));
                }
                Err(err) if err.is_not_found() => {
                  // keep searching
                }
                Err(err) => return Err(err.into()),
              }
            }

            // now check for a package.json
            let package_json_url = member_dir_url.join("package.json").unwrap();
            let package_json_path =
              specifier_to_file_path(&package_json_url).unwrap();
            match opts.fs.read_to_string(&package_json_path) {
              Ok(file_text) => Ok(DenoOrPkgJson::PkgJson(Arc::new(
                PackageJson::load_from_string(package_json_path, file_text)?,
              ))),
              Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
                Err(ResolveWorkspaceMemberError::NotFound {
                  dir_url: member_dir_url.clone(),
                })
              }
              Err(err) => Err(
                PackageJsonReadError::Io {
                  path: package_json_path,
                  source: err,
                }
                .into(),
              ),
            }
          };

          let member = if !raw_member.ends_with('/') {
            Cow::Owned(format!("{}/", raw_member))
          } else {
            Cow::Borrowed(raw_member)
          };
          let member_dir_url = config_file_directory_url
            .join(&member)
            .map_err(|err| WorkspaceDiscoverError::InvalidMember {
              base: workspace_config_file.specifier.clone(),
              member: raw_member.clone(),
              source: err,
            })?;
          let config = find_config(&member_dir_url)?;
          final_members.insert(member_dir_url, config);
        }
        if let Some(config_url) = found_configs.into_keys().next() {
          return Err(WorkspaceDiscoverError::ConfigNotWorkspaceMember {
            workspace_url: workspace_config_file.specifier.clone(),
            config_url,
          });
        }
        return Ok(ConfigFileDiscovery::Workspace {
          root: Arc::new(workspace_config_file),
          members: final_members,
        });
      } else {
        if first_config_file.is_none() {
          first_config_file = Some(workspace_config_file.specifier.clone());
        }
        start = specifier_to_file_path(&workspace_config_file.specifier)?
          .parent()
          .and_then(|p| p.parent())
          .map(|p| Cow::Owned(p.to_owned()));
        found_configs.insert(
          workspace_config_file.specifier.clone(),
          workspace_config_file,
        );
      }
    } else {
      break;
    }
  }

  if let Some(first_config_file) = first_config_file {
    let config = found_configs.remove(&first_config_file).unwrap();
    Ok(ConfigFileDiscovery::Single(Arc::new(config)))
  } else {
    Ok(ConfigFileDiscovery::None)
  }
}

enum PackageJsonDiscovery {
  None,
  Single(Arc<PackageJson>),
  Workspace {
    root: Arc<PackageJson>,
    members: BTreeMap<Url, Arc<PackageJson>>,
  },
}

fn discover_with_npm(
  config_file_discovery: &ConfigFileDiscovery,
  opts: &WorkspaceDiscoverOptions,
) -> Result<PackageJsonDiscovery, WorkspaceDiscoverError> {
  let mut found_configs: HashMap<_, PackageJson> = HashMap::new();
  let mut first_config_file = None;
  let maybe_stop_config_file_path = match &config_file_discovery {
    ConfigFileDiscovery::None => None,
    ConfigFileDiscovery::Single(config_file) => {
      Some(specifier_to_file_path(&config_file.specifier).unwrap())
    }
    ConfigFileDiscovery::Workspace { root, .. } => {
      Some(specifier_to_file_path(&root.specifier).unwrap())
    }
  };
  let maybe_stop_dir = maybe_stop_config_file_path
    .as_ref()
    .and_then(|p| p.parent());
  for ancestor in opts.start.ancestors() {
    if Some(ancestor) == maybe_stop_dir {
      break;
    }
    let pkg_json_path = ancestor.join("package.json");
    let text = match opts.fs.read_to_string(&pkg_json_path) {
      Ok(text) => text,
      Err(err) if is_skippable_io_error(&err) => {
        continue; // keep going
      }
      Err(err) => {
        return Err(
          PackageJsonReadError::Io {
            path: pkg_json_path,
            source: err,
          }
          .into(),
        );
      }
    };
    let pkg_json = PackageJson::load_from_string(pkg_json_path, text)?;
    if let Some(members) = &pkg_json.workspaces {
      let mut has_warned = false;
      let mut final_members = BTreeMap::new();
      for member in members {
        if member.contains('*') {
          if !has_warned {
            has_warned = true;
            log::warn!(
              "Wildcards in npm workspaces are not yet supported. Ignoring."
            );
          }
          continue;
        }

        let mut find_config = || {
          let pkg_json_path = ancestor.join(member).join("package.json");
          // try to find the package.json in memory from what we already
          // found on the file system
          if let Some(pkg_json) = found_configs.remove(&pkg_json_path) {
            return Ok(pkg_json);
          }

          // now search the file system
          let text = match opts.fs.read_to_string(&pkg_json_path) {
            Ok(text) => text,
            Err(err) => {
              return Err(PackageJsonReadError::Io {
                path: pkg_json_path,
                source: err,
              });
            }
          };
          PackageJson::load_from_string(pkg_json_path, text)
        };

        let pkg_json = match find_config() {
          Ok(config) => config,
          Err(err) => {
            log::warn!("Failed loading package.json, but ignoring. {:#}", err);
            continue;
          }
        };
        final_members.insert(
          Url::from_file_path(&pkg_json.path).unwrap(),
          Arc::new(pkg_json),
        );
      }

      // just include any remaining found configs as workspace members
      // instead of erroring for now
      for (path, config) in found_configs {
        let url = Url::from_file_path(&path).unwrap();
        final_members.insert(url, Arc::new(config));
      }

      return Ok(PackageJsonDiscovery::Workspace {
        root: Arc::new(pkg_json),
        members: final_members,
      });
    } else {
      if first_config_file.is_none() {
        first_config_file = Some(pkg_json.path.clone());
      }
      found_configs.insert(pkg_json.path.clone(), pkg_json);
    }
  }

  if let Some(first_config_file) = first_config_file {
    let config = found_configs.remove(&first_config_file).unwrap();
    Ok(PackageJsonDiscovery::Single(Arc::new(config)))
  } else {
    Ok(PackageJsonDiscovery::None)
  }
}

fn parent_specifier_str(specifier: &str) -> Option<&str> {
  let specifier = specifier.strip_suffix('/').unwrap_or(specifier);
  if let Some(index) = specifier.rfind('/') {
    Some(&specifier[..index + 1])
  } else {
    None
  }
}
