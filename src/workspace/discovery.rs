// Copyright 2018-2024 the Deno authors. MIT license.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::path::Path;
use std::path::PathBuf;

use indexmap::IndexSet;
use url::Url;

use crate::glob::is_glob_pattern;
use crate::glob::FileCollector;
use crate::glob::FilePatterns;
use crate::glob::PathOrPattern;
use crate::glob::PathOrPatternSet;
use crate::package_json::PackageJson;
use crate::package_json::PackageJsonLoadError;
use crate::package_json::PackageJsonRc;
use crate::sync::new_rc;
use crate::util::is_skippable_io_error;
use crate::util::specifier_parent;
use crate::ConfigFile;
use crate::ConfigFileRc;

use super::ResolveWorkspaceMemberError;
use super::UrlRc;
use super::VendorEnablement;
use super::WorkspaceDiscoverError;
use super::WorkspaceDiscoverErrorKind;
use super::WorkspaceDiscoverOptions;
use super::WorkspaceDiscoverStart;

#[derive(Debug)]
pub enum DenoOrPkgJson {
  Deno(ConfigFileRc),
  PkgJson(crate::package_json::PackageJsonRc),
}

impl DenoOrPkgJson {
  pub fn specifier(&self) -> Cow<Url> {
    match self {
      Self::Deno(config) => Cow::Borrowed(&config.specifier),
      Self::PkgJson(pkg_json) => Cow::Owned(pkg_json.specifier()),
    }
  }
}

#[derive(Debug)]
pub enum ConfigFolder {
  Single(DenoOrPkgJson),
  Both {
    deno_json: ConfigFileRc,
    pkg_json: PackageJsonRc,
  },
}

impl ConfigFolder {
  pub fn folder_url(&self) -> Url {
    match self {
      Self::Single(DenoOrPkgJson::Deno(config)) => {
        specifier_parent(&config.specifier)
      }
      Self::Single(DenoOrPkgJson::PkgJson(pkg_json)) => {
        Url::from_directory_path(pkg_json.path.parent().unwrap()).unwrap()
      }
      Self::Both { deno_json, .. } => specifier_parent(&deno_json.specifier),
    }
  }

  pub fn is_workspace(&self) -> bool {
    match self {
      Self::Single(DenoOrPkgJson::Deno(config)) => {
        config.json.workspace.is_some()
      }
      Self::Single(DenoOrPkgJson::PkgJson(pkg_json)) => {
        pkg_json.workspaces.is_some()
      }
      Self::Both {
        deno_json,
        pkg_json,
      } => deno_json.json.workspace.is_some() || pkg_json.workspaces.is_some(),
    }
  }

  pub fn deno_json(&self) -> Option<&ConfigFileRc> {
    match self {
      Self::Single(DenoOrPkgJson::Deno(deno_json)) => Some(deno_json),
      Self::Both { deno_json, .. } => Some(deno_json),
      _ => None,
    }
  }

  pub fn pkg_json(&self) -> Option<&PackageJsonRc> {
    match self {
      Self::Single(DenoOrPkgJson::PkgJson(pkg_json)) => Some(pkg_json),
      Self::Both { pkg_json, .. } => Some(pkg_json),
      _ => None,
    }
  }

  pub fn from_maybe_both(
    maybe_deno_json: Option<ConfigFileRc>,
    maybe_pkg_json: Option<PackageJsonRc>,
  ) -> Option<Self> {
    match (maybe_deno_json, maybe_pkg_json) {
      (Some(deno_json), Some(pkg_json)) => Some(Self::Both {
        deno_json,
        pkg_json,
      }),
      (Some(deno_json), None) => {
        Some(Self::Single(DenoOrPkgJson::Deno(deno_json)))
      }
      (None, Some(pkg_json)) => {
        Some(Self::Single(DenoOrPkgJson::PkgJson(pkg_json)))
      }
      (None, None) => None,
    }
  }
}

#[derive(Debug)]
pub enum ConfigFileDiscovery {
  None {
    maybe_vendor_dir: Option<PathBuf>,
  },
  Single {
    config_folder: ConfigFolder,
    maybe_vendor_dir: Option<PathBuf>,
  },
  Workspace {
    root: ConfigFolder,
    members: BTreeMap<UrlRc, ConfigFolder>,
    maybe_vendor_dir: Option<PathBuf>,
  },
}

impl ConfigFileDiscovery {
  fn root_config_specifier(&self) -> Option<Cow<Url>> {
    match self {
      Self::None { .. } => None,
      Self::Single { config_folder, .. } => {
        Some(config_folder_config_specifier(config_folder))
      }
      Self::Workspace { root, .. } => {
        Some(config_folder_config_specifier(root))
      }
    }
  }
}

fn config_folder_config_specifier(res: &ConfigFolder) -> Cow<Url> {
  match res {
    ConfigFolder::Single(config) => config.specifier(),
    ConfigFolder::Both { deno_json, .. } => Cow::Borrowed(&deno_json.specifier),
  }
}

pub fn discover_workspace_config_files(
  start: WorkspaceDiscoverStart,
  opts: &WorkspaceDiscoverOptions,
) -> Result<ConfigFileDiscovery, WorkspaceDiscoverError> {
  match start {
    WorkspaceDiscoverStart::Paths(dirs) => match dirs.len() {
      0 => Ok(ConfigFileDiscovery::None {
        maybe_vendor_dir: resolve_vendor_dir(
          None,
          opts.maybe_vendor_override.as_ref(),
        ),
      }),
      1 => {
        let dir = &dirs[0];
        let start = DirOrConfigFile::Dir(dir);
        discover_workspace_config_files_for_single_dir(start, opts, None)
      }
      _ => {
        let mut checked = HashSet::default();
        let mut final_workspace = ConfigFileDiscovery::None {
          maybe_vendor_dir: resolve_vendor_dir(
            None,
            opts.maybe_vendor_override.as_ref(),
          ),
        };
        for dir in dirs {
          let workspace = discover_workspace_config_files_for_single_dir(
            DirOrConfigFile::Dir(dir),
            opts,
            Some(&mut checked),
          )?;
          if let Some(root_config_specifier) = workspace.root_config_specifier()
          {
            if let Some(final_workspace_config_specifier) =
              final_workspace.root_config_specifier()
            {
              return Err(WorkspaceDiscoverError(
                WorkspaceDiscoverErrorKind::MultipleWorkspaces {
                  base_workspace_url: final_workspace_config_specifier
                    .into_owned(),
                  other_workspace_url: root_config_specifier.into_owned(),
                }
                .into(),
              ));
            }
            final_workspace = workspace;
          }
        }
        Ok(final_workspace)
      }
    },
    WorkspaceDiscoverStart::ConfigFile(file) => {
      let start = DirOrConfigFile::ConfigFile(file);
      discover_workspace_config_files_for_single_dir(start, opts, None)
    }
  }
}

#[derive(Debug, Clone, Copy)]
enum DirOrConfigFile<'a> {
  Dir(&'a Path),
  ConfigFile(&'a Path),
}

fn discover_workspace_config_files_for_single_dir(
  start: DirOrConfigFile,
  opts: &WorkspaceDiscoverOptions,
  mut checked: Option<&mut HashSet<PathBuf>>,
) -> Result<ConfigFileDiscovery, WorkspaceDiscoverError> {
  fn strip_up_to_node_modules(path: &Path) -> PathBuf {
    path
      .components()
      .take_while(|component| match component {
        std::path::Component::Normal(name) => {
          name.to_string_lossy() != "node_modules"
        }
        _ => true,
      })
      .collect()
  }

  let start_dir: Option<&Path>;
  let mut first_config_folder_url: Option<Url> = None;
  let mut found_config_folders: HashMap<_, ConfigFolder> = HashMap::new();
  let config_file_names =
    ConfigFile::resolve_config_file_names(opts.additional_config_file_names);
  let load_pkg_json_in_folder = |folder_path: &Path| {
    if opts.discover_pkg_json {
      let pkg_json_path = folder_path.join("package.json");
      match PackageJson::load_from_path(
        &pkg_json_path,
        opts.fs,
        opts.pkg_json_cache,
      ) {
        Ok(pkg_json) => {
          log::debug!(
            "package.json file found at '{}'",
            pkg_json_path.display()
          );
          Ok(Some(pkg_json))
        }
        Err(PackageJsonLoadError::Io { source, .. })
          if is_skippable_io_error(&source) =>
        {
          Ok(None)
        }
        Err(err) => Err(err),
      }
    } else {
      Ok(None)
    }
  };
  let load_config_folder =
    |folder_path: &Path| -> Result<_, ResolveWorkspaceMemberError> {
      let maybe_config_file = ConfigFile::maybe_find_in_folder(
        opts.fs,
        folder_path,
        &config_file_names,
        &opts.config_parse_options,
      )?;
      let maybe_pkg_json = load_pkg_json_in_folder(folder_path)?;
      Ok(ConfigFolder::from_maybe_both(
        maybe_config_file.map(new_rc),
        maybe_pkg_json,
      ))
    };
  match start {
    DirOrConfigFile::Dir(dir) => {
      start_dir = Some(dir);
    }
    DirOrConfigFile::ConfigFile(file) => {
      let specifier = Url::from_file_path(file).unwrap();
      let config_file = new_rc(ConfigFile::from_specifier(
        opts.fs,
        specifier.clone(),
        &opts.config_parse_options,
      )?);
      let maybe_pkg_json = load_pkg_json_in_folder(&config_file.dir_path())?;
      let parent_dir_url = specifier_parent(&config_file.specifier);
      found_config_folders.insert(
        parent_dir_url.clone(),
        ConfigFolder::from_maybe_both(Some(config_file), maybe_pkg_json)
          .unwrap(),
      );
      first_config_folder_url = Some(parent_dir_url);
      // start searching for a workspace in the parent directory
      start_dir = file.parent().and_then(|p| p.parent());
    }
  }
  // do not auto-discover inside the node_modules folder (ex. when a
  // user is running something directly within there)
  let start_dir = start_dir.map(strip_up_to_node_modules);
  for current_dir in start_dir.iter().flat_map(|p| p.ancestors()) {
    if let Some(checked) = checked.as_mut() {
      if !checked.insert(current_dir.to_path_buf()) {
        // already visited here, so exit
        return Ok(ConfigFileDiscovery::None {
          maybe_vendor_dir: resolve_vendor_dir(
            None,
            opts.maybe_vendor_override.as_ref(),
          ),
        });
      }
    }

    let maybe_config_folder = load_config_folder(current_dir)?;
    let Some(root_config_folder) = maybe_config_folder else {
      continue;
    };
    if root_config_folder.is_workspace() {
      let maybe_vendor_dir = resolve_vendor_dir(
        Some(&root_config_folder),
        opts.maybe_vendor_override.as_ref(),
      );
      let mut final_members = BTreeMap::new();
      let root_config_file_directory_url = root_config_folder.folder_url();
      let resolve_member_url =
        |raw_member: &str| -> Result<Url, ResolveWorkspaceMemberError> {
          let member = ensure_trailing_slash(raw_member);
          let member_dir_url = root_config_file_directory_url
            .join(&member)
            .map_err(|err| ResolveWorkspaceMemberError::InvalidMember {
              base: root_config_folder.folder_url(),
              member: raw_member.to_owned(),
              source: err,
            })?;
          Ok(member_dir_url)
        };
      let validate_member_url =
        |raw_member: &str,
         member_dir_url: &Url|
         -> Result<(), ResolveWorkspaceMemberError> {
          if *member_dir_url == root_config_file_directory_url {
            return Err(ResolveWorkspaceMemberError::InvalidSelfReference {
              member: raw_member.to_string(),
            });
          }
          if !member_dir_url
            .as_str()
            .starts_with(root_config_file_directory_url.as_str())
          {
            return Err(ResolveWorkspaceMemberError::NonDescendant {
              workspace_url: root_config_file_directory_url.clone(),
              member_url: member_dir_url.clone(),
            });
          }
          Ok(())
        };
      let mut find_member_config_folder =
        |member_dir_url: &Url| -> Result<_, ResolveWorkspaceMemberError> {
          // try to find the config folder in memory from the configs we already
          // found on the file system
          if let Some(config_folder) =
            found_config_folders.remove(member_dir_url)
          {
            return Ok(config_folder);
          }

          let maybe_config_folder =
            load_config_folder(&member_dir_url.to_file_path().unwrap())?;
          maybe_config_folder.ok_or_else(|| {
            // it's fine this doesn't use all the possible config file names
            // as this is only used to enhance the error message
            if member_dir_url.as_str().ends_with("/deno.json/")
              || member_dir_url.as_str().ends_with("/deno.jsonc/")
              || member_dir_url.as_str().ends_with("/package.json/")
            {
              ResolveWorkspaceMemberError::NotFoundMaybeSpecifiedFile {
                dir_url: member_dir_url.clone(),
              }
            } else {
              ResolveWorkspaceMemberError::NotFound {
                dir_url: member_dir_url.clone(),
              }
            }
          })
        };
      let mut add_member = |raw_member: &str,
                            member_dir_url: Url,
                            member_config_folder: ConfigFolder|
       -> Result<(), ResolveWorkspaceMemberError> {
        let previous_member =
          final_members.insert(new_rc(member_dir_url), member_config_folder);
        if previous_member.is_some() {
          Err(ResolveWorkspaceMemberError::Duplicate {
            member: raw_member.to_string(),
          })
        } else {
          Ok(())
        }
      };
      if let Some(deno_json) = root_config_folder.deno_json() {
        if let Some(members) = &deno_json.json.workspace {
          if members.is_empty() {
            return Err(
              WorkspaceDiscoverErrorKind::MembersEmpty(
                deno_json.specifier.clone(),
              )
              .into(),
            );
          }
          for raw_member in members {
            let member_dir_url = resolve_member_url(raw_member)?;
            validate_member_url(raw_member, &member_dir_url)?;
            let member_config_folder =
              find_member_config_folder(&member_dir_url)?;
            add_member(raw_member, member_dir_url, member_config_folder)?;
          }
        }
      }
      if let Some(pkg_json) = root_config_folder.pkg_json() {
        if let Some(members) = &pkg_json.workspaces {
          let (pattern_members, path_members): (Vec<_>, Vec<_>) =
            members.iter().partition(|member| {
              is_glob_pattern(member) || member.starts_with('!')
            });
          let patterns = pattern_members
            .iter()
            .map(|raw_member| {
              PathOrPattern::from_relative(
                pkg_json.dir_path(),
                &format!("{}package.json", ensure_trailing_slash(raw_member)),
              )
              .map_err(|err| {
                ResolveWorkspaceMemberError::NpmMemberToPattern {
                  base: root_config_file_directory_url.clone(),
                  member: raw_member.to_string(),
                  source: err,
                }
              })
            })
            .collect::<Result<Vec<_>, _>>()?;
          let pkg_json_paths = if patterns.is_empty() {
            Vec::new()
          } else {
            FileCollector::new(|_| true)
              .ignore_git_folder()
              .ignore_node_modules()
              .set_vendor_folder(maybe_vendor_dir.clone())
              .collect_file_patterns(
                opts.fs,
                FilePatterns {
                  base: pkg_json.dir_path().to_path_buf(),
                  include: Some(PathOrPatternSet::new(patterns)),
                  exclude: PathOrPatternSet::new(Vec::new()),
                },
              )
              .map_err(|err| {
                WorkspaceDiscoverErrorKind::FailedCollectingNpmMembers {
                  package_json_url: pkg_json.specifier(),
                  source: err,
                }
              })?
          };
          let mut member_dir_urls =
            IndexSet::with_capacity(path_members.len() + pkg_json_paths.len());
          for path_member in path_members {
            let member_dir_url = resolve_member_url(path_member)?;
            member_dir_urls.insert(member_dir_url);
          }
          for pkg_json_path in pkg_json_paths {
            let member_dir_url =
              Url::from_directory_path(pkg_json_path.parent().unwrap())
                .unwrap();
            member_dir_urls.insert(member_dir_url);
          }

          for member_dir_url in member_dir_urls {
            validate_member_url("<npm workspace member>", &member_dir_url)?;
            let member_config_folder =
              match find_member_config_folder(&member_dir_url) {
                Ok(config_folder) => config_folder,
                Err(ResolveWorkspaceMemberError::NotFound { dir_url }) => {
                  // enhance the error to say we didn't find a package.json
                  return Err(
                    ResolveWorkspaceMemberError::NotFoundPackageJson {
                      dir_url,
                    }
                    .into(),
                  );
                }
                Err(err) => return Err(err.into()),
              };
            if member_config_folder.pkg_json().is_none() {
              return Err(
                ResolveWorkspaceMemberError::NotFoundPackageJson {
                  dir_url: member_dir_url,
                }
                .into(),
              );
            }
            match add_member(
              "<npm workspace member>",
              member_dir_url,
              member_config_folder,
            ) {
              Ok(()) => {}
              Err(ResolveWorkspaceMemberError::Duplicate { .. }) => {
                // ignore for package.json members
              }
              Err(err) => return Err(err.into()),
            }
          }
        }
      }

      // just include any remaining found configs as workspace members
      // instead of erroring for now
      let is_root_deno_json_workspace = root_config_folder
        .deno_json()
        .map(|d| d.json.workspace.is_some())
        .unwrap_or(false);
      for (url, config_folder) in found_config_folders {
        if is_root_deno_json_workspace {
          return Err(
            WorkspaceDiscoverErrorKind::ConfigNotWorkspaceMember {
              workspace_url: root_config_folder.folder_url(),
              config_url: config_folder_config_specifier(&config_folder)
                .into_owned(),
            }
            .into(),
          );
        } else {
          // otherwise, be lenient and just add it to the workspace
          let url = new_rc(url);
          final_members.insert(url, config_folder);
        }
      }

      // ensure no duplicate names in deno configuration files
      let mut seen_names: HashMap<&str, &Url> =
        HashMap::with_capacity(final_members.len() + 1);
      for folder in
        std::iter::once(&root_config_folder).chain(final_members.values())
      {
        if let Some(deno_json) = folder.deno_json() {
          if let Some(name) = deno_json.json.name.as_deref() {
            if let Some(other_member_url) = seen_names.get(name) {
              return Err(
                ResolveWorkspaceMemberError::DuplicatePackageName {
                  name: name.to_string(),
                  deno_json_url: deno_json.specifier.clone(),
                  other_deno_json_url: (*other_member_url).clone(),
                }
                .into(),
              );
            } else {
              seen_names.insert(name, &deno_json.specifier);
            }
          }
        }
      }

      return Ok(ConfigFileDiscovery::Workspace {
        root: root_config_folder,
        members: final_members,
        maybe_vendor_dir,
      });
    }

    let config_folder_url = root_config_folder.folder_url();
    if first_config_folder_url.is_none() {
      first_config_folder_url = Some(config_folder_url.clone());
    }
    found_config_folders.insert(config_folder_url, root_config_folder);
  }

  if let Some(first_config_folder_url) = first_config_folder_url {
    let config_folder = found_config_folders
      .remove(&first_config_folder_url)
      .unwrap();
    let maybe_vendor_dir = resolve_vendor_dir(
      Some(&config_folder),
      opts.maybe_vendor_override.as_ref(),
    );
    Ok(ConfigFileDiscovery::Single {
      config_folder,
      maybe_vendor_dir,
    })
  } else {
    Ok(ConfigFileDiscovery::None {
      maybe_vendor_dir: resolve_vendor_dir(
        None,
        opts.maybe_vendor_override.as_ref(),
      ),
    })
  }
}

fn resolve_vendor_dir(
  maybe_config_folder: Option<&ConfigFolder>,
  maybe_vendor_override: Option<&VendorEnablement>,
) -> Option<PathBuf> {
  match maybe_config_folder {
    Some(config_folder) => {
      if let Some(vendor_folder_override) = maybe_vendor_override {
        match vendor_folder_override {
          VendorEnablement::Disable => None,
          VendorEnablement::Enable { cwd } => match config_folder.deno_json() {
            Some(c) => Some(c.dir_path().join("vendor")),
            None => Some(cwd.join("vendor")),
          },
        }
      } else {
        let deno_json = config_folder.deno_json()?;
        if deno_json.vendor() == Some(true) {
          Some(deno_json.dir_path().join("vendor"))
        } else {
          None
        }
      }
    }
    None => match maybe_vendor_override {
      Some(VendorEnablement::Enable { cwd }) => Some(cwd.join("vendor")),
      _ => None,
    },
  }
}

fn ensure_trailing_slash(path: &str) -> Cow<str> {
  if !path.ends_with('/') {
    Cow::Owned(format!("{}/", path))
  } else {
    Cow::Borrowed(path)
  }
}
