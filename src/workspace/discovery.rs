// Copyright 2018-2024 the Deno authors. MIT license.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::path::Path;
use std::path::PathBuf;

use deno_package_json::PackageJson;
use deno_package_json::PackageJsonLoadError;
use deno_package_json::PackageJsonRc;
use deno_path_util::url_from_directory_path;
use deno_path_util::url_from_file_path;
use deno_path_util::url_parent;
use deno_path_util::url_to_file_path;
use indexmap::IndexSet;
use url::Url;

use crate::deno_json::ConfigFile;
use crate::deno_json::ConfigFileRc;
use crate::glob::is_glob_pattern;
use crate::glob::FileCollector;
use crate::glob::FilePatterns;
use crate::glob::PathOrPattern;
use crate::glob::PathOrPatternSet;
use crate::sync::new_rc;
use crate::util::is_skippable_io_error;
use crate::workspace::ConfigReadError;
use crate::workspace::Workspace;

use super::ResolveWorkspaceMemberError;
use super::ResolveWorkspacePatchError;
use super::UrlRc;
use super::VendorEnablement;
use super::WorkspaceDiscoverError;
use super::WorkspaceDiscoverErrorKind;
use super::WorkspaceDiscoverOptions;
use super::WorkspaceDiscoverStart;
use super::WorkspaceRc;

#[derive(Debug)]
pub enum DenoOrPkgJson {
  Deno(ConfigFileRc),
  PkgJson(PackageJsonRc),
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
        url_parent(&config.specifier)
      }
      Self::Single(DenoOrPkgJson::PkgJson(pkg_json)) => {
        url_from_directory_path(pkg_json.path.parent().unwrap()).unwrap()
      }
      Self::Both { deno_json, .. } => url_parent(&deno_json.specifier),
    }
  }

  pub fn has_workspace_members(&self) -> bool {
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
  None { maybe_vendor_dir: Option<PathBuf> },
  Workspace { workspace: WorkspaceRc },
}

impl ConfigFileDiscovery {
  fn root_config_specifier(&self) -> Option<Cow<Url>> {
    match self {
      Self::None { .. } => None,
      Self::Workspace { workspace, .. } => {
        let root_folder_configs = workspace.root_folder_configs();
        if let Some(deno_json) = &root_folder_configs.deno_json {
          return Some(Cow::Borrowed(&deno_json.specifier));
        }
        if let Some(pkg_json) = &root_folder_configs.pkg_json {
          return Some(Cow::Owned(pkg_json.specifier()));
        }
        None
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

  if opts.workspace_cache.is_some() {
    // it doesn't really make sense to use a workspace cache without config
    // caches because that would mean the configs might change between calls
    // causing strange behavior, so panic if someone does this
    assert!(
      opts.deno_json_cache.is_some() && opts.pkg_json_cache.is_some(),
      "Using a workspace cache requires setting the deno.json and package.json caches"
    );
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
        &crate::fs::DenoConfigPkgJsonAdapterFs(opts.fs),
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
  let load_config_folder = |folder_path: &Path| -> Result<_, ConfigReadError> {
    let maybe_config_file = ConfigFile::maybe_find_in_folder(
      opts.fs,
      opts.deno_json_cache,
      folder_path,
      &config_file_names,
      &opts.config_parse_options,
    )?;
    let maybe_pkg_json = load_pkg_json_in_folder(folder_path)?;
    Ok(ConfigFolder::from_maybe_both(
      maybe_config_file,
      maybe_pkg_json,
    ))
  };
  match start {
    DirOrConfigFile::Dir(dir) => {
      start_dir = Some(dir);
    }
    DirOrConfigFile::ConfigFile(file) => {
      let specifier = url_from_file_path(file).unwrap();
      let config_file = new_rc(
        ConfigFile::from_specifier(
          opts.fs,
          specifier.clone(),
          &opts.config_parse_options,
        )
        .map_err(ConfigReadError::DenoJsonRead)?,
      );

      // see what config would be loaded if we just specified the parent directory
      let natural_config_folder_result =
        load_config_folder(file.parent().unwrap());
      let matching_config_folder = match natural_config_folder_result {
        Ok(Some(natual_config_folder)) => {
          if natual_config_folder
            .deno_json()
            .is_some_and(|d| d.specifier == config_file.specifier)
          {
            Some(natual_config_folder)
          } else {
            None
          }
        }
        Ok(None) | Err(_) => None,
      };

      let parent_dir_url = url_parent(&config_file.specifier);
      let config_folder = match matching_config_folder {
        Some(config_folder) => config_folder,
        None => {
          // when loading the directory we would have loaded something else, so
          // don't try to load a workspace and don't store this information in
          // the workspace cache
          let config_folder =
            ConfigFolder::Single(DenoOrPkgJson::Deno(config_file));

          if config_folder.has_workspace_members() {
            return handle_workspace_folder_with_members(
              config_folder,
              Some(&parent_dir_url),
              opts,
              found_config_folders,
              &load_config_folder,
            );
          }

          let maybe_vendor_dir = resolve_vendor_dir(
            config_folder.deno_json().map(|d| d.as_ref()),
            opts.maybe_vendor_override.as_ref(),
          );
          let patches =
            resolve_patch_config_folders(&config_folder, load_config_folder)?;
          return Ok(ConfigFileDiscovery::Workspace {
            workspace: new_rc(Workspace::new(
              config_folder,
              Default::default(),
              patches,
              maybe_vendor_dir,
            )),
          });
        }
      };

      if let Some(workspace_cache) = &opts.workspace_cache {
        if let Some(workspace) = workspace_cache.get(&config_file.dir_path()) {
          if cfg!(debug_assertions) {
            let expected_vendor_dir = resolve_vendor_dir(
              config_folder.deno_json().map(|d| d.as_ref()),
              opts.maybe_vendor_override.as_ref(),
            );
            debug_assert_eq!(
              expected_vendor_dir, workspace.vendor_dir,
              "should not be using a different vendor dir across calls"
            );
          }
          return Ok(ConfigFileDiscovery::Workspace {
            workspace: workspace.clone(),
          });
        }
      }

      if config_folder.has_workspace_members() {
        return handle_workspace_folder_with_members(
          config_folder,
          Some(&parent_dir_url),
          opts,
          found_config_folders,
          &load_config_folder,
        );
      }

      found_config_folders.insert(parent_dir_url.clone(), config_folder);
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

    if let Some(workspace_with_members) = opts
      .workspace_cache
      .and_then(|c| c.get(current_dir))
      .filter(|w| w.config_folders.len() > 1)
    {
      if cfg!(debug_assertions) {
        let expected_vendor_dir = resolve_vendor_dir(
          workspace_with_members.root_deno_json().map(|d| d.as_ref()),
          opts.maybe_vendor_override.as_ref(),
        );
        debug_assert_eq!(
          expected_vendor_dir, workspace_with_members.vendor_dir,
          "should not be using a different vendor dir across calls"
        );
      }

      return handle_workspace_with_members(
        workspace_with_members,
        first_config_folder_url.as_ref(),
        found_config_folders,
        opts,
        load_config_folder,
      );
    }

    let maybe_config_folder = load_config_folder(current_dir)?;
    let Some(root_config_folder) = maybe_config_folder else {
      continue;
    };
    if root_config_folder.has_workspace_members() {
      return handle_workspace_folder_with_members(
        root_config_folder,
        first_config_folder_url.as_ref(),
        opts,
        found_config_folders,
        &load_config_folder,
      );
    }

    let config_folder_url = root_config_folder.folder_url();
    if first_config_folder_url.is_none() {
      if let Some(workspace_cache) = &opts.workspace_cache {
        if let Some(workspace) = workspace_cache.get(current_dir) {
          if cfg!(debug_assertions) {
            let expected_vendor_dir = resolve_vendor_dir(
              root_config_folder.deno_json().map(|d| d.as_ref()),
              opts.maybe_vendor_override.as_ref(),
            );
            debug_assert_eq!(
              expected_vendor_dir, workspace.vendor_dir,
              "should not be using a different vendor dir across calls"
            );
          }
          return Ok(ConfigFileDiscovery::Workspace {
            workspace: workspace.clone(),
          });
        }
      }

      first_config_folder_url = Some(config_folder_url.clone());
    }
    found_config_folders.insert(config_folder_url, root_config_folder);
  }

  if let Some(first_config_folder_url) = first_config_folder_url {
    let config_folder = found_config_folders
      .remove(&first_config_folder_url)
      .unwrap();
    let maybe_vendor_dir = resolve_vendor_dir(
      config_folder.deno_json().map(|d| d.as_ref()),
      opts.maybe_vendor_override.as_ref(),
    );
    let patches =
      resolve_patch_config_folders(&config_folder, load_config_folder)?;
    let workspace = new_rc(Workspace::new(
      config_folder,
      Default::default(),
      patches,
      maybe_vendor_dir,
    ));
    if let Some(cache) = opts.workspace_cache {
      cache.set(workspace.root_dir_path(), workspace.clone());
    }
    Ok(ConfigFileDiscovery::Workspace { workspace })
  } else {
    Ok(ConfigFileDiscovery::None {
      maybe_vendor_dir: resolve_vendor_dir(
        None,
        opts.maybe_vendor_override.as_ref(),
      ),
    })
  }
}

fn handle_workspace_folder_with_members(
  root_config_folder: ConfigFolder,
  first_config_folder_url: Option<&Url>,
  opts: &WorkspaceDiscoverOptions<'_>,
  mut found_config_folders: HashMap<Url, ConfigFolder>,
  load_config_folder: &impl Fn(
    &Path,
  ) -> Result<Option<ConfigFolder>, ConfigReadError>,
) -> Result<ConfigFileDiscovery, WorkspaceDiscoverError> {
  let maybe_vendor_dir = resolve_vendor_dir(
    root_config_folder.deno_json().map(|d| d.as_ref()),
    opts.maybe_vendor_override.as_ref(),
  );
  let raw_root_workspace = resolve_workspace_for_config_folder(
    root_config_folder,
    maybe_vendor_dir,
    opts,
    &mut found_config_folders,
    load_config_folder,
  )?;
  let patches =
    resolve_patch_config_folders(&raw_root_workspace.root, load_config_folder)?;
  let root_workspace = new_rc(Workspace::new(
    raw_root_workspace.root,
    raw_root_workspace.members,
    patches,
    raw_root_workspace.vendor_dir,
  ));
  if let Some(cache) = opts.workspace_cache {
    cache.set(root_workspace.root_dir_path(), root_workspace.clone());
  }
  handle_workspace_with_members(
    root_workspace,
    first_config_folder_url,
    found_config_folders,
    opts,
    load_config_folder,
  )
}

fn handle_workspace_with_members(
  root_workspace: WorkspaceRc,
  first_config_folder_url: Option<&Url>,
  mut found_config_folders: HashMap<Url, ConfigFolder>,
  opts: &WorkspaceDiscoverOptions,
  load_config_folder: impl Fn(
    &Path,
  ) -> Result<Option<ConfigFolder>, ConfigReadError>,
) -> Result<ConfigFileDiscovery, WorkspaceDiscoverError> {
  let is_root_deno_json_workspace = root_workspace
    .root_deno_json()
    .map(|d| d.json.workspace.is_some())
    .unwrap_or(false);
  // if the root was an npm workspace that doesn't have the start config
  // as a member then only resolve the start config
  if !is_root_deno_json_workspace {
    if let Some(first_config_folder) = &first_config_folder_url {
      if !root_workspace
        .config_folders
        .contains_key(*first_config_folder)
      {
        if let Some(config_folder) =
          found_config_folders.remove(first_config_folder)
        {
          let maybe_vendor_dir = resolve_vendor_dir(
            config_folder.deno_json().map(|d| d.as_ref()),
            opts.maybe_vendor_override.as_ref(),
          );
          let patches =
            resolve_patch_config_folders(&config_folder, load_config_folder)?;
          let workspace = new_rc(Workspace::new(
            config_folder,
            Default::default(),
            patches,
            maybe_vendor_dir,
          ));
          if let Some(cache) = opts.workspace_cache {
            cache.set(workspace.root_dir_path(), workspace.clone());
          }
          return Ok(ConfigFileDiscovery::Workspace { workspace });
        }
      }
    }
  }

  if is_root_deno_json_workspace {
    for (key, config_folder) in &found_config_folders {
      if !root_workspace.config_folders.contains_key(key) {
        return Err(
          WorkspaceDiscoverErrorKind::ConfigNotWorkspaceMember {
            workspace_url: root_workspace.root_dir().clone(),
            config_url: config_folder_config_specifier(config_folder)
              .into_owned(),
          }
          .into(),
        );
      }
    }
  }

  // ensure no duplicate names in deno configuration files
  let mut seen_names: HashMap<&str, &Url> =
    HashMap::with_capacity(root_workspace.config_folders.len() + 1);
  for deno_json in root_workspace.deno_jsons() {
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

  Ok(ConfigFileDiscovery::Workspace {
    workspace: root_workspace,
  })
}

struct RawResolvedWorkspace {
  root: ConfigFolder,
  members: BTreeMap<UrlRc, ConfigFolder>,
  vendor_dir: Option<PathBuf>,
}

fn resolve_workspace_for_config_folder(
  root_config_folder: ConfigFolder,
  maybe_vendor_dir: Option<PathBuf>,
  opts: &WorkspaceDiscoverOptions,
  found_config_folders: &mut HashMap<Url, ConfigFolder>,
  load_config_folder: impl Fn(
    &Path,
  ) -> Result<Option<ConfigFolder>, ConfigReadError>,
) -> Result<RawResolvedWorkspace, WorkspaceDiscoverError> {
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
  let validate_member_url_is_descendant =
    |member_dir_url: &Url| -> Result<(), ResolveWorkspaceMemberError> {
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
      if let Some(config_folder) = found_config_folders.remove(member_dir_url) {
        return Ok(config_folder);
      }

      let maybe_config_folder =
        load_config_folder(&url_to_file_path(member_dir_url).unwrap())?;
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
  if let Some(deno_json) = root_config_folder.deno_json() {
    if let Some(workspace_config) = deno_json.to_workspace_config()? {
      let (pattern_members, path_members): (Vec<_>, Vec<_>) = workspace_config
        .members
        .iter()
        .partition(|member| is_glob_pattern(member) || member.starts_with("!"));

      let patterns = pattern_members
        .iter()
        .map(|raw_member| {
          PathOrPattern::from_relative(
            &deno_json.dir_path(),
            &format!("{}deno.json", ensure_trailing_slash(raw_member)),
          )
          .map_err(|err| {
            ResolveWorkspaceMemberError::DenoMemberToPattern {
              base: root_config_file_directory_url.clone(),
              member: raw_member.to_string(),
              source: err,
            }
          })
        })
        .collect::<Result<Vec<_>, _>>()?;

      let deno_json_paths = if patterns.is_empty() {
        Vec::new()
      } else {
        FileCollector::new(|_| true)
          .ignore_git_folder()
          .ignore_node_modules()
          .set_vendor_folder(maybe_vendor_dir.clone())
          .collect_file_patterns(
            opts.fs,
            FilePatterns {
              base: deno_json.dir_path().to_path_buf(),
              include: Some(PathOrPatternSet::new(patterns)),
              exclude: PathOrPatternSet::new(Vec::new()),
            },
          )
          .map_err(|err| {
            WorkspaceDiscoverErrorKind::FailedCollectingDenoMembers {
              deno_json_url: deno_json.specifier.clone(),
              source: err,
            }
          })?
      };

      let mut member_dir_urls =
        IndexSet::with_capacity(path_members.len() + deno_json_paths.len());
      for path_member in path_members {
        let member_dir_url = resolve_member_url(path_member)?;
        member_dir_urls.insert((path_member.clone(), member_dir_url));
      }
      for deno_json_path in deno_json_paths {
        let member_dir_url =
          url_from_directory_path(deno_json_path.parent().unwrap()).unwrap();
        member_dir_urls.insert((
          deno_json_path
            .parent()
            .unwrap()
            .to_string_lossy()
            .to_string(),
          member_dir_url,
        ));
      }

      for (raw_member, member_dir_url) in member_dir_urls {
        if member_dir_url == root_config_file_directory_url {
          return Err(
            ResolveWorkspaceMemberError::InvalidSelfReference {
              member: raw_member.to_string(),
            }
            .into(),
          );
        }
        validate_member_url_is_descendant(&member_dir_url)?;
        let member_config_folder = find_member_config_folder(&member_dir_url)?;
        let previous_member = final_members
          .insert(new_rc(member_dir_url.clone()), member_config_folder);
        if previous_member.is_some() {
          return Err(
            ResolveWorkspaceMemberError::Duplicate {
              member: raw_member.to_string(),
            }
            .into(),
          );
        }
      }
    }
  }
  if let Some(pkg_json) = root_config_folder.pkg_json() {
    if let Some(members) = &pkg_json.workspaces {
      let (pattern_members, path_members): (Vec<_>, Vec<_>) = members
        .iter()
        .partition(|member| is_glob_pattern(member) || member.starts_with('!'));
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
          url_from_directory_path(pkg_json_path.parent().unwrap()).unwrap();
        member_dir_urls.insert(member_dir_url);
      }

      for member_dir_url in member_dir_urls {
        if member_dir_url == root_config_file_directory_url {
          continue; // ignore self references
        }
        validate_member_url_is_descendant(&member_dir_url)?;
        let member_config_folder =
          match find_member_config_folder(&member_dir_url) {
            Ok(config_folder) => config_folder,
            Err(ResolveWorkspaceMemberError::NotFound { dir_url }) => {
              // enhance the error to say we didn't find a package.json
              return Err(
                ResolveWorkspaceMemberError::NotFoundPackageJson { dir_url }
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
        // don't surface errors about duplicate members for
        // package.json workspace members
        final_members.insert(new_rc(member_dir_url), member_config_folder);
      }
    }
  }

  Ok(RawResolvedWorkspace {
    root: root_config_folder,
    members: final_members,
    vendor_dir: maybe_vendor_dir,
  })
}

fn resolve_patch_config_folders(
  root_config_folder: &ConfigFolder,
  load_config_folder: impl Fn(
    &Path,
  ) -> Result<Option<ConfigFolder>, ConfigReadError>,
) -> Result<BTreeMap<UrlRc, ConfigFolder>, WorkspaceDiscoverError> {
  let Some(workspace_deno_json) = root_config_folder.deno_json() else {
    return Ok(Default::default());
  };
  let Some(patch_members) = workspace_deno_json.to_patch_config()? else {
    return Ok(Default::default());
  };
  let root_config_file_directory_url = root_config_folder.folder_url();
  let resolve_patch_dir_url =
    |raw_patch: &str| -> Result<Url, WorkspaceDiscoverError> {
      let patch = ensure_trailing_slash(raw_patch);
      let patch_dir_url =
        root_config_file_directory_url.join(&patch).map_err(|err| {
          WorkspaceDiscoverErrorKind::ResolvePatch {
            base: root_config_file_directory_url.clone(),
            patch: raw_patch.to_owned(),
            source: err.into(),
          }
        })?;
      Ok(patch_dir_url)
    };
  let mut final_config_folders = BTreeMap::new();
  for raw_member in &patch_members {
    let patch_dir_url = resolve_patch_dir_url(raw_member)?;
    let patch_configs =
      resolve_patch_member_config_folders(&patch_dir_url, &load_config_folder)
        .map_err(|err| WorkspaceDiscoverErrorKind::ResolvePatch {
          base: root_config_file_directory_url.clone(),
          patch: raw_member.to_string(),
          source: err,
        })?;

    for patch_config_url in patch_configs.keys() {
      if *patch_config_url.as_ref() == root_config_file_directory_url {
        return Err(WorkspaceDiscoverError(
          WorkspaceDiscoverErrorKind::ResolvePatch {
            base: root_config_file_directory_url.clone(),
            patch: raw_member.to_string(),
            source: ResolveWorkspacePatchError::WorkspaceMemberNotAllowed,
          }
          .into(),
        ));
      }
    }

    final_config_folders.extend(patch_configs);
  }

  Ok(final_config_folders)
}

fn resolve_patch_member_config_folders(
  patch_dir_url: &Url,
  load_config_folder: impl Fn(
    &Path,
  ) -> Result<Option<ConfigFolder>, ConfigReadError>,
) -> Result<BTreeMap<UrlRc, ConfigFolder>, ResolveWorkspacePatchError> {
  let patch_dir_path = url_to_file_path(patch_dir_url).unwrap();
  let maybe_config_folder = load_config_folder(&patch_dir_path)?;
  let Some(config_folder) = maybe_config_folder else {
    return Err(ResolveWorkspacePatchError::NotFound {
      dir_url: patch_dir_url.clone(),
    });
  };
  if config_folder.has_workspace_members() {
    let maybe_vendor_dir =
      resolve_vendor_dir(config_folder.deno_json().map(|d| d.as_ref()), None);
    let mut raw_workspace = resolve_workspace_for_config_folder(
      config_folder,
      maybe_vendor_dir,
      &WorkspaceDiscoverOptions::default(),
      &mut HashMap::new(),
      &load_config_folder,
    )
    .map_err(|err| ResolveWorkspacePatchError::Workspace(Box::new(err)))?;
    raw_workspace
      .members
      .insert(new_rc(raw_workspace.root.folder_url()), raw_workspace.root);
    Ok(raw_workspace.members)
  } else {
    // attempt to find the root workspace directory
    for ancestor in patch_dir_path.ancestors().skip(1) {
      let Ok(Some(config_folder)) = load_config_folder(ancestor) else {
        continue;
      };
      if config_folder.has_workspace_members() {
        let maybe_vendor_dir = resolve_vendor_dir(
          config_folder.deno_json().map(|d| d.as_ref()),
          None,
        );
        let Ok(mut raw_workspace) = resolve_workspace_for_config_folder(
          config_folder,
          maybe_vendor_dir,
          &WorkspaceDiscoverOptions::default(),
          &mut HashMap::new(),
          &load_config_folder,
        ) else {
          continue;
        };
        if raw_workspace.members.contains_key(patch_dir_url) {
          raw_workspace.members.insert(
            new_rc(raw_workspace.root.folder_url()),
            raw_workspace.root,
          );
          return Ok(raw_workspace.members);
        }
      }
    }
    Ok(BTreeMap::from([(
      new_rc(patch_dir_url.clone()),
      config_folder,
    )]))
  }
}

fn resolve_vendor_dir(
  maybe_deno_json: Option<&ConfigFile>,
  maybe_vendor_override: Option<&VendorEnablement>,
) -> Option<PathBuf> {
  if let Some(vendor_folder_override) = maybe_vendor_override {
    match vendor_folder_override {
      VendorEnablement::Disable => None,
      VendorEnablement::Enable { cwd } => match maybe_deno_json {
        Some(c) => Some(c.dir_path().join("vendor")),
        None => Some(cwd.join("vendor")),
      },
    }
  } else {
    let deno_json = maybe_deno_json?;
    if deno_json.vendor() == Some(true) {
      Some(deno_json.dir_path().join("vendor"))
    } else {
      None
    }
  }
}

fn ensure_trailing_slash(path: &str) -> Cow<str> {
  if !path.ends_with('/') {
    Cow::Owned(format!("{}/", path))
  } else {
    Cow::Borrowed(path)
  }
}
