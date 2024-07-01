// Copyright 2018-2024 the Deno authors. MIT license.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::path::Path;
use std::path::PathBuf;

use url::Url;

use crate::package_json::PackageJson;
use crate::package_json::PackageJsonLoadError;
use crate::package_json::PackageJsonRc;
use crate::sync::new_rc;
use crate::util::is_skippable_io_error;
use crate::util::normalize_path;
use crate::util::specifier_to_file_path;
use crate::ConfigFile;
use crate::ConfigFileRc;

use super::ResolveWorkspaceMemberError;
use super::UrlRc;
use super::WorkspaceDiscoverError;
use super::WorkspaceDiscoverErrorKind;
use super::WorkspaceDiscoverOptions;
use super::WorkspaceDiscoverStart;

#[derive(Debug)]
pub enum DenoOrPkgJson {
  Deno(ConfigFileRc),
  PkgJson(crate::package_json::PackageJsonRc),
}

#[derive(Debug)]
pub enum ConfigFileDiscovery {
  None,
  Single(ConfigFileRc),
  Workspace {
    root: ConfigFileRc,
    members: BTreeMap<UrlRc, DenoOrPkgJson>,
  },
}

pub fn discover_workspace_config_files(
  start: WorkspaceDiscoverStart,
  opts: &WorkspaceDiscoverOptions,
) -> Result<ConfigFileDiscovery, WorkspaceDiscoverError> {
  let mut next_start_dir: Option<Cow<Path>>;
  let mut first_config_file: Option<Url> = None;
  let mut found_configs: HashMap<_, ConfigFile> = HashMap::new();
  match start {
    WorkspaceDiscoverStart::Dir(dir) => {
      next_start_dir = Some(Cow::Borrowed(dir));
    }
    WorkspaceDiscoverStart::ConfigFile(file) => {
      next_start_dir =
        file.parent().and_then(|p| p.parent()).map(Cow::Borrowed);
      let specifier = Url::from_file_path(file).unwrap();
      let config_file = ConfigFile::from_specifier(
        opts.fs,
        specifier.clone(),
        &opts.config_parse_options,
      )?;
      found_configs.insert(specifier.clone(), config_file);
      first_config_file = Some(specifier);
    }
  }
  while let Some(start_dir) = next_start_dir.take() {
    let config_file = ConfigFile::discover_from(
      opts.fs,
      &start_dir,
      opts.additional_config_file_names,
      &opts.config_parse_options,
    )?;
    let Some(workspace_config_file) = config_file else {
      break;
    };
    let workspace_field = workspace_config_file.json.workspace.as_ref();
    if let Some(members) = workspace_field {
      if members.is_empty() {
        return Err(
          WorkspaceDiscoverErrorKind::MembersEmpty(
            workspace_config_file.specifier.clone(),
          )
          .into(),
        );
      }
      let config_file_path =
        specifier_to_file_path(&workspace_config_file.specifier).unwrap();
      let root_config_file_directory = config_file_path.parent().unwrap();
      let root_config_file_directory_url =
        Url::from_directory_path(root_config_file_directory).unwrap();
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
                return Ok(DenoOrPkgJson::Deno(new_rc(config_file)));
              }
            }
          }

          // now search the file system
          for url in config_file_urls {
            let result = ConfigFile::from_specifier(
              opts.fs,
              url,
              &opts.config_parse_options,
            );
            match result {
              Ok(config_file) => {
                log::debug!(
                  "Member config file found at '{}'",
                  config_file.specifier
                );
                return Ok(DenoOrPkgJson::Deno(new_rc(config_file)));
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
          let pkg_json_result = PackageJson::load_from_path(
            &package_json_path,
            opts.fs,
            opts.pkg_json_cache,
          );
          match pkg_json_result {
            Ok(pkg_json) => {
              log::debug!(
                "Member package.json found at '{}'",
                pkg_json.path.display()
              );
              Ok(DenoOrPkgJson::PkgJson(pkg_json))
            }
            Err(PackageJsonLoadError::Io { source, .. })
              if source.kind() == std::io::ErrorKind::NotFound =>
            {
              Err(ResolveWorkspaceMemberError::NotFound {
                dir_url: member_dir_url.clone(),
              })
            }
            Err(err) => Err(err.into()),
          }
        };

        let member = if !raw_member.ends_with('/') {
          Cow::Owned(format!("{}/", raw_member))
        } else {
          Cow::Borrowed(raw_member)
        };
        let member_dir_url = root_config_file_directory_url
          .join(&member)
          .map_err(|err| {
            WorkspaceDiscoverError(
              WorkspaceDiscoverErrorKind::InvalidMember {
                base: workspace_config_file.specifier.clone(),
                member: raw_member.clone(),
                source: err,
              }
              .into(),
            )
          })?;
        if member_dir_url == root_config_file_directory_url {
          return Err(
            ResolveWorkspaceMemberError::InvalidSelfReference {
              member: raw_member.to_string(),
            }
            .into(),
          );
        }
        if !member_dir_url
          .as_str()
          .starts_with(root_config_file_directory_url.as_str())
        {
          return Err(
            ResolveWorkspaceMemberError::NonDescendant {
              workspace_url: root_config_file_directory_url.clone(),
              member_url: member_dir_url,
            }
            .into(),
          );
        }
        let config = find_config(&member_dir_url)?;
        let previous_member =
          final_members.insert(new_rc(member_dir_url), config);
        if previous_member.is_some() {
          return Err(
            ResolveWorkspaceMemberError::Duplicate {
              member: raw_member.to_string(),
            }
            .into(),
          );
        }
      }
      if let Some(config_url) = found_configs.into_keys().next() {
        return Err(
          WorkspaceDiscoverErrorKind::ConfigNotWorkspaceMember {
            workspace_url: workspace_config_file.specifier.clone(),
            config_url,
          }
          .into(),
        );
      }
      return Ok(ConfigFileDiscovery::Workspace {
        root: new_rc(workspace_config_file),
        members: final_members,
      });
    } else {
      if first_config_file.is_none() {
        first_config_file = Some(workspace_config_file.specifier.clone());
      }
      next_start_dir =
        specifier_to_file_path(&workspace_config_file.specifier)?
          .parent()
          .and_then(|p| p.parent())
          .map(|p| Cow::Owned(p.to_owned()));
      found_configs.insert(
        workspace_config_file.specifier.clone(),
        workspace_config_file,
      );
    }
  }

  if let Some(first_config_file) = first_config_file {
    let config = found_configs.remove(&first_config_file).unwrap();
    Ok(ConfigFileDiscovery::Single(new_rc(config)))
  } else {
    Ok(ConfigFileDiscovery::None)
  }
}

#[derive(Debug)]
pub enum PackageJsonDiscovery {
  None,
  Single(PackageJsonRc),
  Workspace {
    root: PackageJsonRc,
    members: BTreeMap<UrlRc, PackageJsonRc>,
  },
}

pub fn discover_with_npm(
  start: WorkspaceDiscoverStart,
  config_file_discovery: &ConfigFileDiscovery,
  opts: &WorkspaceDiscoverOptions,
) -> Result<PackageJsonDiscovery, WorkspaceDiscoverError> {
  let mut found_configs: HashMap<PathBuf, PackageJsonRc> = HashMap::new();
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
    .and_then(|p| p.parent())
    .and_then(|p| p.parent());
  for ancestor in start.dir_path().ancestors() {
    if Some(ancestor) == maybe_stop_dir {
      break;
    }
    let pkg_json_path = ancestor.join("package.json");
    let pkg_json = match PackageJson::load_from_path(
      &pkg_json_path,
      opts.fs,
      opts.pkg_json_cache,
    ) {
      Ok(pkg_json) => pkg_json,
      Err(PackageJsonLoadError::Io { source, .. })
        if is_skippable_io_error(&source) =>
      {
        continue; // keep going
      }
      Err(err) => return Err(WorkspaceDiscoverError(Box::new(err.into()))),
    };
    log::debug!("package.json file found at '{}'", pkg_json_path.display());
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
          let pkg_json_path =
            normalize_path(ancestor.join(member).join("package.json"));
          if !pkg_json_path.starts_with(ancestor) {
            return Err(ResolveWorkspaceMemberError::NonDescendant {
              workspace_url: Url::from_directory_path(ancestor).unwrap(),
              member_url: Url::from_directory_path(
                pkg_json_path.parent().unwrap(),
              )
              .unwrap(),
            });
          }
          // try to find the package.json in memory from what we already
          // found on the file system
          if let Some(pkg_json) = found_configs.remove(&pkg_json_path) {
            return Ok(pkg_json);
          }

          // now search the file system
          PackageJson::load_from_path(
            &pkg_json_path,
            opts.fs,
            opts.pkg_json_cache,
          )
          .map_err(|e| e.into())
        };

        let pkg_json = match find_config() {
          Ok(config) => config,
          Err(err) => {
            log::warn!("Failed loading package.json, but ignoring. {:#}", err);
            continue;
          }
        };
        final_members.insert(
          new_rc(Url::from_file_path(pkg_json.path.parent().unwrap()).unwrap()),
          pkg_json,
        );
      }

      // just include any remaining found configs as workspace members
      // instead of erroring for now
      for (path, config) in found_configs {
        let url = new_rc(Url::from_file_path(path.parent().unwrap()).unwrap());
        final_members.insert(url, config);
      }

      return Ok(PackageJsonDiscovery::Workspace {
        root: pkg_json,
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
    Ok(PackageJsonDiscovery::Single(config))
  } else {
    log::debug!("No package.json file found");
    Ok(PackageJsonDiscovery::None)
  }
}
