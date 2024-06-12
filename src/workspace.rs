// Copyright 2018-2024 the Deno authors. MIT license.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::path::Path;
use std::sync::Arc;

use thiserror::Error;
use url::Url;

use crate::deno_json::ConfigFile;
use crate::deno_json::ConfigFileReadError;
use crate::deno_json::ConfigParseOptions;
use crate::package_json::PackageJson;
use crate::package_json::PackageJsonReadError;
use crate::util::is_skippable_io_error;
use crate::util::specifier_to_file_path;
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

pub struct Workspace {}

impl Workspace {
  pub fn discover(
    opts: WorkspaceDiscoverOptions,
  ) -> Result<Self, WorkspaceDiscoverError> {
    Ok(Self {})
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
  opts: WorkspaceDiscoverOptions,
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
  opts: WorkspaceDiscoverOptions,
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
