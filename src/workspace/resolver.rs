// Copyright 2018-2024 the Deno authors. MIT license.

use std::sync::Arc;

use import_map::ImportMap;
use import_map::ImportMapWithDiagnostics;
use indexmap::IndexMap;
use thiserror::Error;
use url::Url;

use crate::package_json::PackageJson;
use crate::package_json::PackageJsonDeps;
use crate::ConfigFile;

use super::Workspace;

struct DenoJsonResolverFolderConfig {
  import_map: Option<Arc<ImportMap>>,
  config: Arc<ConfigFile>,
}

struct PkgJsonResolverFolderConfig {
  deps: PackageJsonDeps,
  pkg_json: Arc<PackageJson>,
}

struct ResolverFolderConfigs {
  deno_json: Option<DenoJsonResolverFolderConfig>,
  pkg_json: Option<PkgJsonResolverFolderConfig>,
}

#[derive(Debug, Error)]
pub enum WorkspaceResolverCreateError {
  #[error(transparent)]
  ImportMap(#[from] import_map::ImportMapError),
}

pub struct WorkspaceResolver {
  import_map: ImportMapWithDiagnostics,
  pkg_jsons: IndexMap<Url, PkgJsonResolverFolderConfig>,
}

impl WorkspaceResolver {
  pub(crate) fn from_workspace(
    workspace: &Workspace,
  ) -> Result<Self, WorkspaceResolverCreateError> {
    let (root_dir, root_folder) = workspace.root_folder();
    let deno_jsons = workspace
      .config_folders()
      .iter()
      .filter_map(|(_, f)| f.config.as_ref())
      .collect::<Vec<_>>();
    let base_url = root_folder
      .config
      .as_ref()
      .map(|c| c.specifier.clone())
      .unwrap_or_else(|| root_dir.join("deno.json").unwrap());
    let base_import_map_config = import_map::ext::ImportMapConfig {
      base_url,
      import_map_value: root_folder
        .config
        .as_ref()
        .map(|c| c.to_import_map_value_from_imports())
        .unwrap_or_else(|| serde_json::Value::Object(Default::default())),
    };
    let child_import_map_configs = deno_jsons
      .iter()
      .filter(|f| {
        Some(&f.specifier) != root_folder.config.as_ref().map(|c| &c.specifier)
      })
      .map(|config| import_map::ext::ImportMapConfig {
        base_url: config.specifier.clone(),
        import_map_value: config.to_import_map_value_from_imports(),
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
    let import_map = import_map::parse_from_value(import_map_url, import_map)?;
    let pkg_jsons = workspace
      .config_folders()
      .iter()
      .filter_map(|(dir_url, f)| {
        let pkg_json = f.pkg_json.clone()?;
        let deps = pkg_json.resolve_local_package_json_version_reqs();
        Some((
          dir_url.clone(),
          PkgJsonResolverFolderConfig { deps, pkg_json },
        ))
      })
      .collect::<IndexMap<_, _>>();
    Ok(Self {
      import_map,
      pkg_jsons,
    })
  }
}

fn enhance_import_map_value_with_workspace_members<'a>(
  mut import_map_value: serde_json::Value,
  deno_jsons: impl Iterator<Item = &'a ConfigFile>,
) -> serde_json::Value {
  let mut imports = if let Some(serde_json::Value::Object(imports)) =
    import_map_value.get("imports").as_ref()
  {
    imports.clone() // todo(dsherret): do not clone here
  } else {
    serde_json::Map::new()
  };

  for deno_json in deno_jsons {
    let Some(name) = &deno_json.json.name else {
      continue;
    };
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
