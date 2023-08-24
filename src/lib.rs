// Copyright 2018-2023 the Deno authors. All rights reserved. MIT license.

use anyhow::anyhow;
use anyhow::bail;
use anyhow::Context;
use anyhow::Error as AnyError;
use indexmap::IndexMap;
use serde::Deserialize;
use serde::Serialize;
use serde::Serializer;
use serde_json::json;
use serde_json::Value;
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::path::Path;
use std::path::PathBuf;
use url::Url;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum ConfigFlag {
  #[default]
  Discover,
  Path(String),
  Disabled,
}

/// Gets the parent of this module specifier.
pub fn specifier_parent(specifier: &Url) -> Url {
  let mut specifier = specifier.clone();
  // don't use specifier.segments() because it will strip the leading slash
  let mut segments = specifier.path().split('/').collect::<Vec<_>>();
  if segments.iter().all(|s| s.is_empty()) {
    return specifier;
  }
  if let Some(last) = segments.last() {
    if last.is_empty() {
      segments.pop();
    }
    segments.pop();
    let new_path = format!("{}/", segments.join("/"));
    specifier.set_path(&new_path);
  }
  specifier
}

/// Attempts to convert a specifier to a file path. By default, uses the Url
/// crate's `to_file_path()` method, but falls back to try and resolve unix-style
/// paths on Windows.
pub fn specifier_to_file_path(specifier: &Url) -> Result<PathBuf, AnyError> {
  let result = if specifier.scheme() != "file" {
    Err(())
  } else if cfg!(windows) {
    match specifier.to_file_path() {
      Ok(path) => Ok(path),
      Err(()) => {
        // This might be a unix-style path which is used in the tests even on Windows.
        // Attempt to see if we can convert it to a `PathBuf`. This code should be removed
        // once/if https://github.com/servo/rust-url/issues/730 is implemented.
        if specifier.scheme() == "file"
          && specifier.host().is_none()
          && specifier.port().is_none()
          && specifier.path_segments().is_some()
        {
          let path_str = specifier.path();
          match String::from_utf8(
            percent_encoding::percent_decode(path_str.as_bytes()).collect(),
          ) {
            Ok(path_str) => Ok(PathBuf::from(path_str)),
            Err(_) => Err(()),
          }
        } else {
          Err(())
        }
      }
    }
  } else {
    specifier.to_file_path()
  };
  match result {
    Ok(path) => Ok(path),
    Err(()) => bail!("Invalid file path.\n  Specifier: {specifier}"),
  }
}

#[derive(Debug, Clone, Hash)]
pub struct JsxImportSourceConfig {
  pub default_specifier: Option<String>,
  pub module: String,
  pub base_url: Url,
}

impl JsxImportSourceConfig {
  pub fn maybe_specifier_text(&self) -> Option<String> {
    self
      .default_specifier
      .as_ref()
      .map(|default_specifier| format!("{}/{}", default_specifier, self.module))
  }
}

/// The transpile options that are significant out of a user provided tsconfig
/// file, that we want to deserialize out of the final config for a transpile.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EmitConfigOptions {
  pub check_js: bool,
  pub emit_decorator_metadata: bool,
  pub imports_not_used_as_values: String,
  pub inline_source_map: bool,
  pub inline_sources: bool,
  pub source_map: bool,
  pub jsx: String,
  pub jsx_factory: String,
  pub jsx_fragment_factory: String,
  pub jsx_import_source: Option<String>,
}

/// There are certain compiler options that can impact what modules are part of
/// a module graph, which need to be deserialized into a structure for analysis.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CompilerOptions {
  pub jsx: Option<String>,
  pub jsx_import_source: Option<String>,
  pub types: Option<Vec<String>>,
}

/// A structure that represents a set of options that were ignored and the
/// path those options came from.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct IgnoredCompilerOptions {
  pub items: Vec<String>,
  pub maybe_specifier: Option<Url>,
}

impl fmt::Display for IgnoredCompilerOptions {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let mut codes = self.items.clone();
    codes.sort_unstable();
    if let Some(specifier) = &self.maybe_specifier {
      write!(f, "Unsupported compiler options in \"{}\".\n  The following options were ignored:\n    {}", specifier, codes.join(", "))
    } else {
      write!(f, "Unsupported compiler options provided.\n  The following options were ignored:\n    {}", codes.join(", "))
    }
  }
}

impl Serialize for IgnoredCompilerOptions {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    Serialize::serialize(&self.items, serializer)
  }
}

/// A static slice of all the compiler options that should be ignored that
/// either have no effect on the compilation or would cause the emit to not work
/// in Deno.
pub const IGNORED_COMPILER_OPTIONS: &[&str] = &[
  "allowImportingTsExtensions",
  "allowSyntheticDefaultImports",
  "allowUmdGlobalAccess",
  "assumeChangesOnlyAffectDirectDependencies",
  "baseUrl",
  "build",
  "charset",
  "composite",
  "declaration",
  "declarationMap",
  "diagnostics",
  "disableSizeLimit",
  "downlevelIteration",
  "emitBOM",
  "emitDeclarationOnly",
  "esModuleInterop",
  "experimentalDecorators",
  "extendedDiagnostics",
  "forceConsistentCasingInFileNames",
  "generateCpuProfile",
  "help",
  "importHelpers",
  "incremental",
  "init",
  "inlineSourceMap",
  "inlineSources",
  "isolatedModules",
  "listEmittedFiles",
  "listFiles",
  "mapRoot",
  "maxNodeModuleJsDepth",
  "module",
  "moduleDetection",
  "moduleResolution",
  "newLine",
  "noEmit",
  "noEmitHelpers",
  "noEmitOnError",
  "noLib",
  "noResolve",
  "out",
  "outDir",
  "outFile",
  "paths",
  "preserveConstEnums",
  "preserveSymlinks",
  "preserveWatchOutput",
  "pretty",
  "project",
  "reactNamespace",
  "resolveJsonModule",
  "rootDir",
  "rootDirs",
  "showConfig",
  "skipDefaultLibCheck",
  "skipLibCheck",
  "sourceMap",
  "sourceRoot",
  "stripInternal",
  "target",
  "traceResolution",
  "tsBuildInfoFile",
  "typeRoots",
  "useDefineForClassFields",
  "version",
  "watch",
];

/// A function that works like JavaScript's `Object.assign()`.
pub fn json_merge(a: &mut Value, b: &Value) {
  match (a, b) {
    (&mut Value::Object(ref mut a), Value::Object(b)) => {
      for (k, v) in b {
        json_merge(a.entry(k.clone()).or_insert(Value::Null), v);
      }
    }
    (a, b) => {
      *a = b.clone();
    }
  }
}

fn parse_compiler_options(
  compiler_options: &HashMap<String, Value>,
  maybe_specifier: Option<Url>,
) -> Result<(Value, Option<IgnoredCompilerOptions>), AnyError> {
  let mut filtered: HashMap<String, Value> = HashMap::new();
  let mut items: Vec<String> = Vec::new();

  for (key, value) in compiler_options.iter() {
    let key = key.as_str();
    // We don't pass "types" entries to typescript via the compiler
    // options and instead provide those to tsc as "roots". This is
    // because our "types" behavior is at odds with how TypeScript's
    // "types" works.
    if key != "types" {
      if IGNORED_COMPILER_OPTIONS.contains(&key) {
        items.push(key.to_string());
      } else {
        filtered.insert(key.to_string(), value.to_owned());
      }
    }
  }
  let value = serde_json::to_value(filtered)?;
  let maybe_ignored_options = if !items.is_empty() {
    Some(IgnoredCompilerOptions {
      items,
      maybe_specifier,
    })
  } else {
    None
  };

  Ok((value, maybe_ignored_options))
}

/// A structure for managing the configuration of TypeScript
#[derive(Debug, Clone)]
pub struct TsConfig(pub Value);

impl TsConfig {
  /// Create a new `TsConfig` with the base being the `value` supplied.
  pub fn new(value: Value) -> Self {
    TsConfig(value)
  }

  pub fn as_bytes(&self) -> Vec<u8> {
    let map = self.0.as_object().expect("invalid tsconfig");
    let ordered: BTreeMap<_, _> = map.iter().collect();
    let value = json!(ordered);
    value.to_string().as_bytes().to_owned()
  }

  /// Return the value of the `checkJs` compiler option, defaulting to `false`
  /// if not present.
  pub fn get_check_js(&self) -> bool {
    if let Some(check_js) = self.0.get("checkJs") {
      check_js.as_bool().unwrap_or(false)
    } else {
      false
    }
  }

  pub fn get_declaration(&self) -> bool {
    if let Some(declaration) = self.0.get("declaration") {
      declaration.as_bool().unwrap_or(false)
    } else {
      false
    }
  }

  /// Merge a serde_json value into the configuration.
  pub fn merge(&mut self, value: &Value) {
    json_merge(&mut self.0, value);
  }

  /// Take an optional user provided config file
  /// which was passed in via the `--config` flag and merge `compilerOptions` with
  /// the configuration.  Returning the result which optionally contains any
  /// compiler options that were ignored.
  pub fn merge_tsconfig_from_config_file(
    &mut self,
    maybe_config_file: Option<&ConfigFile>,
  ) -> Result<Option<IgnoredCompilerOptions>, AnyError> {
    if let Some(config_file) = maybe_config_file {
      let (value, maybe_ignored_options) = config_file.to_compiler_options()?;
      self.merge(&value);
      Ok(maybe_ignored_options)
    } else {
      Ok(None)
    }
  }
}

impl Serialize for TsConfig {
  /// Serializes inner hash map which is ordered by the key
  fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    Serialize::serialize(&self.0, serializer)
  }
}

#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields)]
pub struct LintRulesConfig {
  pub tags: Option<Vec<String>>,
  pub include: Option<Vec<String>>,
  pub exclude: Option<Vec<String>>,
}

#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields)]
struct SerializedFilesConfig {
  pub include: Vec<String>,
  pub exclude: Vec<String>,
}

impl SerializedFilesConfig {
  pub fn into_resolved(
    self,
    config_file_specifier: &Url,
  ) -> Result<FilesConfig, AnyError> {
    let config_dir =
      specifier_to_file_path(&specifier_parent(config_file_specifier))?;
    Ok(FilesConfig {
      include: self
        .include
        .into_iter()
        .map(|p| config_dir.join(p))
        .collect::<Vec<_>>(),
      exclude: self
        .exclude
        .into_iter()
        .map(|p| config_dir.join(p))
        .collect::<Vec<_>>(),
    })
  }

  pub fn is_empty(&self) -> bool {
    self.include.is_empty() && self.exclude.is_empty()
  }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FilesConfig {
  pub include: Vec<PathBuf>,
  pub exclude: Vec<PathBuf>,
}

impl FilesConfig {
  /// Gets if the provided specifier is allowed based on the includes
  /// and excludes in the configuration file.
  pub fn matches_specifier(&self, specifier: &Url) -> bool {
    let file_path = match specifier_to_file_path(specifier) {
      Ok(file_path) => file_path,
      Err(_) => return false,
    };
    // Skip files which is in the exclude list.
    if self.exclude.iter().any(|i| file_path.starts_with(i)) {
      return false;
    }

    // Ignore files not in the include list if it's not empty.
    self.include.is_empty()
      || self.include.iter().any(|i| file_path.starts_with(i))
  }

  fn extend(self, rhs: Self) -> Self {
    Self {
      include: [self.include, rhs.include].concat(),
      exclude: [self.exclude, rhs.exclude].concat(),
    }
  }
}

/// Choose between flat and nested files configuration.
///
/// `files` has precedence over `deprecated_files`.
/// when `deprecated_files` is present, a warning is logged.
///
/// caveat: due to default values, it's not possible to distinguish between
/// an empty configuration and a configuration with default values.
/// `{ "files": {} }` is equivalent to `{ "files": { "include": [], "exclude": [] } }`
/// and it wouldn't be able to emit warning for `{ "files": {}, "exclude": [] }`.
///
/// # Arguments
///
/// * `files` - Flat configuration.
/// * `deprecated_files` - Nested configuration. ("Files")
fn choose_files(
  files: SerializedFilesConfig,
  deprecated_files: SerializedFilesConfig,
) -> SerializedFilesConfig {
  const DEPRECATED_FILES: &str =
    "Warning: \"files\" configuration is deprecated";
  const FLAT_CONFIG: &str = "\"include\" and \"exclude\"";

  let (files_nonempty, deprecated_files_nonempty) =
    (!files.is_empty(), !deprecated_files.is_empty());

  match (files_nonempty, deprecated_files_nonempty) {
    (true, true) => {
      log::warn!("{DEPRECATED_FILES} and ignored by {FLAT_CONFIG}.");
      files
    }
    (true, false) => files,
    (false, true) => {
      log::warn!("{DEPRECATED_FILES}. Please use {FLAT_CONFIG} instead.");
      deprecated_files
    }
    (false, false) => SerializedFilesConfig::default(),
  }
}

/// `lint` config representation for serde
///
/// fields `include` and `exclude` are expanded from [SerializedFilesConfig].
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields)]
struct SerializedLintConfig {
  pub rules: LintRulesConfig,
  pub include: Vec<String>,
  pub exclude: Vec<String>,

  #[serde(rename = "files")]
  pub deprecated_files: SerializedFilesConfig,
  pub report: Option<String>,
}

impl SerializedLintConfig {
  pub fn into_resolved(
    self,
    config_file_specifier: &Url,
  ) -> Result<LintConfig, AnyError> {
    let (include, exclude) = (self.include, self.exclude);
    let files = SerializedFilesConfig { include, exclude };

    Ok(LintConfig {
      rules: self.rules,
      files: choose_files(files, self.deprecated_files)
        .into_resolved(config_file_specifier)?,
      report: self.report,
    })
  }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct LintConfig {
  pub rules: LintRulesConfig,
  pub files: FilesConfig,
  pub report: Option<String>,
}

impl LintConfig {
  pub fn with_files(self, files: FilesConfig) -> Self {
    let files = self.files.extend(files);
    Self { files, ..self }
  }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub enum ProseWrap {
  Always,
  Never,
  Preserve,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields, rename_all = "camelCase")]
pub struct FmtOptionsConfig {
  pub use_tabs: Option<bool>,
  pub line_width: Option<u32>,
  pub indent_width: Option<u8>,
  pub single_quote: Option<bool>,
  pub prose_wrap: Option<ProseWrap>,
  pub semi_colons: Option<bool>,
}

impl FmtOptionsConfig {
  pub fn is_empty(&self) -> bool {
    self.use_tabs.is_none()
      && self.line_width.is_none()
      && self.indent_width.is_none()
      && self.single_quote.is_none()
      && self.prose_wrap.is_none()
      && self.semi_colons.is_none()
  }
}

/// Choose between flat and nested fmt options.
///
/// `options` has precedence over `deprecated_options`.
/// when `deprecated_options` is present, a warning is logged.
///
/// caveat: due to default values, it's not possible to distinguish between
/// an empty configuration and a configuration with default values.
/// `{ "fmt": {} } is equivalent to `{ "fmt": { "options": {} } }`
/// and it wouldn't be able to emit warning for `{ "fmt": { "options": {}, "semiColons": "false" } }`.
///
/// # Arguments
///
/// * `options` - Flat options.
/// * `deprecated_options` - Nested files configuration ("option").
fn choose_fmt_options(
  options: FmtOptionsConfig,
  deprecated_options: FmtOptionsConfig,
) -> FmtOptionsConfig {
  const DEPRECATED_OPTIONS: &str =
    "Warning: \"options\" configuration is deprecated";
  const FLAT_OPTION: &str = "\"flat\" options";

  let (options_nonempty, deprecated_options_nonempty) =
    (!options.is_empty(), !deprecated_options.is_empty());

  match (options_nonempty, deprecated_options_nonempty) {
    (true, true) => {
      log::warn!("{DEPRECATED_OPTIONS} and ignored by {FLAT_OPTION}.");
      options
    }
    (true, false) => options,
    (false, true) => {
      log::warn!("{DEPRECATED_OPTIONS}. Please use {FLAT_OPTION} instead.");
      deprecated_options
    }
    (false, false) => FmtOptionsConfig::default(),
  }
}

/// `fmt` config representation for serde
///
/// fields from `use_tabs`..`semi_colons` are expanded from [FmtOptionsConfig].
/// fields `include` and `exclude` are expanded from [SerializedFilesConfig].
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields, rename_all = "camelCase")]
struct SerializedFmtConfig {
  pub use_tabs: Option<bool>,
  pub line_width: Option<u32>,
  pub indent_width: Option<u8>,
  pub single_quote: Option<bool>,
  pub prose_wrap: Option<ProseWrap>,
  pub semi_colons: Option<bool>,
  #[serde(rename = "options")]
  pub deprecated_options: FmtOptionsConfig,
  pub include: Vec<String>,
  pub exclude: Vec<String>,
  #[serde(rename = "files")]
  pub deprecated_files: SerializedFilesConfig,
}

impl SerializedFmtConfig {
  pub fn into_resolved(
    self,
    config_file_specifier: &Url,
  ) -> Result<FmtConfig, AnyError> {
    let (include, exclude) = (self.include, self.exclude);
    let files = SerializedFilesConfig { include, exclude };
    let options = FmtOptionsConfig {
      use_tabs: self.use_tabs,
      line_width: self.line_width,
      indent_width: self.indent_width,
      single_quote: self.single_quote,
      prose_wrap: self.prose_wrap,
      semi_colons: self.semi_colons,
    };

    Ok(FmtConfig {
      options: choose_fmt_options(options, self.deprecated_options),
      files: choose_files(files, self.deprecated_files)
        .into_resolved(config_file_specifier)?,
    })
  }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct FmtConfig {
  pub options: FmtOptionsConfig,
  pub files: FilesConfig,
}

impl FmtConfig {
  pub fn with_files(self, files: FilesConfig) -> Self {
    let files = self.files.extend(files);
    Self { files, ..self }
  }
}

/// `test` config representation for serde
///
/// fields `include` and `exclude` are expanded from [SerializedFilesConfig].
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields)]
struct SerializedTestConfig {
  pub include: Vec<String>,
  pub exclude: Vec<String>,
  #[serde(rename = "files")]
  pub deprecated_files: SerializedFilesConfig,
}

impl SerializedTestConfig {
  pub fn into_resolved(
    self,
    config_file_specifier: &Url,
  ) -> Result<TestConfig, AnyError> {
    let (include, exclude) = (self.include, self.exclude);
    let files = SerializedFilesConfig { include, exclude };

    Ok(TestConfig {
      files: choose_files(files, self.deprecated_files)
        .into_resolved(config_file_specifier)?,
    })
  }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct TestConfig {
  pub files: FilesConfig,
}

impl TestConfig {
  pub fn with_files(self, files: FilesConfig) -> Self {
    let files = self.files.extend(files);
    Self { files }
  }
}

/// `bench` config representation for serde
///
/// fields `include` and `exclude` are expanded from [SerializedFilesConfig].
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields)]
struct SerializedBenchConfig {
  pub include: Vec<String>,
  pub exclude: Vec<String>,
  #[serde(rename = "files")]
  pub deprecated_files: SerializedFilesConfig,
}

impl SerializedBenchConfig {
  pub fn into_resolved(
    self,
    config_file_specifier: &Url,
  ) -> Result<BenchConfig, AnyError> {
    let (include, exclude) = (self.include, self.exclude);
    let files = SerializedFilesConfig { include, exclude };

    Ok(BenchConfig {
      files: choose_files(files, self.deprecated_files)
        .into_resolved(config_file_specifier)?,
    })
  }
}

#[derive(Debug, Default)]
pub struct WorkspaceConfig {
  members: Vec<WorkspaceMemberConfig>,
  base_import_map_value: Value,
}

#[derive(Debug)]
pub struct WorkspaceMemberConfig {
  // As defined in `member` setting of the workspace deno.json.
  pub member_name: String,
  pub path: PathBuf,
  pub package_name: String,
  pub package_version: String,
  pub config_file: ConfigFile,
}

impl WorkspaceConfig {
  pub fn to_import_map_value(&self) -> Result<Option<Value>, AnyError> {
    let mut import_map_imports = json!({});
    let mut import_map_scopes = json!({});
    let synthetic_import_map_imports =
      import_map_imports.as_object_mut().unwrap();
    let synthetic_import_map_scopes =
      import_map_scopes.as_object_mut().unwrap();

    for member_config in self.members.iter() {
      let import_map_value = member_config.config_file.to_import_map_value();

      let mut member_scope = json!({});

      if let Some(imports) = import_map_value.get("imports") {
        let member_scope_obj = member_scope.as_object_mut().unwrap();
        for (key, value) in imports.as_object().unwrap() {
          member_scope_obj.insert(key.to_string(), value.to_owned());
        }
        // TODO(bartlomieju): this need to resolve values in member_scope based
        // on the "base URL" of the member import map filepath
        synthetic_import_map_scopes
          .insert(format!("./{}/", member_config.member_name), member_scope);
      }

      if let Some(scopes) = import_map_value.get("scopes") {
        for (key, value) in scopes.as_object().unwrap() {
          // Keys for scopes need to be processed - they might look like
          // "/foo/" and coming from "bar" workspace member. So we need to
          // prepend the member name to the scope.
          let new_key = format!("./{}{}", member_config.member_name, key);
          // TODO(bartlomieju): this need to resolve value based on the "base URL"
          // of the member import map filepath
          synthetic_import_map_scopes.insert(new_key, value.to_owned());
        }
      }
    }

    if let Some(base_imports) = self.base_import_map_value.get("imports") {
      let base_imports_obj = base_imports.as_object().unwrap();
      for (key, value) in base_imports_obj.iter() {
        synthetic_import_map_imports.insert(key.to_owned(), value.to_owned());
      }
    }
    if let Some(base_scopes) = self.base_import_map_value.get("scopes") {
      let base_scopes_obj = base_scopes.as_object().unwrap();
      for (key, value) in base_scopes_obj.iter() {
        synthetic_import_map_scopes.insert(key.to_owned(), value.to_owned());
      }
    }

    let mut import_map = json!({});

    if !synthetic_import_map_imports.is_empty() {
      import_map["imports"] = import_map_imports;
    }
    if !synthetic_import_map_scopes.is_empty() {
      import_map["scopes"] = import_map_scopes;
    }

    if !import_map.as_object().unwrap().is_empty() {
      Ok(Some(import_map))
    } else {
      Ok(None)
    }
  }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct BenchConfig {
  pub files: FilesConfig,
}

impl BenchConfig {
  pub fn with_files(self, files: FilesConfig) -> Self {
    let files = self.files.extend(files);
    Self { files }
  }
}

#[derive(Clone, Debug, Deserialize, PartialEq)]
#[serde(untagged)]
pub enum LockConfig {
  Bool(bool),
  PathBuf(PathBuf),
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ConfigFileJson {
  pub compiler_options: Option<Value>,
  pub import_map: Option<String>,
  pub imports: Option<Value>,
  pub scopes: Option<Value>,
  pub lint: Option<Value>,
  pub fmt: Option<Value>,
  pub tasks: Option<Value>,
  pub test: Option<Value>,
  pub bench: Option<Value>,
  pub lock: Option<Value>,
  pub exclude: Option<Value>,
  pub node_modules_dir: Option<bool>,
  pub vendor: Option<bool>,

  pub name: Option<String>,
  pub version: Option<String>,
  #[serde(default)]
  pub workspace: bool,
  #[serde(default)]
  pub members: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct ConfigFile {
  pub specifier: Url,
  json: ConfigFileJson,
}

impl ConfigFile {
  pub fn discover(
    config_flag: &ConfigFlag,
    maybe_config_path_args: Option<Vec<PathBuf>>,
    cwd: &Path,
  ) -> Result<Option<ConfigFile>, AnyError> {
    match config_flag {
      ConfigFlag::Disabled => Ok(None),
      ConfigFlag::Path(config_path) => {
        let config_path = PathBuf::from(config_path);
        let config_path = if config_path.is_absolute() {
          config_path
        } else {
          cwd.join(config_path)
        };
        Ok(Some(ConfigFile::read(&config_path)?))
      }
      ConfigFlag::Discover => {
        if let Some(config_path_args) = maybe_config_path_args {
          let mut checked = HashSet::new();
          for f in config_path_args {
            if let Some(cf) = Self::discover_from(&f, &mut checked)? {
              return Ok(Some(cf));
            }
          }
          // From CWD walk up to root looking for deno.json or deno.jsonc
          Self::discover_from(cwd, &mut checked)
        } else {
          Ok(None)
        }
      }
    }
  }

  pub fn discover_from(
    start: &Path,
    checked: &mut HashSet<PathBuf>,
  ) -> Result<Option<ConfigFile>, AnyError> {
    fn is_skippable_err(e: &AnyError) -> bool {
      if let Some(ioerr) = e.downcast_ref::<std::io::Error>() {
        use std::io::ErrorKind::*;
        match ioerr.kind() {
          InvalidInput | PermissionDenied | NotFound => {
            // ok keep going
            true
          }
          _ => {
            const NOT_A_DIRECTORY: i32 = 20;
            cfg!(unix) && ioerr.raw_os_error() == Some(NOT_A_DIRECTORY)
          }
        }
      } else {
        false
      }
    }

    /// Filenames that Deno will recognize when discovering config.
    const CONFIG_FILE_NAMES: [&str; 2] = ["deno.json", "deno.jsonc"];

    // todo(dsherret): in the future, we should force all callers
    // to provide a resolved path
    let start = if start.is_absolute() {
      Cow::Borrowed(start)
    } else {
      Cow::Owned(std::env::current_dir()?.join(start))
    };

    for ancestor in start.ancestors() {
      if checked.insert(ancestor.to_path_buf()) {
        for config_filename in CONFIG_FILE_NAMES {
          let f = ancestor.join(config_filename);
          match ConfigFile::read(&f) {
            Ok(cf) => {
              log::debug!("Config file found at '{}'", f.display());
              return Ok(Some(cf));
            }
            Err(e) if is_skippable_err(&e) => {
              // ok, keep going
            }
            Err(e) => {
              return Err(e);
            }
          }
        }
      }
    }
    // No config file found.
    Ok(None)
  }

  pub fn read(config_path: &Path) -> Result<Self, AnyError> {
    debug_assert!(config_path.is_absolute());

    let specifier = Url::from_file_path(config_path).map_err(|_| {
      anyhow!(
        "Could not convert config file path to specifier. Path: {}",
        config_path.display()
      )
    })?;
    Self::from_specifier_and_path(specifier, config_path)
  }

  pub fn from_specifier(specifier: Url) -> Result<Self, AnyError> {
    let config_path =
      specifier_to_file_path(&specifier).with_context(|| {
        format!("Invalid config file path for '{}'.", specifier)
      })?;
    Self::from_specifier_and_path(specifier, &config_path)
  }

  fn from_specifier_and_path(
    specifier: Url,
    config_path: &Path,
  ) -> Result<Self, AnyError> {
    let text = std::fs::read_to_string(config_path)
      .with_context(|| format!("Error reading config file '{}'.", specifier))?;
    Self::new(&text, specifier)
  }

  pub fn new(text: &str, specifier: Url) -> Result<Self, AnyError> {
    let jsonc =
      match jsonc_parser::parse_to_serde_value(text, &Default::default()) {
        Ok(None) => json!({}),
        Ok(Some(value)) if value.is_object() => value,
        Ok(Some(_)) => {
          return Err(anyhow!(
            "config file JSON {} should be an object",
            specifier,
          ))
        }
        Err(e) => {
          return Err(anyhow!(
            "Unable to parse config file JSON {} because of {}",
            specifier,
            e.to_string()
          ))
        }
      };
    let json: ConfigFileJson = serde_json::from_value(jsonc)?;

    Ok(Self { specifier, json })
  }

  /// Returns true if the configuration indicates that JavaScript should be
  /// type checked, otherwise false.
  pub fn get_check_js(&self) -> bool {
    self
      .json
      .compiler_options
      .as_ref()
      .and_then(|co| co.get("checkJs").and_then(|v| v.as_bool()))
      .unwrap_or(false)
  }

  /// Parse `compilerOptions` and return a serde `Value`.
  /// The result also contains any options that were ignored.
  pub fn to_compiler_options(
    &self,
  ) -> Result<(Value, Option<IgnoredCompilerOptions>), AnyError> {
    if let Some(compiler_options) = self.json.compiler_options.clone() {
      let options: HashMap<String, Value> =
        serde_json::from_value(compiler_options)
          .context("compilerOptions should be an object")?;
      parse_compiler_options(&options, Some(self.specifier.to_owned()))
    } else {
      Ok((json!({}), None))
    }
  }

  pub fn to_import_map_path(&self) -> Option<String> {
    self.json.import_map.clone()
  }

  pub fn node_modules_dir_flag(&self) -> Option<bool> {
    self.json.node_modules_dir
  }

  pub fn vendor_dir_flag(&self) -> Option<bool> {
    self.json.vendor
  }

  pub fn vendor_dir_path(&self) -> Option<PathBuf> {
    if self.json.vendor == Some(true) {
      Some(
        self
          .specifier
          .to_file_path()
          .unwrap()
          .parent()
          .unwrap()
          .join("vendor"),
      )
    } else {
      None
    }
  }

  pub fn to_import_map_value(&self) -> Value {
    let mut value = serde_json::Map::with_capacity(2);
    if let Some(imports) = &self.json.imports {
      value.insert("imports".to_string(), imports.clone());
    }
    if let Some(scopes) = &self.json.scopes {
      value.insert("scopes".to_string(), scopes.clone());
    }
    value.into()
  }

  pub fn is_an_import_map(&self) -> bool {
    self.json.imports.is_some() || self.json.scopes.is_some()
  }

  pub fn to_files_config(&self) -> Result<Option<FilesConfig>, AnyError> {
    let mut exclude: Vec<String> =
      if let Some(exclude) = self.json.exclude.clone() {
        serde_json::from_value(exclude)
          .context("Failed to parse \"exclude\" configuration")?
      } else {
        Vec::new()
      };

    if self.vendor_dir_flag() == Some(true) {
      exclude.push("vendor".to_string());
    }

    let raw_files_config = SerializedFilesConfig {
      exclude,
      ..Default::default()
    };
    Ok(Some(raw_files_config.into_resolved(&self.specifier)?))
  }

  pub fn to_fmt_config(&self) -> Result<Option<FmtConfig>, AnyError> {
    let files_config = self.to_files_config()?;
    let fmt_config = match self.json.fmt.clone() {
      Some(config) => {
        let fmt_config: SerializedFmtConfig = serde_json::from_value(config)
          .context("Failed to parse \"fmt\" configuration")?;
        Some(fmt_config.into_resolved(&self.specifier)?)
      }
      None => None,
    };

    if files_config.is_none() && fmt_config.is_none() {
      return Ok(None);
    }

    let fmt_config = fmt_config.unwrap_or_default();
    let files_config = files_config.unwrap_or_default();

    Ok(Some(fmt_config.with_files(files_config)))
  }

  pub fn to_lint_config(&self) -> Result<Option<LintConfig>, AnyError> {
    let files_config = self.to_files_config()?;
    let lint_config = match self.json.lint.clone() {
      Some(config) => {
        let lint_config: SerializedLintConfig = serde_json::from_value(config)
          .context("Failed to parse \"lint\" configuration")?;
        Some(lint_config.into_resolved(&self.specifier)?)
      }
      None => None,
    };

    if files_config.is_none() && lint_config.is_none() {
      return Ok(None);
    }

    let lint_config = lint_config.unwrap_or_default();
    let files_config = files_config.unwrap_or_default();

    Ok(Some(lint_config.with_files(files_config)))
  }

  pub fn to_test_config(&self) -> Result<Option<TestConfig>, AnyError> {
    let files_config = self.to_files_config()?;
    let test_config = match self.json.test.clone() {
      Some(config) => {
        let test_config: SerializedTestConfig = serde_json::from_value(config)
          .context("Failed to parse \"test\" configuration")?;
        Some(test_config.into_resolved(&self.specifier)?)
      }
      None => None,
    };

    if files_config.is_none() && test_config.is_none() {
      return Ok(None);
    }

    let test_config = test_config.unwrap_or_default();
    let files_config = files_config.unwrap_or_default();

    Ok(Some(test_config.with_files(files_config)))
  }

  pub fn to_workspace_config(
    &self,
  ) -> Result<Option<WorkspaceConfig>, AnyError> {
    let Ok(config_file_path) = self.specifier.to_file_path() else {
      return Ok(None);
    };

    let config_file_directory = config_file_path.parent().unwrap();
    let mut members = Vec::with_capacity(self.json.members.len());

    for member in self.json.members.iter() {
      let member_path = config_file_directory.join(member);
      let member_deno_json = member_path.as_path().join("deno.json");
      if !member_deno_json.exists() {
        bail!(
          "Workspace member '{}' has no deno.json file ('{}')",
          member,
          member_deno_json.display()
        );
      }
      let member_config_file = ConfigFile::from_specifier_and_path(
        Url::from_file_path(&member_deno_json).unwrap(),
        &member_deno_json,
      )?;
      let Some(package_name) = &member_config_file.json.name else {
        bail!("Missing 'name' for workspace member {}", member);
      };
      let Some(package_version) = &member_config_file.json.version else {
        bail!("Missing 'version' for workspace member {}", member);
      };
      members.push(WorkspaceMemberConfig {
        member_name: member.to_string(),
        path: member_path,
        package_name: package_name.to_string(),
        package_version: package_version.to_string(),
        config_file: member_config_file,
      });
    }

    let base_import_map_value = self.to_import_map_value();

    Ok(Some(WorkspaceConfig {
      members,
      base_import_map_value,
    }))
  }

  pub fn to_bench_config(&self) -> Result<Option<BenchConfig>, AnyError> {
    let files_config = self.to_files_config()?;
    let bench_config = match self.json.bench.clone() {
      Some(config) => {
        let bench_config: SerializedBenchConfig =
          serde_json::from_value(config)
            .context("Failed to parse \"bench\" configuration")?;
        Some(bench_config.into_resolved(&self.specifier)?)
      }
      None => None,
    };

    if files_config.is_none() && bench_config.is_none() {
      return Ok(None);
    }

    let bench_config = bench_config.unwrap_or_default();
    let files_config = files_config.unwrap_or_default();

    Ok(Some(bench_config.with_files(files_config)))
  }

  /// Return any tasks that are defined in the configuration file as a sequence
  /// of JSON objects providing the name of the task and the arguments of the
  /// task in a detail field.
  pub fn to_lsp_tasks(&self) -> Option<Value> {
    let value = self.json.tasks.clone()?;
    let tasks: BTreeMap<String, String> = serde_json::from_value(value).ok()?;
    Some(
      tasks
        .into_iter()
        .map(|(key, value)| {
          json!({
            "name": key,
            "detail": value,
          })
        })
        .collect(),
    )
  }

  pub fn to_tasks_config(
    &self,
  ) -> Result<Option<IndexMap<String, String>>, AnyError> {
    if let Some(config) = self.json.tasks.clone() {
      let tasks_config: IndexMap<String, String> =
        serde_json::from_value(config)
          .context("Failed to parse \"tasks\" configuration")?;
      Ok(Some(tasks_config))
    } else {
      Ok(None)
    }
  }

  /// If the configuration file contains "extra" modules (like TypeScript
  /// `"types"`) options, return them as imports to be added to a module graph.
  pub fn to_maybe_imports(&self) -> Result<Vec<(Url, Vec<String>)>, AnyError> {
    let mut imports = Vec::new();
    let compiler_options_value =
      if let Some(value) = self.json.compiler_options.as_ref() {
        value
      } else {
        return Ok(Vec::new());
      };
    let compiler_options: CompilerOptions =
      serde_json::from_value(compiler_options_value.clone())?;
    if let Some(types) = compiler_options.types {
      imports.extend(types);
    }
    if !imports.is_empty() {
      let referrer = self.specifier.clone();
      Ok(vec![(referrer, imports)])
    } else {
      Ok(Vec::new())
    }
  }

  /// Based on the compiler options in the configuration file, return the
  /// JSX import source configuration.
  pub fn to_maybe_jsx_import_source_config(
    &self,
  ) -> Result<Option<JsxImportSourceConfig>, AnyError> {
    let Some(compiler_options_value) = self.json.compiler_options.as_ref() else {
      return Ok(None);
    };
    let Some(compiler_options) =
      serde_json::from_value::<CompilerOptions>(compiler_options_value.clone()).ok() else {
        return Ok(None);
      };
    let module = match compiler_options.jsx.as_deref() {
      Some("react-jsx") => "jsx-runtime".to_string(),
      Some("react-jsxdev") => "jsx-dev-runtime".to_string(),
      Some("react") | None => {
        if compiler_options.jsx_import_source.is_some() {
          bail!(
            "'jsxImportSource' is only supported when 'jsx' is set to 'react-jsx' or 'react-jsxdev'.\n  at {}",
            self.specifier,
          );
        }
        return Ok(None);
      }
      Some(setting) => bail!(
        "Unsupported 'jsx' compiler option value '{}'. Supported: 'react-jsx', 'react-jsxdev', 'react'\n  at {}",
        setting,
        self.specifier,
      ),
    };
    Ok(Some(JsxImportSourceConfig {
      default_specifier: compiler_options.jsx_import_source,
      module,
      base_url: self.specifier.clone(),
    }))
  }

  pub fn resolve_tasks_config(
    &self,
  ) -> Result<IndexMap<String, String>, AnyError> {
    let maybe_tasks_config = self.to_tasks_config()?;
    let tasks_config = maybe_tasks_config.unwrap_or_default();
    for key in tasks_config.keys() {
      if key.is_empty() {
        bail!("Configuration file task names cannot be empty");
      } else if !key
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | ':'))
      {
        bail!("Configuration file task names must only contain alpha-numeric characters, colons (:), underscores (_), or dashes (-). Task: {}", key);
      } else if !key.chars().next().unwrap().is_ascii_alphabetic() {
        bail!("Configuration file task names must start with an alphabetic character. Task: {}", key);
      }
    }
    Ok(tasks_config)
  }

  pub fn to_lock_config(&self) -> Result<Option<LockConfig>, AnyError> {
    if let Some(config) = self.json.lock.clone() {
      let lock_config: LockConfig = serde_json::from_value(config)
        .context("Failed to parse \"lock\" configuration")?;
      Ok(Some(lock_config))
    } else {
      Ok(None)
    }
  }

  pub fn resolve_lockfile_path(&self) -> Result<Option<PathBuf>, AnyError> {
    match self.to_lock_config()? {
      Some(LockConfig::Bool(lock)) if !lock => Ok(None),
      Some(LockConfig::PathBuf(lock)) => Ok(Some(
        self
          .specifier
          .to_file_path()
          .unwrap()
          .parent()
          .unwrap()
          .join(lock),
      )),
      _ => {
        let mut path = self.specifier.to_file_path().unwrap();
        path.set_file_name("deno.lock");
        Ok(Some(path))
      }
    }
  }
}

/// Represents the "default" type library that should be used when type
/// checking the code in the module graph.  Note that a user provided config
/// of `"lib"` would override this value.
#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
pub enum TsTypeLib {
  DenoWindow,
  DenoWorker,
  UnstableDenoWindow,
  UnstableDenoWorker,
}

impl Default for TsTypeLib {
  fn default() -> Self {
    Self::DenoWindow
  }
}

impl Serialize for TsTypeLib {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    let value = match self {
      Self::DenoWindow => vec!["deno.window".to_string()],
      Self::DenoWorker => vec!["deno.worker".to_string()],
      Self::UnstableDenoWindow => {
        vec!["deno.window".to_string(), "deno.unstable".to_string()]
      }
      Self::UnstableDenoWorker => {
        vec!["deno.worker".to_string(), "deno.unstable".to_string()]
      }
    };
    Serialize::serialize(&value, serializer)
  }
}

/// An enum that represents the base tsc configuration to return.
pub enum TsConfigType {
  /// Return a configuration for bundling, using swc to emit the bundle. This is
  /// independent of type checking.
  Bundle,
  /// Return a configuration to use tsc to type check. This
  /// is independent of either bundling or emitting via swc.
  Check { lib: TsTypeLib },
  /// Return a configuration to use swc to emit single module files.
  Emit,
}

pub struct TsConfigForEmit {
  pub ts_config: TsConfig,
  pub maybe_ignored_options: Option<IgnoredCompilerOptions>,
}

/// For a given configuration type and optionally a configuration file,
/// return a `TsConfig` struct and optionally any user configuration
/// options that were ignored.
pub fn get_ts_config_for_emit(
  config_type: TsConfigType,
  maybe_config_file: Option<&ConfigFile>,
) -> Result<TsConfigForEmit, AnyError> {
  let mut ts_config = match config_type {
    TsConfigType::Bundle => TsConfig::new(json!({
      "allowImportingTsExtensions": true,
      "checkJs": false,
      "emitDecoratorMetadata": false,
      "importsNotUsedAsValues": "remove",
      "inlineSourceMap": false,
      "inlineSources": false,
      "sourceMap": false,
      "jsx": "react",
      "jsxFactory": "React.createElement",
      "jsxFragmentFactory": "React.Fragment",
    })),
    TsConfigType::Check { lib } => TsConfig::new(json!({
      "allowJs": true,
      "allowImportingTsExtensions": true,
      "allowSyntheticDefaultImports": true,
      "checkJs": false,
      "emitDecoratorMetadata": false,
      "experimentalDecorators": true,
      "incremental": true,
      "jsx": "react",
      "importsNotUsedAsValues": "remove",
      "inlineSourceMap": true,
      "inlineSources": true,
      "isolatedModules": true,
      "lib": lib,
      "module": "esnext",
      "moduleDetection": "force",
      "noEmit": true,
      "resolveJsonModule": true,
      "sourceMap": false,
      "strict": true,
      "target": "esnext",
      "tsBuildInfoFile": "internal:///.tsbuildinfo",
      "useDefineForClassFields": true,
      // TODO(@kitsonk) remove for Deno 2.0
      "useUnknownInCatchVariables": false,
    })),
    TsConfigType::Emit => TsConfig::new(json!({
      "allowImportingTsExtensions": true,
      "checkJs": false,
      "emitDecoratorMetadata": false,
      "importsNotUsedAsValues": "remove",
      "inlineSourceMap": true,
      "inlineSources": true,
      "sourceMap": false,
      "jsx": "react",
      "jsxFactory": "React.createElement",
      "jsxFragmentFactory": "React.Fragment",
      "resolveJsonModule": true,
    })),
  };
  let maybe_ignored_options =
    ts_config.merge_tsconfig_from_config_file(maybe_config_file)?;
  Ok(TsConfigForEmit {
    ts_config,
    maybe_ignored_options,
  })
}

#[cfg(test)]
mod tests {
  use super::*;
  use pretty_assertions::assert_eq;
  use serde_json::json;
  use std::path::PathBuf;

  fn testdata_path() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"))).join("testdata")
  }

  fn unpack_object<T>(result: Result<Option<T>, AnyError>, name: &str) -> T {
    result
      .unwrap_or_else(|err| panic!("error parsing {name} object but got {err}"))
      .unwrap_or_else(|| panic!("{name} object should be defined"))
  }

  #[test]
  fn read_config_file_absolute() {
    let path = testdata_path().join("module_graph/tsconfig.json");
    let config_file = ConfigFile::read(path.as_path()).unwrap();
    assert!(config_file.json.compiler_options.is_some());
  }

  #[test]
  fn include_config_path_on_error() {
    let path = testdata_path().join("404.json");
    let error = ConfigFile::read(path.as_path()).err().unwrap();
    assert!(error.to_string().contains("404.json"));
  }

  #[test]
  fn test_json_merge() {
    let mut value_a = json!({
      "a": true,
      "b": "c"
    });
    let value_b = json!({
      "b": "d",
      "e": false,
    });
    json_merge(&mut value_a, &value_b);
    assert_eq!(
      value_a,
      json!({
        "a": true,
        "b": "d",
        "e": false,
      })
    );
  }

  #[test]
  fn test_parse_config() {
    let config_text = r#"{
      "compilerOptions": {
        "build": true,
        // comments are allowed
        "strict": true
      },
      "lint": {
        "include": ["src/"],
        "exclude": ["src/testdata/"],
        "rules": {
          "tags": ["recommended"],
          "include": ["ban-untagged-todo"]
        }
      },
      "fmt": {
        "include": ["src/"],
        "exclude": ["src/testdata/"],
        "useTabs": true,
        "lineWidth": 80,
        "indentWidth": 4,
        "singleQuote": true,
        "proseWrap": "preserve"
      },
      "tasks": {
        "build": "deno run --allow-read --allow-write build.ts",
        "server": "deno run --allow-net --allow-read server.ts"
      }
    }"#;
    let config_dir = Url::parse("file:///deno/").unwrap();
    let config_specifier = config_dir.join("tsconfig.json").unwrap();
    let config_file =
      ConfigFile::new(config_text, config_specifier.clone()).unwrap();
    let (options_value, ignored) = config_file.to_compiler_options().unwrap();
    assert!(options_value.is_object());
    let options = options_value.as_object().unwrap();
    assert!(options.contains_key("strict"));
    assert_eq!(options.len(), 1);
    assert_eq!(
      ignored,
      Some(IgnoredCompilerOptions {
        items: vec!["build".to_string()],
        maybe_specifier: Some(config_specifier),
      }),
    );

    assert_eq!(
      unpack_object(config_file.to_lint_config(), "lint"),
      LintConfig {
        files: FilesConfig {
          include: vec![PathBuf::from("/deno/src/")],
          exclude: vec![PathBuf::from("/deno/src/testdata/")],
        },
        rules: LintRulesConfig {
          include: Some(vec!["ban-untagged-todo".to_string()]),
          exclude: None,
          tags: Some(vec!["recommended".to_string()]),
        },
        ..Default::default()
      }
    );
    assert_eq!(
      unpack_object(config_file.to_fmt_config(), "fmt"),
      FmtConfig {
        files: FilesConfig {
          include: vec![PathBuf::from("/deno/src/")],
          exclude: vec![PathBuf::from("/deno/src/testdata/")],
        },
        options: FmtOptionsConfig {
          use_tabs: Some(true),
          line_width: Some(80),
          indent_width: Some(4),
          single_quote: Some(true),
          prose_wrap: Some(ProseWrap::Preserve),
          ..Default::default()
        },
      }
    );

    let tasks_config = config_file.to_tasks_config().unwrap().unwrap();
    assert_eq!(
      tasks_config["build"],
      "deno run --allow-read --allow-write build.ts",
    );
    assert_eq!(
      tasks_config["server"],
      "deno run --allow-net --allow-read server.ts"
    );
  }

  /// if either "include" or "exclude" is specified, "files" is ignored
  #[test]
  fn test_parse_config_with_deprecated_files_field() {
    let config_text = r#"{
      "lint": {
        "files": { "include": ["foo/"], "exclude": ["bar/"] },
        "include": ["src/"]
      },
      "fmt": {
        "files": { "include": ["foo/"], "exclude": ["bar/"] },
        "exclude": ["dist/"]
      },
      "bench": {
        "files": { "include": ["foo/"] },
        "include": ["src/"]
      },
      "test": {
        "files": { "include": ["foo/"] },
        "include": ["src/"]
      }
    }"#;
    let config_dir = Url::parse("file:///deno/").unwrap();
    let config_specifier = config_dir.join("tsconfig.json").unwrap();
    let config_file = ConfigFile::new(config_text, config_specifier).unwrap();

    let lint_files = unpack_object(config_file.to_lint_config(), "lint").files;
    assert_eq!(
      lint_files,
      FilesConfig {
        include: vec![PathBuf::from("/deno/src/")],
        exclude: vec![],
      }
    );

    let fmt_files = unpack_object(config_file.to_fmt_config(), "fmt").files;
    assert_eq!(
      fmt_files,
      FilesConfig {
        exclude: vec![PathBuf::from("/deno/dist/")],
        include: vec![],
      }
    );

    let test_include = unpack_object(config_file.to_test_config(), "test")
      .files
      .include;
    assert_eq!(test_include, vec![PathBuf::from("/deno/src/")]);

    let bench_include = unpack_object(config_file.to_bench_config(), "bench")
      .files
      .include;
    assert_eq!(bench_include, vec![PathBuf::from("/deno/src/")]);
  }

  #[test]
  fn test_parse_config_with_deprecated_files_field_only() {
    let config_text = r#"{
      "lint": { "files": { "include": ["src/"] } },
      "fmt": { "files": { "include": ["src/"] } },
      "test": { "files": { "exclude": ["dist/"] } },
      "bench": { "files": { "exclude": ["dist/"] } }
    }"#;
    let config_dir = Url::parse("file:///deno/").unwrap();
    let config_specifier = config_dir.join("tsconfig.json").unwrap();
    let config_file = ConfigFile::new(config_text, config_specifier).unwrap();

    let lint_include = unpack_object(config_file.to_lint_config(), "lint")
      .files
      .include;
    assert_eq!(lint_include, vec![PathBuf::from("/deno/src/")]);

    let fmt_include = unpack_object(config_file.to_fmt_config(), "fmt")
      .files
      .include;
    assert_eq!(fmt_include, vec![PathBuf::from("/deno/src/")]);

    let test_exclude = unpack_object(config_file.to_test_config(), "test")
      .files
      .exclude;
    assert_eq!(test_exclude, vec![PathBuf::from("/deno/dist/")]);

    let bench_exclude = unpack_object(config_file.to_bench_config(), "bench")
      .files
      .exclude;
    assert_eq!(bench_exclude, vec![PathBuf::from("/deno/dist/")]);
  }

  #[test]
  fn test_parse_config_with_deprecated_fmt_options() {
    let config_text_both = r#"{
      "fmt": {
        "options": {
          "semiColons": true
        },
        "semiColons": false
      }
    }"#;
    let config_text_deprecated = r#"{
      "fmt": {
        "options": {
          "semiColons": true
        }
      }
    }"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    let config_file_both =
      ConfigFile::new(config_text_both, config_specifier.clone()).unwrap();
    let config_file_deprecated =
      ConfigFile::new(config_text_deprecated, config_specifier).unwrap();

    fn unpack_options(config_file: ConfigFile) -> FmtOptionsConfig {
      unpack_object(config_file.to_fmt_config(), "fmt").options
    }

    let fmt_options_both = unpack_options(config_file_both);
    assert_eq!(fmt_options_both.semi_colons, Some(false));

    let fmt_options_deprecated = unpack_options(config_file_deprecated);
    assert_eq!(fmt_options_deprecated.semi_colons, Some(true));
  }

  #[test]
  fn test_parse_config_with_empty_file() {
    let config_text = "";
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    let config_file = ConfigFile::new(config_text, config_specifier).unwrap();
    let (options_value, _) = config_file.to_compiler_options().unwrap();
    assert!(options_value.is_object());
  }

  #[test]
  fn test_parse_config_with_commented_file() {
    let config_text = r#"//{"foo":"bar"}"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    let config_file = ConfigFile::new(config_text, config_specifier).unwrap();
    let (options_value, _) = config_file.to_compiler_options().unwrap();
    assert!(options_value.is_object());
  }

  #[test]
  fn test_parse_config_with_global_files() {
    let config_text = r#"{
      "exclude": ["foo/"],
      "test": {
        "exclude": ["npm/"],
      },
      "bench": {}
    }"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    let config_file = ConfigFile::new(config_text, config_specifier).unwrap();

    let (options_value, _) = config_file.to_compiler_options().unwrap();
    assert!(options_value.is_object());

    let test_config = config_file.to_test_config().unwrap().unwrap();
    assert_eq!(test_config.files.include, Vec::<PathBuf>::new());
    assert_eq!(
      test_config.files.exclude,
      vec![PathBuf::from("/deno/npm/"), PathBuf::from("/deno/foo/")]
    );

    let bench_config = config_file.to_bench_config().unwrap().unwrap();
    assert_eq!(
      bench_config.files.exclude,
      vec![PathBuf::from("/deno/foo/")]
    );
  }

  #[test]
  fn test_parse_config_with_global_files_only() {
    let config_text = r#"{
      "exclude": ["npm/"]
    }"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    let config_file = ConfigFile::new(config_text, config_specifier).unwrap();

    let (options_value, _) = config_file.to_compiler_options().unwrap();
    assert!(options_value.is_object());

    let empty_include = Vec::<PathBuf>::new();

    let files_config = config_file.to_files_config().unwrap().unwrap();
    assert_eq!(files_config.include, empty_include);
    assert_eq!(files_config.exclude, vec![PathBuf::from("/deno/npm/")]);

    let lint_config = config_file.to_lint_config().unwrap().unwrap();
    assert_eq!(lint_config.files.include, empty_include);
    assert_eq!(lint_config.files.exclude, vec![PathBuf::from("/deno/npm/")]);

    let fmt_config = config_file.to_fmt_config().unwrap().unwrap();
    assert_eq!(fmt_config.files.include, empty_include);
    assert_eq!(fmt_config.files.exclude, vec![PathBuf::from("/deno/npm/")],);
  }

  #[test]
  fn test_parse_config_with_invalid_file() {
    let config_text = "{foo:bar}";
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    // Emit error: Unable to parse config file JSON "<config_path>" because of Unexpected token on line 1 column 6.
    assert!(ConfigFile::new(config_text, config_specifier).is_err());
  }

  #[test]
  fn test_parse_config_with_not_object_file() {
    let config_text = "[]";
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    // Emit error: config file JSON "<config_path>" should be an object
    assert!(ConfigFile::new(config_text, config_specifier).is_err());
  }

  #[test]
  fn test_jsx_invalid_setting() {
    let config_text = r#"{ "compilerOptions": { "jsx": "preserve" } }"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    let config = ConfigFile::new(config_text, config_specifier).unwrap();
    assert_eq!(
      config.to_maybe_jsx_import_source_config().err().unwrap().to_string(),
      concat!(
        "Unsupported 'jsx' compiler option value 'preserve'. Supported: 'react-jsx', 'react-jsxdev', 'react'\n",
        "  at file:///deno/tsconfig.json",
      ),
    );
  }

  #[test]
  fn test_jsx_import_source_only() {
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    {
      let config_text =
        r#"{ "compilerOptions": { "jsxImportSource": "test" } }"#;
      let config =
        ConfigFile::new(config_text, config_specifier.clone()).unwrap();
      assert_eq!(
        config.to_maybe_jsx_import_source_config().err().unwrap().to_string(),
        concat!(
          "'jsxImportSource' is only supported when 'jsx' is set to 'react-jsx' or 'react-jsxdev'.\n",
          "  at file:///deno/tsconfig.json",
        ),
      );
    }
    {
      let config_text = r#"{ "compilerOptions": { "jsx": "react", "jsxImportSource": "test" } }"#;
      let config = ConfigFile::new(config_text, config_specifier).unwrap();
      assert_eq!(
        config.to_maybe_jsx_import_source_config().err().unwrap().to_string(),
        concat!(
          "'jsxImportSource' is only supported when 'jsx' is set to 'react-jsx' or 'react-jsxdev'.\n",
          "  at file:///deno/tsconfig.json",
        ),
      );
    }
  }

  #[test]
  fn test_jsx_import_source_valid() {
    let config_text = r#"{ "compilerOptions": { "jsx": "react" } }"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    assert!(ConfigFile::new(config_text, config_specifier).is_ok());
  }

  #[test]
  fn test_tsconfig_as_bytes() {
    let mut tsconfig1 = TsConfig::new(json!({
      "strict": true,
      "target": "esnext",
    }));
    tsconfig1.merge(&json!({
      "target": "es5",
      "module": "amd",
    }));
    let mut tsconfig2 = TsConfig::new(json!({
      "target": "esnext",
      "strict": true,
    }));
    tsconfig2.merge(&json!({
      "module": "amd",
      "target": "es5",
    }));
    assert_eq!(tsconfig1.as_bytes(), tsconfig2.as_bytes());
  }

  #[test]
  fn discover_from_success() {
    // testdata/fmt/deno.jsonc exists
    let testdata = testdata_path();
    let c_md = testdata.join("fmt/with_config/subdir/c.md");
    let mut checked = HashSet::new();
    let config_file = ConfigFile::discover_from(&c_md, &mut checked)
      .unwrap()
      .unwrap();
    assert!(checked.contains(c_md.parent().unwrap()));
    assert!(!checked.contains(testdata.as_path()));
    let fmt_config = config_file.to_fmt_config().unwrap().unwrap();
    let expected_exclude =
      Url::from_file_path(testdata.join("fmt/with_config/subdir/b.ts"))
        .unwrap()
        .to_file_path()
        .unwrap();
    assert_eq!(fmt_config.files.exclude, vec![expected_exclude]);

    // Now add all ancestors of testdata to checked.
    for a in testdata.as_path().ancestors() {
      checked.insert(a.to_path_buf());
    }

    // If we call discover_from again starting at testdata, we ought to get None.
    assert!(ConfigFile::discover_from(testdata.as_path(), &mut checked)
      .unwrap()
      .is_none());
  }

  #[test]
  fn discover_from_malformed() {
    let testdata = testdata_path();
    let d = testdata.join("malformed_config/");
    let mut checked = HashSet::new();
    let err = ConfigFile::discover_from(d.as_path(), &mut checked).unwrap_err();
    assert!(err.to_string().contains("Unable to parse config file"));
  }

  #[test]
  fn task_name_invalid_chars() {
    run_task_error_test(
            r#"{
        "tasks": {
          "build": "deno test",
          "some%test": "deno bundle mod.ts"
        }
      }"#,
            concat!(
                "Configuration file task names must only contain alpha-numeric ",
                "characters, colons (:), underscores (_), or dashes (-). Task: some%test",
            ),
        );
  }

  #[test]
  fn task_name_non_alpha_starting_char() {
    run_task_error_test(
      r#"{
        "tasks": {
          "build": "deno test",
          "1test": "deno bundle mod.ts"
        }
      }"#,
      concat!(
        "Configuration file task names must start with an ",
        "alphabetic character. Task: 1test",
      ),
    );
  }

  #[test]
  fn task_name_empty() {
    run_task_error_test(
      r#"{
        "tasks": {
          "build": "deno test",
          "": "deno bundle mod.ts"
        }
      }"#,
      "Configuration file task names cannot be empty",
    );
  }

  fn run_task_error_test(config_text: &str, expected_error: &str) {
    let config_dir = Url::parse("file:///deno/").unwrap();
    let config_specifier = config_dir.join("tsconfig.json").unwrap();
    let config_file = ConfigFile::new(config_text, config_specifier).unwrap();
    assert_eq!(
      config_file
        .resolve_tasks_config()
        .err()
        .unwrap()
        .to_string(),
      expected_error,
    );
  }

  #[test]
  fn test_specifier_parent() {
    run_test("file:///", "file:///");
    run_test("file:///test", "file:///");
    run_test("file:///test/", "file:///");
    run_test("file:///test/other", "file:///test/");
    run_test("file:///test/other.txt", "file:///test/");
    run_test("file:///test/other/", "file:///test/");

    fn run_test(specifier: &str, expected: &str) {
      let result = specifier_parent(&Url::parse(specifier).unwrap());
      assert_eq!(result.to_string(), expected);
    }
  }

  #[test]
  fn test_specifier_to_file_path() {
    run_success_test("file:///", "/");
    run_success_test("file:///test", "/test");
    run_success_test("file:///dir/test/test.txt", "/dir/test/test.txt");
    run_success_test(
      "file:///dir/test%20test/test.txt",
      "/dir/test test/test.txt",
    );

    fn run_success_test(specifier: &str, expected_path: &str) {
      let result =
        specifier_to_file_path(&Url::parse(specifier).unwrap()).unwrap();
      assert_eq!(result, PathBuf::from(expected_path));
    }
  }
}
