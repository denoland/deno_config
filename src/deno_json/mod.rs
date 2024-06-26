// Copyright 2018-2024 the Deno authors. MIT license.

use anyhow::bail;
use anyhow::Context;
use anyhow::Error as AnyError;
use import_map::ImportMapWithDiagnostics;
use indexmap::IndexMap;
use jsonc_parser::common::Ranged;
use jsonc_parser::CollectOptions;
use jsonc_parser::ParseResult;
use serde::Deserialize;
use serde::Serialize;
use serde::Serializer;
use serde_json::json;
use serde_json::Value;
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::future::Future;
use std::path::Path;
use std::path::PathBuf;
use thiserror::Error;
use ts::parse_compiler_options;
use url::Url;

use crate::fs::DenoConfigFs;
use crate::glob::FilePatterns;
use crate::glob::PathOrPatternSet;
use crate::util::is_skippable_io_error;
use crate::util::normalize_path;
use crate::util::specifier_parent;
use crate::util::specifier_to_file_path;
use crate::SpecifierToFilePathError;

mod ts;

pub use ts::CompilerOptions;
pub use ts::EmitConfigOptions;
pub use ts::IgnoredCompilerOptions;
pub use ts::JsxImportSourceConfig;
pub use ts::TsConfig;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum ConfigFlag {
  #[default]
  Discover,
  Path(String),
  Disabled,
}

#[derive(Clone, Debug, Default, Deserialize, Hash, PartialEq)]
#[serde(default, deny_unknown_fields)]
pub struct LintRulesConfig {
  pub tags: Option<Vec<String>>,
  pub include: Option<Vec<String>>,
  pub exclude: Option<Vec<String>>,
}

#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields)]
struct SerializedFilesConfig {
  pub include: Option<Vec<String>>,
  pub exclude: Vec<String>,
}

impl SerializedFilesConfig {
  pub fn into_resolved(
    self,
    config_file_specifier: &Url,
  ) -> Result<FilePatterns, AnyError> {
    let config_dir =
      specifier_to_file_path(&specifier_parent(config_file_specifier))?;
    Ok(FilePatterns {
      base: config_dir.clone(),
      include: match self.include {
        Some(i) => Some(
          PathOrPatternSet::from_include_relative_path_or_patterns(
            &config_dir,
            &i,
          )
          .context("Invalid include.")?,
        ),
        None => None,
      },
      exclude: PathOrPatternSet::from_exclude_relative_path_or_patterns(
        &config_dir,
        &self.exclude,
      )
      .context("Invalid exclude.")?,
    })
  }

  pub fn is_empty(&self) -> bool {
    self.include.is_none() && self.exclude.is_empty()
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
  mut deprecated_files: SerializedFilesConfig,
) -> SerializedFilesConfig {
  const DEPRECATED_FILES: &str =
    "Warning: \"files\" configuration is deprecated";
  const FLAT_CONFIG: &str = "\"include\" and \"exclude\"";

  // only consider files as empty if it's include is empty
  // because this code might be merging a top level config
  // "exclude" in.
  let files_empty =
    files.include.as_ref().map(|i| i.is_empty()).unwrap_or(true);
  let (files_nonempty, deprecated_files_nonempty) =
    (!files_empty, !deprecated_files.is_empty());

  match (files_nonempty, deprecated_files_nonempty) {
    (true, true) => {
      log::warn!("{DEPRECATED_FILES} and ignored by {FLAT_CONFIG}.");
      files
    }
    (false, true) => {
      log::warn!("{DEPRECATED_FILES}. Please use {FLAT_CONFIG} instead.");
      // combine the excludes
      let mut exclude = files.exclude;
      exclude.extend(std::mem::take(&mut deprecated_files.exclude));
      deprecated_files.exclude = exclude;
      deprecated_files
    }
    _ => files,
  }
}

/// `lint` config representation for serde
///
/// fields `include` and `exclude` are expanded from [SerializedFilesConfig].
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields)]
struct SerializedLintConfig {
  pub rules: LintRulesConfig,
  pub include: Option<Vec<String>>,
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
    })
  }
}

#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct WorkspaceLintConfig {
  pub report: Option<String>,
}

#[derive(Clone, Debug, Hash, PartialEq)]
pub struct LintConfig {
  pub rules: LintRulesConfig,
  pub files: FilePatterns,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, Hash, PartialEq)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub enum ProseWrap {
  Always,
  Never,
  Preserve,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize, Hash, PartialEq)]
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
  pub include: Option<Vec<String>>,
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

#[derive(Clone, Debug, Hash, PartialEq)]
pub struct FmtConfig {
  pub options: FmtOptionsConfig,
  pub files: FilePatterns,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExportsConfig {
  base: Url,
  map: IndexMap<String, String>,
}

impl ExportsConfig {
  pub fn into_map(self) -> IndexMap<String, String> {
    self.map
  }

  pub fn get(&self, export_name: &str) -> Option<&String> {
    self.map.get(export_name)
  }

  pub fn get_resolved(
    &self,
    export_name: &str,
  ) -> Result<Option<Url>, url::ParseError> {
    match self.get(export_name) {
      Some(name) => self.base.join(name).map(Some),
      None => Ok(None),
    }
  }
}

/// `test` config representation for serde
///
/// fields `include` and `exclude` are expanded from [SerializedFilesConfig].
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields)]
struct SerializedTestConfig {
  pub include: Option<Vec<String>>,
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

#[derive(Clone, Debug, Hash, PartialEq)]
pub struct TestConfig {
  pub files: FilePatterns,
}

/// `publish` config representation for serde
///
/// fields `include` and `exclude` are expanded from [SerializedFilesConfig].
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields)]
struct SerializedPublishConfig {
  pub include: Option<Vec<String>>,
  pub exclude: Vec<String>,
}

impl SerializedPublishConfig {
  pub fn into_resolved(
    self,
    config_file_specifier: &Url,
  ) -> Result<PublishConfig, AnyError> {
    let (include, exclude) = (self.include, self.exclude);
    let files = SerializedFilesConfig { include, exclude };

    Ok(PublishConfig {
      files: files.into_resolved(config_file_specifier)?,
    })
  }
}

#[derive(Clone, Debug, Hash, PartialEq)]
pub struct PublishConfig {
  pub files: FilePatterns,
}

/// `bench` config representation for serde
///
/// fields `include` and `exclude` are expanded from [SerializedFilesConfig].
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields)]
struct SerializedBenchConfig {
  pub include: Option<Vec<String>>,
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

#[derive(Clone, Debug, PartialEq)]
pub struct BenchConfig {
  pub files: FilePatterns,
}

#[derive(Clone, Debug, Deserialize, PartialEq)]
#[serde(untagged)]
pub enum LockConfig {
  Bool(bool),
  PathBuf(PathBuf),
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Task {
  Definition(String),
  Commented {
    definition: String,
    comments: Vec<String>,
  },
}

impl Task {
  pub fn definition(&self) -> &str {
    match self {
      Task::Definition(d) => d,
      Task::Commented { definition, .. } => definition,
    }
  }
}

#[derive(Debug, Error)]
pub enum ConfigFileReadError {
  #[error("Could not convert config file path to specifier. Path: {0}")]
  PathToUrl(PathBuf),
  #[error(transparent)]
  SpecifierToFilePathError(#[from] SpecifierToFilePathError),
  #[error("Error reading config file '{}'.", specifier)]
  FailedReading {
    specifier: Url,
    #[source]
    source: std::io::Error,
  },
  #[error("Unable to parse config file JSON {}.", specifier)]
  Parse {
    specifier: Url,
    #[source]
    source: Box<jsonc_parser::errors::ParseError>,
  },
  #[error("Failed deserializing config file '{}'.", specifier)]
  Deserialize {
    specifier: Url,
    #[source]
    source: serde_json::Error,
  },
  #[error("Config file JSON should be an object '{}'.", specifier)]
  NotObject { specifier: Url },
}

impl ConfigFileReadError {
  pub fn is_not_found(&self) -> bool {
    if let ConfigFileReadError::FailedReading { source: ioerr, .. } = self {
      matches!(ioerr.kind(), std::io::ErrorKind::NotFound)
    } else {
      false
    }
  }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
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
  pub publish: Option<Value>,

  pub name: Option<String>,
  pub version: Option<String>,
  pub workspace: Option<Vec<String>>,
  #[serde(rename = "workspaces")]
  pub(crate) deprecated_workspaces: Option<Vec<String>>,
  pub exports: Option<Value>,
  #[serde(default)]
  pub unstable: Vec<String>,
}

/// collects comments attached to tasks and
/// returns a new object where each task
/// has a list of the comments that accompanied it.
/// i.e. it will be the following form
///
/// ```json
/// {
///   "tasks": {
///     "task1": {
///       "comments": ["first comment line", "second comment line"],
///       "definition": "deno run ..."
///     }
///   }
/// }
/// ```
fn decorate_tasks_json(
  text: &str,
  tokens: &[jsonc_parser::tokens::TokenAndRange<'_>],
  comments: &HashMap<usize, std::rc::Rc<Vec<jsonc_parser::ast::Comment<'_>>>>,
  tasks: &jsonc_parser::ast::Object,
) -> Value {
  let mut new_tasks = serde_json::Map::new();

  // we want to exclude comments that aren't on their own line
  // so the roundabout method here is to
  // figure out whether there's a newline between the
  // previous token and the comment in question

  let task_tokens_start = tokens
    .binary_search_by(|t| {
      // we want the greatest token that is less than or equal to the start of the tasks
      if t.range.end <= tasks.range.start {
        std::cmp::Ordering::Less
      } else {
        std::cmp::Ordering::Greater
      }
    })
    .unwrap_err();
  let task_tokens_end = tokens[task_tokens_start..]
    .iter()
    .take_while(|t| t.range.end <= tasks.range.end)
    .count()
    + task_tokens_start;

  let task_tokens = &tokens[task_tokens_start..task_tokens_end];

  for prop in &tasks.properties {
    let prop_comments =
      comments.get(&prop.range.start).cloned().unwrap_or_default();

    let mut comment_texts = Vec::with_capacity(prop_comments.len());

    for comment in prop_comments.iter() {
      let token_pos = task_tokens
        .binary_search_by(|t| {
          // we want to find the greatest token that is less than the start of comment
          // (we can't search for token end == comment start because the
          // preceding range might be a comment)
          if t.range.end <= comment.range().start {
            std::cmp::Ordering::Less
          } else {
            std::cmp::Ordering::Greater
          }
        })
        .unwrap_err();
      // the previous and next tokens
      match (task_tokens.get(token_pos - 1), task_tokens.get(token_pos)) {
        (Some(prev), Some(next)) => {
          // on a different line than the previous and next tokens
          if text[prev.range.end..comment.range().start].contains('\n')
            && text[comment.range().end..next.range.start].contains('\n')
          {
            let comment_lines = comment.text().trim().split('\n').map(|s| {
              s.trim().trim_start_matches('*').trim_start().to_string()
            });
            comment_texts.extend(comment_lines);
          } else {
            continue;
          }
        }
        _ => continue,
      };
    }

    new_tasks.insert(
      prop.name.as_str().to_string(),
      json!({
        "comments": comment_texts,
        "definition": Value::from(prop.value.clone()),
      }),
    );
  }

  Value::Object(new_tasks)
}

#[derive(Clone, Debug, Default)]
pub struct ConfigParseOptions {
  pub include_task_comments: bool,
}

#[derive(Clone, Debug)]
pub struct ConfigFile {
  pub specifier: Url,
  pub json: ConfigFileJson,
}

impl ConfigFile {
  /// Filenames that Deno will recognize when discovering config.
  pub(crate) fn resolve_config_file_names<'a>(
    additional_config_file_names: &[&'a str],
  ) -> Cow<'a, [&'a str]> {
    const CONFIG_FILE_NAMES: [&str; 2] = ["deno.json", "deno.jsonc"];
    if additional_config_file_names.is_empty() {
      Cow::Borrowed(&CONFIG_FILE_NAMES)
    } else {
      Cow::Owned(
        CONFIG_FILE_NAMES
          .iter()
          .copied()
          .chain(additional_config_file_names.iter().copied())
          .collect::<Vec<_>>(),
      )
    }
  }

  pub fn discover_from(
    fs: &dyn DenoConfigFs,
    start: &Path,
    additional_config_file_names: &[&str],
    parse_options: &ConfigParseOptions,
  ) -> Result<Option<ConfigFile>, ConfigFileReadError> {
    fn is_skippable_err(e: &ConfigFileReadError) -> bool {
      if let ConfigFileReadError::FailedReading { source: ioerr, .. } = e {
        is_skippable_io_error(ioerr)
      } else {
        false
      }
    }

    let config_file_names =
      Self::resolve_config_file_names(additional_config_file_names);

    debug_assert!(start.is_absolute());
    for ancestor in start.ancestors() {
      for config_filename in config_file_names.iter() {
        let f = ancestor.join(config_filename);
        match ConfigFile::read(fs, &f, parse_options) {
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
    // No config file found.
    Ok(None)
  }

  pub fn read(
    fs: &dyn DenoConfigFs,
    config_path: &Path,
    parse_options: &ConfigParseOptions,
  ) -> Result<Self, ConfigFileReadError> {
    debug_assert!(config_path.is_absolute());
    let specifier = Url::from_file_path(config_path)
      .map_err(|_| ConfigFileReadError::PathToUrl(config_path.to_path_buf()))?;
    Self::from_specifier_and_path(fs, specifier, config_path, parse_options)
  }

  pub fn from_specifier(
    fs: &dyn DenoConfigFs,
    specifier: Url,
    parse_options: &ConfigParseOptions,
  ) -> Result<Self, ConfigFileReadError> {
    let config_path = specifier_to_file_path(&specifier)
      .context("Invalid config file path.")?;
    Self::from_specifier_and_path(specifier, &config_path, parse_options)
  }

  fn from_specifier_and_path(
    fs: &dyn DenoConfigFs,
    specifier: Url,
    config_path: &Path,
    parse_options: &ConfigParseOptions,
  ) -> Result<Self, ConfigFileReadError> {
    let text = fs.read_to_string(config_path).map_err(|err| {
      ConfigFileReadError::FailedReading {
        specifier: specifier.clone(),
        source: err,
      }
    })?;
    Self::new(&text, specifier, parse_options)
  }

  pub fn new(
    text: &str,
    specifier: Url,
    parse_options: &ConfigParseOptions,
  ) -> Result<Self, ConfigFileReadError> {
    let need_comments_tokens = parse_options.include_task_comments;
    let jsonc = match jsonc_parser::parse_to_ast(
      text,
      &CollectOptions {
        comments: need_comments_tokens,
        tokens: need_comments_tokens,
      },
      &Default::default(),
    ) {
      Ok(ParseResult {
        comments: Some(comments),
        value: Some(jsonc_parser::ast::Value::Object(value)),
        tokens: Some(tokens),
        ..
      }) => {
        let mut value_json =
          Value::from(jsonc_parser::ast::Value::Object(value.clone()));
        if let Some(tasks) = value.get_object("tasks") {
          let decorated_tasks =
            decorate_tasks_json(text, &tokens, &comments, tasks);
          value_json["tasks"] = decorated_tasks
        }
        value_json
      }
      Ok(ParseResult {
        comments: None,
        value: Some(value @ jsonc_parser::ast::Value::Object(_)),
        tokens: None,
        ..
      }) => Value::from(value),
      Ok(ParseResult { value: None, .. }) => {
        json!({})
      }
      Err(e) => {
        return Err(ConfigFileReadError::Parse {
          specifier,
          source: Box::new(e),
        });
      }
      _ => {
        return Err(ConfigFileReadError::NotObject { specifier });
      }
    };
    let json: ConfigFileJson =
      serde_json::from_value(jsonc).map_err(|err| {
        ConfigFileReadError::Deserialize {
          specifier: specifier.clone(),
          source: err,
        }
      })?;

    Ok(Self { specifier, json })
  }

  pub fn dir_path(&self) -> PathBuf {
    specifier_to_file_path(&self.specifier)
      .unwrap()
      .parent()
      .unwrap()
      .to_path_buf()
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

  pub fn to_import_map_specifier(&self) -> Result<Option<Url>, AnyError> {
    let Some(value) = self.json.import_map.as_ref() else {
      return Ok(None);
    };
    // try to resolve as a url
    if let Ok(specifier) = Url::parse(value) {
      return Ok(Some(specifier));
    }
    // now as a relative file path
    if let Ok(config_file_path) = self.specifier.to_file_path() {
      // people may specify a file path without a leading `./` so
      // this handles that
      let path = config_file_path.parent().unwrap().join(value);
      Url::from_file_path(normalize_path(&path))
        .map_err(|()| {
          anyhow::anyhow!("Failed converting {} to url.", path.display())
        })
        .map(Some)
    } else {
      Ok(Some(self.specifier.join(value)?))
    }
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

  /// Resolves the import map potentially resolving the file specified
  /// at the "importMap" entry.
  pub async fn to_import_map<
    TReturn: Future<Output = Result<String, AnyError>>,
  >(
    &self,
    fetch_text: impl Fn(&Url) -> TReturn,
  ) -> Result<Option<ImportMapWithDiagnostics>, AnyError> {
    let maybe_result = self.to_import_map_value(fetch_text).await?;
    match maybe_result {
      Some((specifier, value)) => {
        let import_map =
          import_map::parse_from_value(specifier.into_owned(), value)?;
        Ok(Some(import_map))
      }
      None => Ok(None),
    }
  }

  /// Resolves the import map `serde_json::Value` potentially resolving the
  /// file specified at the "importMap" entry.
  pub async fn to_import_map_value<
    TReturn: Future<Output = Result<String, AnyError>>,
  >(
    &self,
    fetch_text: impl Fn(&Url) -> TReturn,
  ) -> Result<Option<(Cow<Url>, serde_json::Value)>, AnyError> {
    // has higher precedence over the path
    if self.json.imports.is_some() || self.json.scopes.is_some() {
      Ok(Some((
        Cow::Borrowed(&self.specifier),
        self.to_import_map_value_from_imports(),
      )))
    } else {
      match self.to_import_map_specifier()? {
        Some(import_map_specifier) => {
          let text = fetch_text(&import_map_specifier).await?;
          let value = serde_json::from_str(&text)?;
          // does not expand the imports because this one will use the import map standard
          Ok(Some((Cow::Owned(import_map_specifier), value)))
        }
        None => Ok(None),
      }
    }
  }

  /// Creates the import map from the imports entry.
  ///
  /// Warning: This does not take into account the 'importMap' entry. Use `to_import_map` instead.
  pub fn to_import_map_from_imports(
    &self,
  ) -> Result<ImportMapWithDiagnostics, AnyError> {
    let value = self.to_import_map_value_from_imports();
    let result = import_map::parse_from_value(self.specifier.clone(), value)?;
    Ok(result)
  }

  pub fn to_import_map_value_from_imports(&self) -> Value {
    let mut value = serde_json::Map::with_capacity(2);
    if let Some(imports) = &self.json.imports {
      value.insert("imports".to_string(), imports.clone());
    }
    if let Some(scopes) = &self.json.scopes {
      value.insert("scopes".to_string(), scopes.clone());
    }
    import_map::ext::expand_import_map_value(Value::Object(value))
  }

  pub fn is_an_import_map(&self) -> bool {
    self.json.imports.is_some() || self.json.scopes.is_some()
  }

  pub fn is_package(&self) -> bool {
    self.json.name.is_some() && self.json.exports.is_some()
  }

  pub fn has_unstable(&self, name: &str) -> bool {
    self.json.unstable.iter().any(|v| v == name)
  }

  /// Resolve the export values in a config file to their URLs.
  pub fn resolve_export_value_urls(&self) -> Result<Vec<Url>, AnyError> {
    let exports_config = self
      .to_exports_config()
      .with_context(|| {
        format!("Failed to parse exports at {}", self.specifier)
      })?
      .into_map();
    let mut exports = Vec::with_capacity(exports_config.len());
    for (_, value) in exports_config {
      let entry_point = self.specifier.join(&value).with_context(|| {
        format!("Failed to join {} with {}", self.specifier, value)
      })?;
      exports.push(entry_point);
    }
    Ok(exports)
  }

  pub fn to_exports_config(&self) -> Result<ExportsConfig, AnyError> {
    fn has_extension(value: &str) -> bool {
      let search_text = &value[value.rfind('/').unwrap_or(0)..];
      search_text.contains('.')
    }

    fn validate_key(
      key_display: &dyn Fn() -> Cow<'static, str>,
      key: &str,
    ) -> Result<(), AnyError> {
      if key == "." {
        return Ok(());
      }
      if key.is_empty() {
        bail!(
          "The {} must not be empty. Use '.' if you meant the root export.",
          key_display()
        );
      }
      if !key.starts_with("./") {
        let suggestion = if key.starts_with('/') {
          format!(".{}", key)
        } else {
          format!("./{}", key)
        };
        bail!(
          "The {} must start with './'. Did you mean '{suggestion}'?",
          key_display(),
        );
      }
      if key.ends_with('/') {
        let suggestion = key.trim_end_matches('/');
        bail!(
          "The {} must not end with '/'. Did you mean '{suggestion}'?",
          key_display(),
        );
      }
      // ban anything that is not [a-zA-Z0-9_-./]
      if key.chars().any(|c| {
        !matches!(c, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_' | '-' | '.' | '/')
      }) {
        bail!(
          "The {} must only contain alphanumeric characters, underscores (_), dashes (-), dots (.), and slashes (/).",
          key_display()
        );
      }
      // ban parts consisting of only dots, and empty parts (e.g. `./foo//bar`)
      for part in key.split('/').skip(1) {
        if part.is_empty() || part.chars().all(|c| c == '.') {
          bail!(
            "The {} must not contain double slashes (//), or parts consisting entirely of dots (.).",
            key_display()
          );
        }
      }
      Ok(())
    }

    fn validate_value(
      key_display: &dyn Fn() -> Cow<'static, str>,
      value: &str,
    ) -> Result<(), AnyError> {
      if value.is_empty() {
        bail!("The path for the {} must not be empty.", key_display());
      }
      if !value.starts_with("./") {
        let suggestion = if value.starts_with('/') {
          format!(".{}", value)
        } else {
          format!("./{}", value)
        };
        bail!(
          "The path '{value}' at the {} could not be resolved as a relative path from the config file. Did you mean '{suggestion}'?",
          key_display(),
        );
      }
      if value.ends_with('/') {
        let suggestion = value.trim_end_matches('/');
        bail!(
          "The path '{value}' at the {} must not end with '/'. Did you mean '{suggestion}'?",
          key_display(),
        );
      }
      if !has_extension(value) {
        bail!(
          "The path '{value}' at the {} is missing a file extension. Add a file extension such as '.js' or '.ts'.",
          key_display()
        );
      }
      Ok(())
    }

    let map = match &self.json.exports {
      Some(Value::Object(map)) => {
        let mut result = IndexMap::with_capacity(map.len());
        for (k, v) in map {
          let key_display = || Cow::Owned(format!("'{}' export", k));
          validate_key(&key_display, k)?;
          match v {
            Value::String(value) => {
              validate_value(&key_display, value)?;
              result.insert(k.clone(), value.clone());
            }
            Value::Object(_) => {
              bail!("The path of the {} must be a string, found invalid value '{}'. Exports in deno.json do not support conditional exports.", key_display(), v);
            }
            Value::Bool(_)
            | Value::Number(_)
            | Value::Array(_)
            | Value::Null => {
              bail!("The path of the {} must be a string, found invalid value '{}'.", key_display(), v);
            }
          }
        }
        result
      }
      Some(Value::String(value)) => {
        validate_value(&|| "root export".into(), value)?;
        IndexMap::from([(".".to_string(), value.clone())])
      }
      Some(
        v @ Value::Bool(_)
        | v @ Value::Array(_)
        | v @ Value::Number(_)
        | v @ Value::Null,
      ) => {
        bail!("The 'exports' key must be a string or object, found invalid value '{v}'.");
      }
      None => IndexMap::new(),
    };

    Ok(ExportsConfig {
      base: self.specifier.clone(),
      map,
    })
  }

  pub fn to_files_config(&self) -> Result<FilePatterns, AnyError> {
    let exclude = self.resolve_exclude_patterns()?;
    let raw_files_config = SerializedFilesConfig {
      exclude,
      ..Default::default()
    };
    raw_files_config
      .into_resolved(&self.specifier)
      .context("Invalid exclude config.")
  }

  fn resolve_exclude_patterns(&self) -> Result<Vec<String>, AnyError> {
    let mut exclude: Vec<String> =
      if let Some(exclude) = self.json.exclude.clone() {
        serde_json::from_value(exclude)
          .context("Failed to parse \"exclude\" configuration")?
      } else {
        Vec::new()
      };

    if self.json.vendor == Some(true) {
      exclude.push("vendor".to_string());
    }
    Ok(exclude)
  }

  pub fn to_bench_config(&self) -> Result<Option<BenchConfig>, AnyError> {
    let mut exclude_patterns = self.resolve_exclude_patterns()?;
    let serialized = match self.json.bench.clone() {
      Some(config) => {
        let mut serialized: SerializedBenchConfig =
          serde_json::from_value(config)
            .context("Failed to parse \"bench\" configuration")?;
        // top level excludes at the start because they're lower priority
        exclude_patterns.extend(std::mem::take(&mut serialized.exclude));
        serialized.exclude = exclude_patterns;
        serialized
      }
      None => return Ok(None),
    };

    serialized
      .into_resolved(&self.specifier)
      .context("Invalid bench config.")
      .map(Some)
  }

  pub fn to_fmt_config(&self) -> Result<Option<FmtConfig>, AnyError> {
    let mut exclude_patterns = self.resolve_exclude_patterns()?;
    let serialized = match self.json.fmt.clone() {
      Some(config) => {
        let mut serialized: SerializedFmtConfig =
          serde_json::from_value(config)
            .context("Failed to parse \"fmt\" configuration")?;
        // top level excludes at the start because they're lower priority
        exclude_patterns.extend(std::mem::take(&mut serialized.exclude));
        serialized.exclude = exclude_patterns;
        serialized
      }
      None if !exclude_patterns.is_empty() => SerializedFmtConfig {
        exclude: exclude_patterns,
        ..Default::default()
      },
      None => return Ok(None),
    };

    serialized
      .into_resolved(&self.specifier)
      .context("Invalid fmt config.")
      .map(Some)
  }

  pub fn to_lint_config(&self) -> Result<Option<LintConfig>, AnyError> {
    let mut exclude_patterns = self.resolve_exclude_patterns()?;
    let serialized = match self.json.lint.clone() {
      Some(config) => {
        let mut serialized: SerializedLintConfig =
          serde_json::from_value(config)
            .context("Failed to parse \"lint\" configuration")?;
        // top level excludes at the start because they're lower priority
        exclude_patterns.extend(std::mem::take(&mut serialized.exclude));
        serialized.exclude = exclude_patterns;
        serialized
      }
      None if !exclude_patterns.is_empty() => SerializedLintConfig {
        exclude: exclude_patterns,
        ..Default::default()
      },
      None => return Ok(None),
    };

    serialized
      .into_resolved(&self.specifier)
      .context("Invalid lint config.")
      .map(Some)
  }

  pub fn to_test_config(&self) -> Result<Option<TestConfig>, AnyError> {
    let mut exclude_patterns = self.resolve_exclude_patterns()?;
    let serialized = match self.json.test.clone() {
      Some(config) => {
        let mut serialized: SerializedTestConfig =
          serde_json::from_value(config)
            .context("Failed to parse \"test\" configuration")?;
        // top level excludes at the start because they're lower priority
        exclude_patterns.extend(std::mem::take(&mut serialized.exclude));
        serialized.exclude = exclude_patterns;
        serialized
      }
      None if !exclude_patterns.is_empty() => SerializedTestConfig {
        exclude: exclude_patterns,
        ..Default::default()
      },
      None => return Ok(None),
    };

    serialized
      .into_resolved(&self.specifier)
      .context("Invalid test config.")
      .map(Some)
  }

  pub(crate) fn to_publish_config(
    &self,
  ) -> Result<Option<PublishConfig>, AnyError> {
    let mut exclude_patterns = self.resolve_exclude_patterns()?;
    let serialized = match self.json.publish.clone() {
      Some(config) => {
        let mut serialized: SerializedPublishConfig =
          serde_json::from_value(config)
            .context("Failed to parse \"test\" configuration")?;
        // top level excludes at the start because they're lower priority
        exclude_patterns.extend(std::mem::take(&mut serialized.exclude));
        serialized.exclude = exclude_patterns;
        serialized
      }
      None if !exclude_patterns.is_empty() => SerializedPublishConfig {
        exclude: exclude_patterns,
        ..Default::default()
      },
      None => return Ok(None),
    };

    serialized
      .into_resolved(&self.specifier)
      .context("Invalid publish config.")
      .map(Some)
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
  ) -> Result<Option<IndexMap<String, Task>>, AnyError> {
    if let Some(config) = self.json.tasks.clone() {
      let tasks_config: IndexMap<String, Task> = serde_json::from_value(config)
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
        if compiler_options.jsx_import_source_types.is_some() {
          bail!(
            "'jsxImportSourceTypes' is only supported when 'jsx' is set to 'react-jsx' or 'react-jsxdev'.\n  at {}",
            self.specifier,
          )
        }
        return Ok(None);
      }
      Some("precompile") => "jsx-runtime".to_string(),
      Some(setting) => bail!(
        "Unsupported 'jsx' compiler option value '{}'. Supported: 'react-jsx', 'react-jsxdev', 'react', 'precompile'\n  at {}",
        setting,
        self.specifier,
      ),
    };
    Ok(Some(JsxImportSourceConfig {
      default_specifier: compiler_options.jsx_import_source,
      default_types_specifier: compiler_options.jsx_import_source_types,
      module,
      base_url: self.specifier.clone(),
    }))
  }

  pub fn resolve_tasks_config(
    &self,
  ) -> Result<IndexMap<String, Task>, AnyError> {
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
      let mut lock_config: LockConfig = serde_json::from_value(config)
        .context("Failed to parse \"lock\" configuration")?;
      if let LockConfig::PathBuf(path) = &mut lock_config {
        *path = specifier_to_file_path(&self.specifier)?
          .parent()
          .unwrap()
          .join(&path);
      }
      Ok(Some(lock_config))
    } else {
      Ok(None)
    }
  }

  pub fn resolve_lockfile_path(&self) -> Result<Option<PathBuf>, AnyError> {
    match self.to_lock_config()? {
      Some(LockConfig::Bool(lock)) if !lock => Ok(None),
      Some(LockConfig::PathBuf(lock)) => Ok(Some(lock)),
      _ => {
        let mut path = specifier_to_file_path(&self.specifier)?;
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
      Self::DenoWindow => {
        vec!["deno.window".to_string(), "deno.unstable".to_string()]
      }
      Self::DenoWorker => {
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
      "experimentalDecorators": true,
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
      "experimentalDecorators": false,
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
      "experimentalDecorators": false,
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
  use crate::fs::RealDenoConfigFs;
  use crate::glob::PathOrPattern;
  use crate::util::specifier_to_file_path;

  use super::*;
  use pretty_assertions::assert_eq;
  use std::path::PathBuf;

  impl Task {
    fn new(s: impl AsRef<str>) -> Self {
      Self::Definition(s.as_ref().to_string())
    }
  }

  #[macro_export]
  macro_rules! assert_contains {
    ($string:expr, $($test:expr),+ $(,)?) => {
      let string = &$string; // This might be a function call or something
      if !($(string.contains($test))||+) {
        panic!("{:?} does not contain any of {:?}", string, [$($test),+]);
      }
    }
  }

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
    let config_file = ConfigFile::read(
      &RealDenoConfigFs,
      path.as_path(),
      &ConfigParseOptions::default(),
    )
    .unwrap();
    assert!(config_file.json.compiler_options.is_some());
  }

  #[test]
  fn include_config_path_on_error() {
    let path = testdata_path().join("404.json");
    let error = ConfigFile::read(
      &RealDenoConfigFs,
      path.as_path(),
      &ConfigParseOptions::default(),
    )
    .err()
    .unwrap();
    assert!(error.to_string().contains("404.json"));
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
      },
      "unstable": ["kv", "ffi"]
    }"#;
    let config_dir = Url::parse("file:///deno/").unwrap();
    let config_specifier = config_dir.join("tsconfig.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier.clone(),
      &ConfigParseOptions::default(),
    )
    .unwrap();
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

    let config_dir_path = specifier_to_file_path(&config_dir).unwrap();
    assert_eq!(
      unpack_object(config_file.to_lint_config(), "lint"),
      LintConfig {
        files: FilePatterns {
          base: config_dir_path.clone(),
          include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
            PathBuf::from("/deno/src/")
          )])),
          exclude: PathOrPatternSet::new(vec![PathOrPattern::Path(
            PathBuf::from("/deno/src/testdata/")
          )]),
        },
        rules: LintRulesConfig {
          include: Some(vec!["ban-untagged-todo".to_string()]),
          exclude: None,
          tags: Some(vec!["recommended".to_string()]),
        },
      }
    );
    assert_eq!(
      unpack_object(config_file.to_fmt_config(), "fmt"),
      FmtConfig {
        files: FilePatterns {
          base: config_dir_path.clone(),
          include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
            PathBuf::from("/deno/src/")
          )])),
          exclude: PathOrPatternSet::new(vec![PathOrPattern::Path(
            PathBuf::from("/deno/src/testdata/")
          )]),
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
      Task::new("deno run --allow-read --allow-write build.ts"),
    );
    assert_eq!(
      tasks_config["server"],
      Task::new("deno run --allow-net --allow-read server.ts"),
    );

    assert_eq!(
      config_file.json.unstable,
      vec!["kv".to_string(), "ffi".to_string()],
    )
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
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();
    let config_dir_path = specifier_to_file_path(&config_dir).unwrap();

    let lint_files = unpack_object(config_file.to_lint_config(), "lint").files;
    assert_eq!(
      lint_files,
      FilePatterns {
        base: config_dir_path.clone(),
        include: Some(
          PathOrPatternSet::from_absolute_paths(&["/deno/src/".to_string()])
            .unwrap()
        ),
        exclude: Default::default(),
      }
    );

    let fmt_files = unpack_object(config_file.to_fmt_config(), "fmt").files;
    assert_eq!(
      fmt_files,
      FilePatterns {
        base: config_dir_path.clone(),
        // meh, this is fine that it combines them when there's only an exclude
        include: Some(
          PathOrPatternSet::from_absolute_paths(&["/deno/foo/".to_string(),])
            .unwrap()
        ),
        exclude: PathOrPatternSet::from_absolute_paths(&[
          "/deno/dist/".to_string(),
          // meh, this is fine
          "/deno/bar/".to_string(),
        ])
        .unwrap(),
      }
    );

    let test_include = unpack_object(config_file.to_test_config(), "test")
      .files
      .include;
    assert_eq!(
      test_include,
      Some(
        PathOrPatternSet::from_absolute_paths(&["/deno/src/".to_string()])
          .unwrap()
      )
    );

    let bench_include = unpack_object(config_file.to_bench_config(), "bench")
      .files
      .include;
    assert_eq!(
      bench_include,
      Some(
        PathOrPatternSet::from_absolute_paths(&["/deno/src/".to_string()])
          .unwrap()
      )
    );
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
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();

    let lint_include = unpack_object(config_file.to_lint_config(), "lint")
      .files
      .include;
    assert_eq!(
      lint_include,
      Some(
        PathOrPatternSet::from_absolute_paths(&["/deno/src/".to_string()])
          .unwrap()
      )
    );

    let fmt_include = unpack_object(config_file.to_fmt_config(), "fmt")
      .files
      .include;
    assert_eq!(
      fmt_include,
      Some(
        PathOrPatternSet::from_absolute_paths(&["/deno/src/".to_string()])
          .unwrap()
      )
    );

    let test_exclude = unpack_object(config_file.to_test_config(), "test")
      .files
      .exclude;
    assert_eq!(
      test_exclude,
      PathOrPatternSet::from_absolute_paths(&["/deno/dist/".to_string()])
        .unwrap()
    );

    let bench_exclude = unpack_object(config_file.to_bench_config(), "bench")
      .files
      .exclude;
    assert_eq!(
      bench_exclude,
      PathOrPatternSet::from_absolute_paths(&["/deno/dist/".to_string()])
        .unwrap()
    );
  }

  #[test]
  fn test_parse_config_exclude_lower_priority_path() {
    let config_text = r#"{
      "fmt": {
        "exclude": ["!dist/data", "dist/"]
      }
    }"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();

    let err = config_file.to_fmt_config().err().unwrap();
    assert_eq!(
      format!("{:?}", err),
      r#"Invalid fmt config.

Caused by:
    0: Invalid exclude.
    1: The negation of '!dist/data' is never reached due to the higher priority 'dist/' exclude. Move '!dist/data' after 'dist/'."#
    );
  }

  #[test]
  fn test_parse_config_exclude_lower_priority_glob() {
    let config_text = r#"{
      "lint": {
        "exclude": ["!dist/data/**/*.ts", "dist/"]
      }
    }"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();

    let err = config_file.to_lint_config().err().unwrap();
    assert_eq!(
      format!("{:?}", err),
      r#"Invalid lint config.

Caused by:
    0: Invalid exclude.
    1: The negation of '!dist/data/**/*.ts' is never reached due to the higher priority 'dist/' exclude. Move '!dist/data/**/*.ts' after 'dist/'."#
    );
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
    let config_file_both = ConfigFile::new(
      config_text_both,
      config_specifier.clone(),
      &ConfigParseOptions::default(),
    )
    .unwrap();
    let config_file_deprecated = ConfigFile::new(
      config_text_deprecated,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();

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
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();
    let (options_value, _) = config_file.to_compiler_options().unwrap();
    assert!(options_value.is_object());
  }

  #[test]
  fn test_parse_config_with_commented_file() {
    let config_text = r#"//{"foo":"bar"}"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();
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
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();

    let (options_value, _) = config_file.to_compiler_options().unwrap();
    assert!(options_value.is_object());

    let test_config = config_file.to_test_config().unwrap().unwrap();
    assert_eq!(test_config.files.include, None);
    assert_eq!(
      test_config.files.exclude,
      PathOrPatternSet::from_absolute_paths(&[
        "/deno/foo/".to_string(),
        "/deno/npm/".to_string(),
      ])
      .unwrap()
    );

    let bench_config = config_file.to_bench_config().unwrap().unwrap();
    assert_eq!(
      bench_config.files.exclude,
      PathOrPatternSet::from_absolute_paths(&["/deno/foo/".to_string()])
        .unwrap()
    );
  }

  #[test]
  fn test_parse_config_publish() {
    let config_text = r#"{
      "exclude": ["foo/"],
      "publish": {
        "exclude": ["npm/"],
      }
    }"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();

    let (options_value, _) = config_file.to_compiler_options().unwrap();
    assert!(options_value.is_object());

    let publish_config = config_file.to_publish_config().unwrap().unwrap();
    assert_eq!(publish_config.files.include, None);
    assert_eq!(
      publish_config.files.exclude,
      PathOrPatternSet::from_absolute_paths(&[
        "/deno/foo/".to_string(),
        "/deno/npm/".to_string(),
      ])
      .unwrap()
    );
  }

  #[test]
  fn test_parse_config_with_global_files_only() {
    let config_text = r#"{
      "exclude": ["npm/"]
    }"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();

    let (options_value, _) = config_file.to_compiler_options().unwrap();
    assert!(options_value.is_object());

    let files_config = config_file.to_files_config().unwrap();
    assert_eq!(files_config.include, None);
    assert_eq!(
      files_config.exclude,
      PathOrPatternSet::from_absolute_paths(&["/deno/npm/".to_string()])
        .unwrap()
    );

    let lint_config = config_file.to_lint_config().unwrap().unwrap();
    assert_eq!(lint_config.files.include, None);
    assert_eq!(
      lint_config.files.exclude,
      PathOrPatternSet::from_absolute_paths(&["/deno/npm/".to_string()])
        .unwrap()
    );

    let fmt_config = config_file.to_fmt_config().unwrap().unwrap();
    assert_eq!(fmt_config.files.include, None);
    assert_eq!(
      fmt_config.files.exclude,
      PathOrPatternSet::from_absolute_paths(&["/deno/npm/".to_string()])
        .unwrap()
    );
  }

  #[test]
  fn test_parse_config_with_invalid_file() {
    let config_text = "{foo:bar}";
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    // Emit error: Unable to parse config file JSON "<config_path>" because of Unexpected token on line 1 column 6.
    assert!(ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default()
    )
    .is_err());
  }

  #[test]
  fn test_parse_config_with_not_object_file() {
    let config_text = "[]";
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    // Emit error: config file JSON "<config_path>" should be an object
    assert!(ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default()
    )
    .is_err());
  }

  #[test]
  fn test_jsx_invalid_setting() {
    let config_text = r#"{ "compilerOptions": { "jsx": "preserve" } }"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    let config = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();
    assert_eq!(
      config.to_maybe_jsx_import_source_config().err().unwrap().to_string(),
      concat!(
        "Unsupported 'jsx' compiler option value 'preserve'. Supported: 'react-jsx', 'react-jsxdev', 'react', 'precompile'\n",
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
      let config = ConfigFile::new(
        config_text,
        config_specifier.clone(),
        &ConfigParseOptions::default(),
      )
      .unwrap();
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
      let config = ConfigFile::new(
        config_text,
        config_specifier,
        &ConfigParseOptions::default(),
      )
      .unwrap();
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
  fn test_jsx_import_source_types_only() {
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    {
      let config_text =
        r#"{ "compilerOptions": { "jsxImportSourceTypes": "test" } }"#;
      let config = ConfigFile::new(
        config_text,
        config_specifier.clone(),
        &ConfigParseOptions::default(),
      )
      .unwrap();
      assert_eq!(
        config.to_maybe_jsx_import_source_config().err().unwrap().to_string(),
        concat!(
          "'jsxImportSourceTypes' is only supported when 'jsx' is set to 'react-jsx' or 'react-jsxdev'.\n",
          "  at file:///deno/tsconfig.json",
        ),
      );
    }
    {
      let config_text = r#"{ "compilerOptions": { "jsx": "react", "jsxImportSourceTypes": "test" } }"#;
      let config = ConfigFile::new(
        config_text,
        config_specifier,
        &ConfigParseOptions::default(),
      )
      .unwrap();
      assert_eq!(
        config.to_maybe_jsx_import_source_config().err().unwrap().to_string(),
        concat!(
          "'jsxImportSourceTypes' is only supported when 'jsx' is set to 'react-jsx' or 'react-jsxdev'.\n",
          "  at file:///deno/tsconfig.json",
        ),
      );
    }
  }

  #[test]
  fn test_jsx_import_source_valid() {
    let config_text = r#"{ "compilerOptions": { "jsx": "react" } }"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    assert!(ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default()
    )
    .is_ok());
  }

  #[test]
  fn test_jsx_precompile_skip_setting() {
    let config_text = r#"{ "compilerOptions": { "jsx": "precompile", "jsxPrecompileSkipElements": ["a", "p"] } }"#;
    let config_specifier = Url::parse("file:///deno/tsconfig.json").unwrap();
    assert!(ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default()
    )
    .is_ok());
  }

  #[test]
  fn discover_from_success() {
    // testdata/fmt/deno.jsonc exists
    let testdata = testdata_path();
    let c_md = testdata.join("fmt/with_config/subdir/c.md");
    let config_file = ConfigFile::discover_from(
      &RealDenoConfigFs,
      &c_md,
      &[],
      &ConfigParseOptions::default(),
    )
    .unwrap()
    .unwrap();
    let fmt_config = config_file.to_fmt_config().unwrap().unwrap();
    let expected_exclude =
      Url::from_file_path(testdata.join("fmt/with_config/subdir/b.ts"))
        .unwrap()
        .to_file_path()
        .unwrap();
    assert_eq!(
      fmt_config.files.exclude,
      PathOrPatternSet::new(vec![PathOrPattern::Path(expected_exclude)])
    );
  }

  #[test]
  fn discover_from_additional_config_file_names_success() {
    let testdata = testdata_path();
    let dir = testdata.join("additional_files/");
    let config_file = ConfigFile::discover_from(
      &RealDenoConfigFs,
      &dir,
      &["jsr.json"],
      &ConfigParseOptions::default(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(config_file.json.name.unwrap(), "@foo/bar");
  }

  #[test]
  fn discover_from_malformed() {
    let testdata = testdata_path();
    let d = testdata.join("malformed_config/");
    let err = ConfigFile::discover_from(
      &RealDenoConfigFs,
      d.as_path(),
      &[],
      &ConfigParseOptions::default(),
    )
    .unwrap_err();
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

  #[track_caller]
  fn run_task_error_test(config_text: &str, expected_error: &str) {
    let config_dir = Url::parse("file:///deno/").unwrap();
    let config_specifier = config_dir.join("tsconfig.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();
    assert_eq!(
      config_file.resolve_tasks_config().unwrap_err().to_string(),
      expected_error,
    );
  }

  #[test]
  fn files_pattern_matches_remote() {
    assert!(FilePatterns::new_with_base(PathBuf::from("/"))
      .matches_specifier(&Url::parse("https://example.com/mod.ts").unwrap()));
  }

  #[test]
  fn resolve_lockfile_path_from_unix_path() {
    let config_file = ConfigFile::new(
      "{}",
      Url::parse("file:///root/deno.json").unwrap(),
      &ConfigParseOptions::default(),
    )
    .unwrap();
    let lockfile_path = config_file.resolve_lockfile_path().unwrap();
    let lockfile_path = lockfile_path.unwrap();
    assert_eq!(lockfile_path, PathBuf::from("/root/deno.lock"));
  }

  #[test]
  fn exports() {
    fn get_exports(config_text: &str) -> ExportsConfig {
      let config_dir = Url::parse("file:///deno/").unwrap();
      let config_specifier = config_dir.join("tsconfig.json").unwrap();
      let config_file = ConfigFile::new(
        config_text,
        config_specifier,
        &ConfigParseOptions::default(),
      )
      .unwrap();
      config_file.to_exports_config().unwrap()
    }

    // no exports
    assert_eq!(
      get_exports("{}").into_map(),
      IndexMap::<String, String>::new()
    );
    // string export
    assert_eq!(
      get_exports(r#"{ "exports": "./mod.ts" }"#).into_map(),
      IndexMap::from([(".".to_string(), "./mod.ts".to_string())])
    );
    // map export
    assert_eq!(
      get_exports(r#"{ "exports": { "./export": "./mod.ts" } }"#).into_map(),
      IndexMap::from([("./export".to_string(), "./mod.ts".to_string())])
    );
    // resolve an export
    let exports = get_exports(r#"{ "exports": { "./export": "./mod.ts" } }"#);
    assert_eq!(
      exports
        .get_resolved("./export")
        .unwrap()
        .unwrap()
        .to_string(),
      "file:///deno/mod.ts"
    );
    assert!(exports.get_resolved("./non-existent").unwrap().is_none());
  }

  #[test]
  fn exports_errors() {
    #[track_caller]
    fn run_test(config_text: &str, expected_error: &str) {
      let config_dir = Url::parse("file:///deno/").unwrap();
      let config_specifier = config_dir.join("tsconfig.json").unwrap();
      let config_file = ConfigFile::new(
        config_text,
        config_specifier,
        &ConfigParseOptions::default(),
      )
      .unwrap();
      assert_eq!(
        config_file.to_exports_config().unwrap_err().to_string(),
        expected_error,
      );
    }

    // empty key
    run_test(
      r#"{ "exports": { "": "./mod.ts" } }"#,
      "The '' export must not be empty. Use '.' if you meant the root export.",
    );
    // no ./ at start of key
    run_test(
      r#"{ "exports": { "mod": "./mod.ts" } }"#,
      "The 'mod' export must start with './'. Did you mean './mod'?",
    );
    // trailing slash in key
    run_test(
      r#"{ "exports": { "./mod/": "./mod.ts" } }"#,
      "The './mod/' export must not end with '/'. Did you mean './mod'?",
    );
    // multiple trailing slash in key
    run_test(
      r#"{ "exports": { "./mod//": "./mod.ts" } }"#,
      "The './mod//' export must not end with '/'. Did you mean './mod'?",
    );
    // unsupported characters in key
    run_test(
      r#"{ "exports": { "./mod*": "./mod.ts" } }"#,
      "The './mod*' export must only contain alphanumeric characters, underscores (_), dashes (-), dots (.), and slashes (/).",
    );
    // double slash in key
    run_test(
      r#"{ "exports": { "./mod//bar": "./mod.ts" } }"#,
      "The './mod//bar' export must not contain double slashes (//), or parts consisting entirely of dots (.).",
    );
    // . part in key
    run_test(
      r#"{ "exports": { "././mod": "./mod.ts" } }"#,
      "The '././mod' export must not contain double slashes (//), or parts consisting entirely of dots (.).",
    );
    // .. part in key
    run_test(
      r#"{ "exports": { "./../mod": "./mod.ts" } }"#,
      "The './../mod' export must not contain double slashes (//), or parts consisting entirely of dots (.).",
    );
    // ...... part in key
    run_test(
      r#"{ "exports": { "./....../mod": "./mod.ts" } }"#,
      "The './....../mod' export must not contain double slashes (//), or parts consisting entirely of dots (.).",
    );

    // empty value
    run_test(
      r#"{ "exports": { "./mod": "" } }"#,
      "The path for the './mod' export must not be empty.",
    );
    // value without ./ at start
    run_test(
      r#"{ "exports": { "./mod": "mod.ts" } }"#,
      "The path 'mod.ts' at the './mod' export could not be resolved as a relative path from the config file. Did you mean './mod.ts'?",
    );
    // value with a trailing slash
    run_test(
      r#"{ "exports": { "./mod": "./folder/" } }"#,
      "The path './folder/' at the './mod' export must not end with '/'. Did you mean './folder'?",
    );
    // value without an extension
    run_test(
      r#"{ "exports": { "./mod": "./folder" } }"#,
      "The path './folder' at the './mod' export is missing a file extension. Add a file extension such as '.js' or '.ts'.",
    );
    // boolean key value
    run_test(
      r#"{ "exports": { "./mod": true } }"#,
      "The path of the './mod' export must be a string, found invalid value 'true'.",
    );
    // object key value
    run_test(
      r#"{ "exports": { "./mod": {} } }"#,
      "The path of the './mod' export must be a string, found invalid value '{}'. Exports in deno.json do not support conditional exports.",
    );
    // non-map or string value
    run_test(
      r#"{ "exports": [] }"#,
      "The 'exports' key must be a string or object, found invalid value '[]'.",
    );
    // null
    run_test(
      r#"{ "exports": { "./mod": null }  }"#,
      "The path of the './mod' export must be a string, found invalid value 'null'.",
    );
  }

  #[test]
  fn resolve_export_value_urls() {
    fn get_exports(config_text: &str) -> Vec<String> {
      let config_dir = Url::parse("file:///deno/").unwrap();
      let config_specifier = config_dir.join("tsconfig.json").unwrap();
      let config_file = ConfigFile::new(
        config_text,
        config_specifier,
        &ConfigParseOptions::default(),
      )
      .unwrap();
      config_file
        .resolve_export_value_urls()
        .unwrap()
        .into_iter()
        .map(|u| u.to_string())
        .collect()
    }

    // no exports
    assert_eq!(get_exports("{}"), Vec::<String>::new());
    // string export
    assert_eq!(
      get_exports(r#"{ "exports": "./mod.ts" }"#),
      vec!["file:///deno/mod.ts".to_string()]
    );
    // map export
    assert_eq!(
      get_exports(r#"{ "exports": { "./export": "./mod.ts" } }"#),
      vec!["file:///deno/mod.ts".to_string()]
    );
    // multiple
    assert_eq!(
      get_exports(
        r#"{ "exports": { "./export": "./mod.ts", "./other": "./other.ts" } }"#
      ),
      vec![
        "file:///deno/mod.ts".to_string(),
        "file:///deno/other.ts".to_string(),
      ]
    );
  }

  #[test]
  fn test_is_package() {
    fn get_for_config(config_text: &str) -> bool {
      let config_specifier = root_url().join("tsconfig.json").unwrap();
      let config_file = ConfigFile::new(
        config_text,
        config_specifier,
        &ConfigParseOptions::default(),
      )
      .unwrap();
      config_file.is_package()
    }

    assert!(!get_for_config("{}"));
    assert!(!get_for_config(
      r#"{
        "name": "test"
      }"#
    ));
    assert!(!get_for_config(
      r#"{
        "name": "test",
        "version": "1.0.0"
      }"#
    ));
    assert!(get_for_config(
      r#"{
        "name": "test",
        "exports": "./mod.ts"
      }"#
    ));
    assert!(!get_for_config(
      r#"{
        "version": "1.0.0",
        "exports": "./mod.ts"
      }"#
    ));
    assert!(get_for_config(
      r#"{
        "name": "test",
        "version": "1.0.0",
        "exports": "./mod.ts"
      }"#
    ));
  }

  #[test]
  fn test_to_import_map_from_imports() {
    let config_text = r#"{
      "imports": {
        "@std/test": "jsr:@std/test@0.2.0"
      }
    }"#;
    let config_specifier = root_url().join("deno.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();
    let result = config_file.to_import_map_from_imports().unwrap();

    assert_eq!(
      json!(result.import_map.imports()),
      // imports should be expanded
      json!({
        "@std/test/": "jsr:/@std/test@0.2.0/",
        "@std/test": "jsr:@std/test@0.2.0",
      })
    );
  }

  #[tokio::test]
  async fn test_to_import_map_imports_entry() {
    let config_text = r#"{
      "imports": { "@std/test": "jsr:@std/test@0.2.0" },
      // will be ignored because imports and scopes takes precedence
      "importMap": "import_map.json",
    }"#;
    let config_specifier = root_url().join("deno.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();
    let result = config_file
      .to_import_map(|_url| async { unreachable!() })
      .await
      .unwrap()
      .unwrap();

    assert_eq!(
      result.import_map.base_url(),
      &root_url().join("deno.json").unwrap()
    );
    assert_eq!(
      json!(result.import_map.imports()),
      // imports should be expanded
      json!({
        "@std/test/": "jsr:/@std/test@0.2.0/",
        "@std/test": "jsr:@std/test@0.2.0",
      })
    );
  }

  #[tokio::test]
  async fn test_to_import_map_scopes_entry() {
    let config_text = r#"{
      "scopes": { "https://deno.land/x/test/mod.ts": { "@std/test": "jsr:@std/test@0.2.0" } },
      // will be ignored because imports and scopes takes precedence
      "importMap": "import_map.json",
    }"#;
    let config_specifier = root_url().join("deno.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();
    let result = config_file
      .to_import_map(|_url| async { unreachable!() })
      .await
      .unwrap()
      .unwrap();

    assert_eq!(
      result.import_map.base_url(),
      &root_url().join("deno.json").unwrap()
    );
    assert_eq!(
      json!(result.import_map),
      // imports should be expanded
      json!({
        "imports": {},
        "scopes": {
          "https://deno.land/x/test/mod.ts": {
            "@std/test/": "jsr:/@std/test@0.2.0/",
            "@std/test": "jsr:@std/test@0.2.0",
          }
        }
      })
    );
  }

  #[tokio::test]
  async fn test_to_import_map_import_map_entry() {
    let config_text = r#"{
      "importMap": "import_map.json",
    }"#;
    let config_specifier = root_url().join("deno.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();
    let result = config_file
      .to_import_map(|url| {
        assert_eq!(url, &root_url().join("import_map.json").unwrap());
        async {
          Ok(
            r#"{ "imports": { "@std/test": "jsr:@std/test@0.2.0" } }"#
              .to_string(),
          )
        }
      })
      .await
      .unwrap()
      .unwrap();

    assert_eq!(
      result.import_map.base_url(),
      &root_url().join("import_map.json").unwrap()
    );
    assert_eq!(
      json!(result.import_map.imports()),
      // imports should NOT be expanded
      json!({
        "@std/test": "jsr:@std/test@0.2.0",
      })
    );
  }

  #[tokio::test]
  async fn test_to_import_map_import_map_remote() {
    let config_text = r#"{
      "importMap": "https://deno.land/import_map.json",
    }"#;
    let config_specifier = root_url().join("deno.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();
    let result = config_file
      .to_import_map(|url| {
        assert_eq!(url.as_str(), "https://deno.land/import_map.json");
        async {
          Ok(
            r#"{ "imports": { "@std/test": "jsr:@std/test@0.2.0" } }"#
              .to_string(),
          )
        }
      })
      .await
      .unwrap()
      .unwrap();

    assert_eq!(
      result.import_map.base_url().as_str(),
      "https://deno.land/import_map.json"
    );
    assert_eq!(
      json!(result.import_map.imports()),
      // imports should NOT be expanded
      json!({
        "@std/test": "jsr:@std/test@0.2.0",
      })
    );
  }

  #[tokio::test]
  async fn test_to_import_map_import_map_remote_relative() {
    let config_text = r#"{
      "importMap": "./import_map.json",
    }"#;
    let config_specifier =
      Url::parse("https://deno.land/import_map.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();
    let result = config_file
      .to_import_map(|url| {
        assert_eq!(url.as_str(), "https://deno.land/import_map.json");
        async {
          Ok(
            r#"{ "imports": { "@std/test": "jsr:@std/test@0.2.0" } }"#
              .to_string(),
          )
        }
      })
      .await
      .unwrap()
      .unwrap();

    assert_eq!(
      result.import_map.base_url().as_str(),
      "https://deno.land/import_map.json"
    );
    assert_eq!(
      json!(result.import_map.imports()),
      // imports should NOT be expanded
      json!({
        "@std/test": "jsr:@std/test@0.2.0",
      })
    );
  }

  fn root_url() -> Url {
    if cfg!(windows) {
      Url::parse("file://C:/deno/").unwrap()
    } else {
      Url::parse("file:///deno/").unwrap()
    }
  }

  #[test]
  fn task_comments() {
    let config_text = r#"{
      "tasks": {
        // dev task
        "dev": "deno run -A --watch mod.ts",
        // run task
        // with multiple line comments
        "run": "deno run -A mod.ts", // comments not supported here
        /*
         * test task
         *
         * with multi-line comments
         */
        "test": "deno test",
        /* we should */ /* ignore these */ "fmt": "deno fmt",
        "lint": "deno lint"
        // trailing comments
      },
    }"#;

    let config = ConfigFile::new(
      config_text,
      root_url().join("deno.jsonc").unwrap(),
      &ConfigParseOptions {
        include_task_comments: true,
      },
    )
    .unwrap();
    assert_eq!(
      config.resolve_tasks_config().unwrap(),
      IndexMap::from([
        (
          "dev".into(),
          Task::Commented {
            definition: "deno run -A --watch mod.ts".into(),
            comments: vec!["dev task".into()]
          }
        ),
        (
          "run".into(),
          Task::Commented {
            definition: "deno run -A mod.ts".into(),
            comments: vec![
              "run task".into(),
              "with multiple line comments".into()
            ]
          }
        ),
        (
          "test".into(),
          Task::Commented {
            definition: "deno test".into(),
            comments: vec![
              "test task".into(),
              "".into(),
              "with multi-line comments".into()
            ]
          }
        ),
        (
          "fmt".into(),
          Task::Commented {
            definition: "deno fmt".into(),
            comments: vec![]
          }
        ),
        (
          "lint".into(),
          Task::Commented {
            definition: "deno lint".into(),
            comments: vec![]
          }
        )
      ])
    );
  }

  #[test]
  fn resolve_import_map_specifier_parent() {
    let config_text = r#"{ "importMap": "../import_map.json" }"#;
    let config_specifier = Url::parse("file:///deno/sub/deno.json").unwrap();
    let config_file = ConfigFile::new(
      config_text,
      config_specifier,
      &ConfigParseOptions::default(),
    )
    .unwrap();
    assert_eq!(
      config_file
        .to_import_map_specifier()
        .unwrap()
        .unwrap()
        .as_str(),
      "file:///deno/import_map.json"
    );
  }
}
