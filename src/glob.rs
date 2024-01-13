// Copyright 2018-2024 the Deno authors. All rights reserved. MIT license.

use std::path::Component;
use std::path::Path;
use std::path::PathBuf;

use anyhow::Context;
use indexmap::IndexMap;
use url::Url;

#[derive(Clone, Default, Debug, Eq, PartialEq)]
pub struct FilePatterns {
  pub include: Option<PathOrPatternSet>,
  pub exclude: PathOrPatternSet,
}

impl FilePatterns {
  pub fn matches_specifier(&self, specifier: &Url) -> bool {
    if specifier.scheme() != "file" {
      return true;
    }
    let path = match specifier.to_file_path() {
      Ok(path) => path,
      Err(_) => return true,
    };
    self.matches_path(&path)
  }

  pub fn matches_path(&self, path: &Path) -> bool {
    // Skip files in the exclude list.
    if self.exclude.matches_path(path) {
      return false;
    }

    // Ignore files not in the include list if it's present.
    self
      .include
      .as_ref()
      .map(|m| m.matches_path(path))
      .unwrap_or(true)
  }

  /// Creates a collection of `FilePatterns` by base where the containing patterns
  /// are only the ones applicable to the base.
  ///
  /// The order these are returned in is the order that the directory traversal
  /// should occur in.
  pub fn split_by_base(&self) -> Vec<(PathBuf, Self)> {
    let Some(include) = &self.include else {
      return Vec::new();
    };

    let mut include_paths = Vec::new();
    let mut include_patterns = Vec::new();
    for path_or_pattern in &include.0 {
      match path_or_pattern {
        PathOrPattern::Path(path) => include_paths.push((path.is_file(), path)),
        PathOrPattern::Pattern(pattern) => include_patterns.push(pattern),
        PathOrPattern::RemoteUrl(_) => {}
      }
    }
    let include_patterns_by_base_path = include_patterns.into_iter().fold(
      IndexMap::new(),
      |mut map: IndexMap<_, Vec<_>>, p| {
        map.entry(p.base_path()).or_default().push(p);
        map
      },
    );
    let exclude_by_base_path = self
      .exclude
      .0
      .iter()
      .filter_map(|s| Some((s.base_path()?, s)))
      .collect::<Vec<_>>();
    let get_applicable_excludes =
      |is_file_path: bool, base_path: &PathBuf| -> Vec<PathOrPattern> {
        exclude_by_base_path
          .iter()
          .filter_map(|(exclude_base_path, exclude)| {
            match exclude {
              PathOrPattern::RemoteUrl(_) => None,
              PathOrPattern::Path(exclude_path) => {
                // For explicitly specified files, ignore when the exclude path starts
                // with it. Regardless, include excludes that are on a sub path of the dir.
                if is_file_path && base_path.starts_with(exclude_path)
                  || exclude_path.starts_with(base_path)
                {
                  Some((*exclude).clone())
                } else {
                  None
                }
              }
              PathOrPattern::Pattern(_) => {
                // include globs that's are sub paths or a parent path
                if exclude_base_path.starts_with(base_path)
                  || base_path.starts_with(exclude_base_path)
                {
                  Some((*exclude).clone())
                } else {
                  None
                }
              }
            }
          })
          .collect::<Vec<_>>()
      };

    let mut result = Vec::with_capacity(
      include_paths.len() + include_patterns_by_base_path.len(),
    );
    for (is_file, path) in include_paths {
      let applicable_excludes = get_applicable_excludes(is_file, path);
      result.push((
        path.clone(),
        Self {
          include: Some(PathOrPatternSet::new(vec![PathOrPattern::Path(
            path.clone(),
          )])),
          exclude: PathOrPatternSet::new(applicable_excludes),
        },
      ));
    }

    // todo(dsherret): This could be further optimized by not including
    // patterns that will only ever match another base.
    for base_path in include_patterns_by_base_path.keys() {
      let applicable_excludes = get_applicable_excludes(false, base_path);
      let mut applicable_includes = Vec::new();
      // get all patterns that apply to the current or ancestor directories
      for path in base_path.ancestors() {
        if let Some(patterns) = include_patterns_by_base_path.get(path) {
          applicable_includes.extend(
            patterns
              .iter()
              .map(|p| PathOrPattern::Pattern((*p).clone())),
          );
        }
      }
      result.push((
        base_path.clone(),
        Self {
          include: Some(PathOrPatternSet::new(applicable_includes)),
          exclude: PathOrPatternSet::new(applicable_excludes),
        },
      ));
    }

    // Sort by the longest base path first. This ensures that we visit opted into
    // nested directories first before visiting the parent directory. The directory
    // traverser will handle not going into directories it's already been in.
    result.sort_by(|a, b| b.0.as_os_str().len().cmp(&a.0.as_os_str().len()));

    result
  }

  pub(crate) fn extend(self, rhs: Self) -> Self {
    Self {
      include: match (self.include, rhs.include) {
        (None, None) => None,
        (Some(lhs), None) => Some(lhs),
        (None, Some(rhs)) => Some(rhs),
        (Some(lhs), Some(rhs)) => Some(PathOrPatternSet(
          lhs.0.into_iter().filter(|p| rhs.0.contains(p)).collect(),
        )),
      },
      exclude: PathOrPatternSet([self.exclude.0, rhs.exclude.0].concat()),
    }
  }
}

#[derive(Clone, Default, Debug, Eq, PartialEq)]
pub struct PathOrPatternSet(Vec<PathOrPattern>);

impl PathOrPatternSet {
  pub fn new(elements: Vec<PathOrPattern>) -> Self {
    Self(elements)
  }

  pub fn from_absolute_paths(paths: &[String]) -> Result<Self, anyhow::Error> {
    Ok(Self(
      paths
        .iter()
        .map(|p| PathOrPattern::new(p))
        .collect::<Result<Vec<_>, _>>()?,
    ))
  }

  pub fn from_relative_path_or_patterns(
    base: &Path,
    paths: &[String],
  ) -> Result<Self, anyhow::Error> {
    Ok(Self(
      paths
        .iter()
        .map(|p| PathOrPattern::from_relative(base, p))
        .collect::<Result<Vec<_>, _>>()?,
    ))
  }

  pub fn inner(&self) -> &Vec<PathOrPattern> {
    &self.0
  }

  pub fn into_path_or_patterns(self) -> Vec<PathOrPattern> {
    self.0
  }

  pub fn matches_path(&self, path: &Path) -> bool {
    self.0.iter().any(|p| p.matches_path(path))
  }

  pub fn base_paths(&self) -> Vec<PathBuf> {
    let mut result = Vec::with_capacity(self.0.len());
    for element in &self.0 {
      match element {
        PathOrPattern::Path(path) => {
          result.push(path.to_path_buf());
        }
        PathOrPattern::RemoteUrl(_) => {
          // ignore
        }
        PathOrPattern::Pattern(pattern) => {
          result.push(pattern.base_path());
        }
      }
    }
    result
  }
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum PathOrPattern {
  Path(PathBuf),
  RemoteUrl(Url),
  Pattern(GlobPattern),
}

impl PathOrPattern {
  pub fn new(path: &str) -> Result<Self, anyhow::Error> {
    if path.starts_with("http://")
      || path.starts_with("https://")
      || path.starts_with("file://")
    {
      let url = Url::parse(path)?;
      if url.scheme() == "file" {
        let path = url
          .to_file_path()
          .map_err(|_| anyhow::anyhow!("Invalid file URL: \"{}\"", path))?;
        return Ok(Self::Path(path));
      } else {
        return Ok(Self::RemoteUrl(url));
      }
    }

    GlobPattern::new_if_pattern(path).map(|maybe_pattern| {
      maybe_pattern
        .map(PathOrPattern::Pattern)
        .unwrap_or_else(|| PathOrPattern::Path(normalize_path(path)))
    })
  }

  pub fn from_relative(
    base: &Path,
    p: &str,
  ) -> Result<PathOrPattern, anyhow::Error> {
    if is_glob_pattern(p) {
      let p = p.strip_prefix("./").unwrap_or(p);
      let mut pattern = base.to_string_lossy().replace('\\', "/");
      if !pattern.ends_with('/') {
        pattern.push('/');
      }
      let p = p.strip_suffix('/').unwrap_or(p);
      pattern.push_str(p);
      PathOrPattern::new(&pattern)
    } else {
      Ok(PathOrPattern::Path(base.join(p)))
    }
  }

  pub fn matches_path(&self, path: &Path) -> bool {
    match self {
      PathOrPattern::Path(p) => path.starts_with(p),
      PathOrPattern::RemoteUrl(_) => false,
      PathOrPattern::Pattern(p) => p.matches_path(path),
    }
  }

  /// Returns the base path of the pattern if it's not a remote url pattern.
  pub fn base_path(&self) -> Option<PathBuf> {
    match self {
      PathOrPattern::Path(p) => Some(p.clone()),
      PathOrPattern::RemoteUrl(_) => None,
      PathOrPattern::Pattern(p) => Some(p.base_path()),
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GlobPattern(glob::Pattern);

impl GlobPattern {
  pub fn new_if_pattern(pattern: &str) -> Result<Option<Self>, anyhow::Error> {
    if !is_glob_pattern(pattern) {
      return Ok(None);
    }
    Self::new(pattern).map(Some)
  }

  pub fn new(pattern: &str) -> Result<Self, anyhow::Error> {
    let pattern = escape_brackets(pattern).replace('\\', "/");
    let pattern = glob::Pattern::new(&pattern)
      .with_context(|| format!("Failed to expand glob: \"{}\"", pattern))?;
    Ok(Self(pattern))
  }

  pub fn matches_path(&self, path: &Path) -> bool {
    self.0.matches_path_with(path, match_options())
  }

  pub fn base_path(&self) -> PathBuf {
    let base_path = self
      .0
      .as_str()
      .split('/')
      .take_while(|c| !has_glob_chars(c))
      .collect::<Vec<_>>()
      .join(std::path::MAIN_SEPARATOR_STR);
    PathBuf::from(base_path)
  }
}

pub fn is_glob_pattern(path: &str) -> bool {
  !path.starts_with("http://")
    && !path.starts_with("https://")
    && !path.starts_with("file://")
    && has_glob_chars(path)
}

fn has_glob_chars(pattern: &str) -> bool {
  // we don't support [ and ]
  pattern.chars().any(|c| matches!(c, '*' | '?'))
}

fn escape_brackets(pattern: &str) -> String {
  // Escape brackets - we currently don't support them, because with introduction
  // of glob expansion paths like "pages/[id].ts" would suddenly start giving
  // wrong results. We might want to revisit that in the future.
  pattern.replace('[', "[[]").replace(']', "[]]")
}

fn match_options() -> glob::MatchOptions {
  // Matches what `deno_task_shell` does
  glob::MatchOptions {
    // false because it should work the same way on case insensitive file systems
    case_sensitive: false,
    // true because it copies what sh does
    require_literal_separator: true,
    // true because it copies with sh does—these files are considered "hidden"
    require_literal_leading_dot: true,
  }
}

/// Normalize all intermediate components of the path (ie. remove "./" and "../" components).
/// Similar to `fs::canonicalize()` but doesn't resolve symlinks.
///
/// Taken from Cargo
/// <https://github.com/rust-lang/cargo/blob/af307a38c20a753ec60f0ad18be5abed3db3c9ac/src/cargo/util/paths.rs#L60-L85>
fn normalize_path<P: AsRef<Path>>(path: P) -> PathBuf {
  let mut components = path.as_ref().components().peekable();
  let mut ret =
    if let Some(c @ Component::Prefix(..)) = components.peek().cloned() {
      components.next();
      PathBuf::from(c.as_os_str())
    } else {
      PathBuf::new()
    };

  for component in components {
    match component {
      Component::Prefix(..) => unreachable!(),
      Component::RootDir => {
        ret.push(component.as_os_str());
      }
      Component::CurDir => {}
      Component::ParentDir => {
        ret.pop();
      }
      Component::Normal(c) => {
        ret.push(c);
      }
    }
  }
  ret
}

#[cfg(test)]
mod test {
  use pretty_assertions::assert_eq;
  use tempfile::TempDir;

  use super::*;

  // For easier comparisons in tests.
  #[derive(Debug, PartialEq, Eq)]
  struct ComparableFilePatterns {
    include: Option<Vec<String>>,
    exclude: Vec<String>,
  }

  impl ComparableFilePatterns {
    pub fn new(root: &Path, file_patterns: &FilePatterns) -> Self {
      fn path_or_pattern_to_string(
        root: &Path,
        p: &PathOrPattern,
      ) -> Option<String> {
        match p {
          PathOrPattern::RemoteUrl(_) => None,
          PathOrPattern::Path(p) => Some(
            p.strip_prefix(root)
              .unwrap()
              .to_string_lossy()
              .replace('\\', "/"),
          ),
          PathOrPattern::Pattern(p) => Some(
            p.0
              .as_str()
              .strip_prefix(&format!(
                "{}/",
                root.to_string_lossy().replace('\\', "/")
              ))
              .unwrap()
              .to_string(),
          ),
        }
      }

      Self {
        include: file_patterns.include.as_ref().map(|p| {
          p.0
            .iter()
            .filter_map(|p| path_or_pattern_to_string(root, p))
            .collect()
        }),
        exclude: file_patterns
          .exclude
          .0
          .iter()
          .filter_map(|p| path_or_pattern_to_string(root, p))
          .collect(),
      }
    }

    pub fn from_split(
      root: &Path,
      patterns_by_base: &[(PathBuf, FilePatterns)],
    ) -> Vec<(String, ComparableFilePatterns)> {
      patterns_by_base
        .iter()
        .map(|(base_path, file_patterns)| {
          (
            base_path
              .strip_prefix(root)
              .unwrap()
              .to_string_lossy()
              .replace('\\', "/"),
            ComparableFilePatterns::new(root, file_patterns),
          )
        })
        .collect()
    }
  }

  #[test]
  fn should_split_globs_by_base_dir() {
    let temp_dir = TempDir::new().unwrap();
    let patterns = FilePatterns {
      include: Some(PathOrPatternSet::new(vec![
        PathOrPattern::Pattern(
          GlobPattern::new(&format!(
            "{}/inner/**/*.ts",
            temp_dir.path().to_string_lossy().replace('\\', "/")
          ))
          .unwrap(),
        ),
        PathOrPattern::Pattern(
          GlobPattern::new(&format!(
            "{}/inner/sub/deeper/**/*.js",
            temp_dir.path().to_string_lossy().replace('\\', "/")
          ))
          .unwrap(),
        ),
        PathOrPattern::Pattern(
          GlobPattern::new(&format!(
            "{}/other/**/*.js",
            temp_dir.path().to_string_lossy().replace('\\', "/")
          ))
          .unwrap(),
        ),
        PathOrPattern::Path(temp_dir.path().join("sub/file.ts").to_path_buf()),
      ])),
      exclude: PathOrPatternSet::new(vec![
        PathOrPattern::Pattern(
          GlobPattern::new(&format!(
            "{}/inner/other/**/*.ts",
            temp_dir.path().to_string_lossy().replace('\\', "/")
          ))
          .unwrap(),
        ),
        PathOrPattern::Path(
          temp_dir
            .path()
            .join("inner/sub/deeper/file.js")
            .to_path_buf(),
        ),
      ]),
    };
    let split = ComparableFilePatterns::from_split(
      temp_dir.path(),
      &patterns.split_by_base(),
    );
    assert_eq!(
      split,
      vec![
        (
          "inner/sub/deeper".to_string(),
          ComparableFilePatterns {
            include: Some(vec![
              "inner/sub/deeper/**/*.js".to_string(),
              "inner/**/*.ts".to_string(),
            ]),
            exclude: vec!["inner/sub/deeper/file.js".to_string()],
          }
        ),
        (
          "sub/file.ts".to_string(),
          ComparableFilePatterns {
            include: Some(vec!["sub/file.ts".to_string()]),
            exclude: vec![],
          }
        ),
        (
          "inner".to_string(),
          ComparableFilePatterns {
            include: Some(vec!["inner/**/*.ts".to_string()]),
            exclude: vec![
              "inner/other/**/*.ts".to_string(),
              "inner/sub/deeper/file.js".to_string(),
            ],
          }
        ),
        (
          "other".to_string(),
          ComparableFilePatterns {
            include: Some(vec!["other/**/*.js".to_string()]),
            exclude: vec![],
          }
        )
      ]
    );
  }

  #[test]
  fn from_relative() {
    let cwd = std::env::current_dir().unwrap();
    let pattern = PathOrPattern::from_relative(&cwd, "./**/*.ts").unwrap();
    assert_eq!(pattern.matches_path(&cwd.join("foo.ts")), true);
    assert_eq!(pattern.matches_path(&cwd.join("dir/foo.ts")), true);
    assert_eq!(pattern.matches_path(&cwd.join("foo.js")), false);
    assert_eq!(pattern.matches_path(&cwd.join("dir/foo.js")), false);
  }
}
