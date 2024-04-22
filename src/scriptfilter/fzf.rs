//! Item filtering through [`fzf`](https://github.com/junegunn/fzf) (require
//! `fzf` to be installed locally).
//! 
//! Example:
//! 
//! ```
//! use alfred_json::{Item, ItemBuilder};
//! use alfred_json::fzf::fzf_filter;
//!
//! let items: Vec<Item> = vec![
//!     ItemBuilder::new("foo").into(),
//!     ItemBuilder::new("bar").into(),
//! ];
//! let foo: Vec<Item> = fzf_filter("foo", items, true).unwrap();
//! ```
//! 

use crate::scriptfilter::Item;
use crate::Arg;
use std::collections::{HashMap, HashSet};
use std::process::{Command, Stdio};

/// Errors while requesting `fzf`.
#[derive(Debug)]
pub enum FzfError {
    /// Failed to launch `fzf`.
    Launch,
    /// Incorrect exit code.
    ErrCode(i32),
    /// Terminated by signal.
    SigTerm,
    /// Failed to parse the output of `fzf`.
    Parse,
    /// Duplicate match strings detected.
    DuplicateKey,
}

/// A simple port of `anyhow::Context` here for convenience.
trait Context<T> {
    fn context<C>(self, context: C) -> Result<T, C>;
}

impl<T> Context<T> for Option<T> {
    fn context<C>(self, context: C) -> Result<T, C> {
        match self {
            Some(value) => Ok(value),
            None => Err(context),
        }
    }
}

/// Return a Vec of unique selected indices, or `FzfError` if any error occurs.
///
/// Arguments:
///
/// - `query`: the `fzf` query.
/// - `candidates`: a mapping from `fzf` candidates to index into items.
/// - `exact`: `true` to pass "--exact" to `fzf`.
///
fn request_fzf(
    query: &str,
    candidates: HashMap<&str, usize>,
    exact: bool,
) -> Result<Vec<usize>, FzfError> {
    // Prepare fzf argv
    let mut fzf_argv = Vec::new();
    if exact {
        fzf_argv.push("--exact");
    }
    fzf_argv.push("--filter");
    fzf_argv.push(query);

    // Prepare stdin to fzf
    let mut stdin = String::new();
    for (key, _) in candidates.iter() {
        stdin.push_str(key);
        stdin.push('\n');
    }

    let process_output = |lines| -> Result<Vec<usize>, FzfError> {
        let mut uniq = Vec::new();
        let mut uniq_set = HashSet::new();
        for line in lines {
            let index = candidates.get(line).context(FzfError::Parse)?;
            if uniq_set.insert(*index) {
                uniq.push(*index);
            }
        }
        Ok(uniq)
    };

    match Command::new("fzf")
        .args(fzf_argv)
        .stderr(Stdio::null())
        .output()
    {
        Err(_) => Err(FzfError::Launch),
        Ok(proc) => match proc.status.code() {
            None => Err(FzfError::SigTerm),
            Some(code) => match code {
                0 => process_output(
                    String::from_utf8(proc.stdout)
                        .map_err(|_| FzfError::Parse)?
                        .lines(),
                ),
                1 => Ok(Vec::new()),
                _ => Err(FzfError::ErrCode(code)),
            },
        },
    }
}

fn parse_items_into_candidates<'a>(
    items: &'a [Item<'a>],
) -> Result<HashMap<&'a str, usize>, FzfError> {
    let mut candidates = HashMap::new();
    for (j, item) in items.into_iter().enumerate() {
        let match_strs: Vec<&'a str> = match item.match_ {
            None => vec![item.title.as_ref()],
            Some(ref arg) => match arg {
                Arg::One(a) => vec![a],
                Arg::Many(a) => a.into_iter().map(AsRef::as_ref).collect(),
            },
        };
        for s in match_strs {
            if candidates.insert(s, j).is_some() {
                return Err(FzfError::DuplicateKey);
            }
        }
    }
    Ok(candidates.into())
}

/// Request `fzf` to fuzzy filter items with query. For each `item`, the match
/// string is taken from either `match` field or `title` if the former does not
/// exist. Return `Err(FzfError)` on error. See `FzfError` for the causes of the
/// error.
///
/// Arguments:
///
/// - `query`: the `fzf` query.
/// - `items`: the items to filter
/// - `exact`: `true` to pass "--exact" to `fzf`
pub fn fzf_filter<'a>(
    query: &str,
    mut items: Vec<Item<'a>>,
    exact: bool,
) -> Result<Vec<Item<'a>>, FzfError> {
    let candidates = parse_items_into_candidates(items.as_slice())?;
    let matched_indices = request_fzf(query, candidates, exact)?;
    let mut keep = vec![false; items.len()];
    for j in matched_indices {
        keep[j] = true;
    }
    let mut keep_iter = keep.iter();
    items.retain(|_| *keep_iter.next().unwrap());

    Ok(items)
}
