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
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::io::Write;
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

/// `HashMap` that remembers the insertion order. The key must implement the
/// `Copy` trait.
struct OrderedHashMap<K, V> {
    map: HashMap<K, V>,
    order: Vec<K>,
}

impl<K: Copy + Eq + Hash, V> OrderedHashMap<K, V> {
    fn new() -> Self {
        Self {
            map: HashMap::new(),
            order: Vec::new(),
        }
    }

    fn insert(&mut self, k: K, v: V) -> Option<V> {
        match self.map.insert(k, v) {
            Some(v) => Some(v),
            None => {
                self.order.push(k);
                None
            }
        }
    }

    fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.map.get(k)
    }

    fn keys(&self) -> Vec<K> {
        self.order.iter().map(|k| *k).collect()
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
    candidates: OrderedHashMap<&str, usize>,
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
    let mut message = String::new();
    for key in candidates.keys() {
        message.push_str(key);
        message.push('\n');
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
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
    {
        Err(_) => Err(FzfError::Launch),
        Ok(mut proc) => {
            let mut stdin = proc.stdin.take().unwrap();
            std::thread::spawn(move || {
                stdin.write_all(message.as_bytes()).unwrap()
            });
            let proc = proc.wait_with_output().unwrap();
            match proc.status.code() {
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
            }
        }
    }
}

fn parse_items_into_candidates<'a>(
    items: &'a [Item<'a>],
) -> Result<OrderedHashMap<&'a str, usize>, FzfError> {
    let mut candidates = OrderedHashMap::new();
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
    Ok(candidates)
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

#[cfg(test)]
mod tests {
    use crate::fzf::fzf_filter;
    use crate::{Builder, ItemBuilder};

    #[test]
    fn test_fzf_filter() {
        let items = vec![
            ItemBuilder::new("foo").into_output(),
            ItemBuilder::new("bar").into_output(),
        ];
        let items = fzf_filter("foo", items, true).unwrap();
        assert_eq!(items.len(), 1);
        assert_eq!(items.get(0).unwrap().title, "foo");
    }
}
