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

/// Map key to some positions. Duplicate keys are allowed.
struct PositionMap<K>(HashMap<K, Vec<usize>>);

impl<K> PositionMap<K> {
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn insert(&mut self, k: K, v: usize)
    where
        K: Copy + Eq + Hash,
    {
        self.0.entry(k).or_default().push(v);
    }

    fn get<Q: ?Sized>(&self, k: &Q) -> Option<&[usize]>
    where
        K: Borrow<Q> + Eq + Hash,
        Q: Hash + Eq,
    {
        self.0.get(k).map(Vec::as_ref)
    }

    fn keys(&self) -> impl Iterator<Item = K> + '_
    where
        K: Copy,
    {
        self.0.keys().map(|k| *k)
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
    candidates: PositionMap<&str>,
    exact: bool,
) -> Result<HashSet<usize>, FzfError> {
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

    let process_output = |lines| -> Result<HashSet<usize>, FzfError> {
        let mut uniq = HashSet::new();
        for line in lines {
            let ind = candidates.get(line).context(FzfError::Parse)?;
            uniq.extend(ind);
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
                    1 => Ok(HashSet::new()),
                    _ => Err(FzfError::ErrCode(code)),
                },
            }
        }
    }
}

fn parse_items_into_candidates<'a>(
    items: &'a [Item<'a>],
) -> Result<PositionMap<&'a str>, FzfError> {
    let mut candidates = PositionMap::new();
    for (j, item) in items.into_iter().enumerate() {
        let match_strs: Vec<&str> = match item.match_ {
            None => vec![item.title.as_ref()],
            Some(ref arg) => match arg {
                Arg::One(a) => vec![a],
                Arg::Many(a) => a.into_iter().map(AsRef::as_ref).collect(),
            },
        };
        for s in match_strs {
            candidates.insert(s, j);
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
    use crate::scriptfilter::fzf::PositionMap;
    use crate::{ArgBuilder, Builder, Item, ItemBuilder};

    #[test]
    fn test_ordered_position_map() {
        let mut map = PositionMap::new();
        map.insert("foo", 0);
        map.insert("bar", 0);
        map.insert("foo", 1);
        map.insert("baz", 2);
        assert_eq!(map.get("foo"), Some([0, 1].as_slice()));
        assert_eq!(map.get("bar"), Some([0].as_slice()));
        assert_eq!(map.get("baz"), Some([2].as_slice()));
    }

    #[test]
    fn test_fzf_filter() {
        fn test_case1<'a>() -> Vec<Item<'a>> {
            vec![
                ItemBuilder::new("foo").into_output(),
                ItemBuilder::new("bar").into_output(),
            ]
        }

        let items = fzf_filter("foo", test_case1(), true).unwrap();
        assert_eq!(items.len(), 1);
        assert_eq!(items.get(0).unwrap().title, "foo");

        fn test_case2<'a>() -> Vec<Item<'a>> {
            vec![
                ItemBuilder::new("a")
                    .match_(ArgBuilder::many(["foo", "bar"]).into_output())
                    .into_output(),
                ItemBuilder::new("baz").into_output(),
                ItemBuilder::new("c")
                    .match_(ArgBuilder::many(["foo", "bar"]).into_output())
                    .into_output(),
            ]
        }

        let items = fzf_filter("ba", test_case2(), false).unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items.get(0).unwrap().title, "a");
        assert_eq!(items.get(1).unwrap().title, "baz");
        assert_eq!(items.get(2).unwrap().title, "c");

        let items = fzf_filter("bar", test_case2(), true).unwrap();
        assert_eq!(items.len(), 2);
        assert_eq!(items.get(0).unwrap().title, "a");
        assert_eq!(items.get(1).unwrap().title, "c");
    }
}
