//! Helpers for writing Alfred script filter output.
//!
//! Example:
//!
//! ```
//! use serde_json::Value;
//! use alfred_json::{ItemBuilder, ScriptFilterOutputBuilder, ScriptFilterOutput};
//! let output: ScriptFilterOutput = ScriptFilterOutputBuilder::from([
//!     ItemBuilder::new("Item 1").subtitle("subtitle").into(),
//!     ItemBuilder::new("Item 2").valid(false).into(),
//! ]).into();
//! let output: Value = output.into();
//! println!("{}", output);
//! ```

use serde_json::{json, Value};
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;

#[cfg(feature = "fzf")]
pub mod fzf;

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum ModifierType {
    /// Command key
    Command,
    /// Option/Alt key
    Option,
    /// Control key
    Control,
    /// Shift key
    Shift,
    /// Fn key
    Fn,
}

impl AsRef<str> for ModifierType {
    fn as_ref(&self) -> &str {
        match &self {
            Self::Command => "cmd",
            Self::Option => "alt",
            Self::Control => "ctrl",
            Self::Shift => "shift",
            Self::Fn => "fn",
        }
    }
}

impl TryFrom<&str> for ModifierType {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        if value == "cmd" {
            Ok(Self::Command)
        } else if value == "alt" {
            Ok(Self::Option)
        } else if value == "ctrl" {
            Ok(Self::Control)
        } else if value == "shift" {
            Ok(Self::Shift)
        } else if value == "fn" {
            Ok(Self::Fn)
        } else {
            Err(())
        }
    }
}

impl fmt::Display for ModifierType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let str: &str = self.as_ref();
        write!(f, "{}", str)
    }
}

/// A modifier key or a combination of modifier keys.
///
/// Example 1:
///
/// ```
/// use alfred_json::ModifiersComb;
/// let mc = ModifiersComb::try_from("cmd+alt").unwrap();
/// ```
///
/// Example 2:
///
/// ```
/// use alfred_json::{ModifiersComb, ModifierType};
/// let mc = ModifiersComb::new_comb([ModifierType::Command, ModifierType::Option]).unwrap();
/// ```
#[derive(Eq, PartialEq, Hash, Debug)]
pub struct ModifiersComb {
    keys: Vec<ModifierType>,
}

impl fmt::Display for ModifiersComb {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut repr = String::new();
        repr.push_str(self.keys.get(0).unwrap().as_ref());
        for mf in &self.keys[1..] {
            repr.push('+');
            repr.push_str(mf.as_ref());
        }
        write!(f, "{}", repr)
    }
}

impl ModifiersComb {
    /// This is simply a wrapper over `ModifierType`.
    pub fn new(m: ModifierType) -> Self {
        Self { keys: vec![m] }
    }

    /// New modifier key combination of one or more different modifier keys.
    /// Panic if an empty `modifiers` is provided. Return `Err` if any pair of
    /// modifier keys are the same.
    pub fn new_comb<I: IntoIterator<Item = ModifierType>>(
        modifiers: I,
    ) -> Result<Self, ()> {
        let mut uniq = HashSet::new();
        for mf in modifiers.into_iter() {
            if !uniq.insert(mf) {
                return Err(());
            }
        }
        if uniq.is_empty() {
            panic!("`modifiers` is empty");
        }
        Ok(Self {
            keys: uniq.into_iter().collect(),
        })
    }

    /// New modifier key combination with no check on empty sequence or
    /// duplicate modifier keys.
    pub fn new_comb_unchecked<I: IntoIterator<Item = ModifierType>>(
        modifiers: I,
    ) -> Self {
        Self {
            keys: modifiers.into_iter().collect(),
        }
    }
}

impl TryFrom<&str> for ModifiersComb {
    type Error = ();

    /// Try constructing `ModifierComb` from string.
    ///
    /// For example,
    ///
    /// ```
    /// use alfred_json::{ModifiersComb, ModifierType};
    /// let modifiers: ModifiersComb = "cmd+alt".try_into().unwrap();
    /// ```
    fn try_from(value: &str) -> Result<ModifiersComb, ()> {
        let mut modifiers: Vec<ModifierType> = Vec::new();
        for mf_str in value.split('+') {
            modifiers.push(mf_str.try_into()?);
        }
        ModifiersComb::new_comb(modifiers)
    }
}

/// A convenient trait such that, instead of the style in the mod doc, users
/// may write:
///
/// ```
/// use alfred_json::{ItemBuilder, ScriptFilterOutputBuilder, ScriptFilterOutput, IntoJson};
/// let output: ScriptFilterOutput = ScriptFilterOutputBuilder::from([
///     ItemBuilder::new("Item 1").subtitle("subtitle").into(),
///     ItemBuilder::new("Item 2").valid(false).into(),
/// ]).into();
/// // One line shorter here:
/// println!("{}", output.into_json());
/// ```
pub trait IntoJson: Into<Value> {
    fn into_json(self) -> Value {
        self.into()
    }
}

impl<T: Into<Value>> IntoJson for T {}

/// Design choice: Why to use `String` in the key position? Because
/// `serde_json::Map` requires `String` in the key position. Converting to
/// `String` is inevitable.
pub type Variables<'a> = HashMap<String, Cow<'a, str>>;

struct HashMapWrapperVariables<'a>(Variables<'a>);

impl<'a> From<HashMapWrapperVariables<'a>> for Value {
    fn from(value: HashMapWrapperVariables) -> Self {
        let value = value.0;
        let mut vars = serde_json::Map::with_capacity(value.len());
        for (key, value) in value.into_iter() {
            vars.insert(key, json!(value));
        }
        Value::Object(vars)
    }
}

/// An icon.
pub enum Icon<'a> {
    /// Path to an image file on disk relative to the workflow directory.
    Path(Cow<'a, str>),
    /// Path to a file whose icon will be used.
    File(Cow<'a, str>),
    /// UTI for a file type to use (e.g. public.folder).
    FileType(Cow<'a, str>),
}

impl<'a> From<Icon<'a>> for Value {
    fn from(value: Icon<'a>) -> Self {
        use Icon::*;
        match value {
            Path(p) => json!({"path": p}),
            File(p) => json!({"type": "fileicon", "path": p}),
            FileType(uti) => json!({"type": "filetype", "path": uti}),
        }
    }
}

/// Builder for an `Icon` object.
pub struct IconBuilder<'a> {
    icon: Icon<'a>,
}

impl<'a> IconBuilder<'a> {
    /// The default icon type.
    pub fn path<S: Into<Cow<'a, str>>>(path: S) -> Self {
        Self {
            icon: Icon::Path(path.into()),
        }
    }

    /// The fileicon type.
    pub fn file<S: Into<Cow<'a, str>>>(path: S) -> Self {
        Self {
            icon: Icon::File(path.into()),
        }
    }

    /// The filetype type.
    pub fn filetype<S: Into<Cow<'a, str>>>(uti: S) -> Self {
        Self {
            icon: Icon::FileType(uti.into()),
        }
    }
}

impl<'a> From<IconBuilder<'a>> for Icon<'a> {
    /// Return the icon built.
    fn from(value: IconBuilder<'a>) -> Self {
        value.icon
    }
}

/// The type of `Item` object.
pub enum ItemType {
    /// Default type for an item.
    Default,
    /// Type representing a file.
    ///
    /// Already checks that the file exists on disk, and hides the result if it
    /// does not.
    File,
    /// Type representing a file, with filesystem checks skipped.
    ///
    /// Similar to `File` but skips the check to ensure the file exists.
    FileSkipCheck,
}

impl From<ItemType> for Value {
    fn from(value: ItemType) -> Self {
        use ItemType::*;
        match value {
            Default => json!("default"),
            File => json!("file"),
            FileSkipCheck => json!("file:skipcheck"),
        }
    }
}

/// An argument.
pub enum Arg<'a> {
    One(Cow<'a, str>),
    Many(Vec<Cow<'a, str>>),
}

impl<'a> From<Arg<'a>> for Value {
    fn from(value: Arg<'a>) -> Self {
        use Arg::*;
        match value {
            One(a) => json!(a),
            Many(args) => {
                Value::Array(args.into_iter().map(|a| json!(a)).collect())
            }
        }
    }
}

/// Builder for an `Arg`.
pub struct ArgBuilder<'a> {
    arg: Arg<'a>,
}

impl<'a> ArgBuilder<'a> {
    /// One argument.
    pub fn one<S: Into<Cow<'a, str>>>(arg: S) -> Self {
        Self {
            arg: Arg::One(arg.into()),
        }
    }

    /// A list of multiple arguments.
    pub fn many<S, I>(args: I) -> Self
    where
        S: Into<Cow<'a, str>>,
        I: IntoIterator<Item = S>,
    {
        Self {
            arg: Arg::Many(args.into_iter().map(Into::into).collect()),
        }
    }
}

impl<'a> From<ArgBuilder<'a>> for Arg<'a> {
    /// Return the arg built.
    fn from(value: ArgBuilder<'a>) -> Self {
        value.arg
    }
}

/// Builder for a collection of variables. Merely a wrapper over `HashMap`
/// that facilitates automatic `Into<_>` conversion.
///
/// Example 1:
///
/// ```
/// use std::collections::HashMap;
/// use alfred_json::VariablesBuilder;
/// let variables: HashMap<_, _> = VariablesBuilder::from([
///     ("hello", "world"),
///     ("foo", "bar"),
/// ]).into();
/// ```
///
/// Example 2:
///
/// ```
/// use std::collections::HashMap;
/// use alfred_json::VariablesBuilder;
/// let variables: HashMap<_, _> = VariablesBuilder::new()
///     .variable("hello", "world")
///     .variable("foo", "bar".to_string())
///     .into();
pub struct VariablesBuilder<'a> {
    variables: Variables<'a>,
}

impl<'a, K, V, I> From<I> for VariablesBuilder<'a>
where
    K: Into<String>,
    V: Into<Cow<'a, str>>,
    I: IntoIterator<Item = (K, V)>,
{
    fn from(value: I) -> Self {
        Self {
            variables: HashMap::from_iter(
                value.into_iter().map(|(k, v)| (k.into(), v.into())),
            ),
        }
    }
}

impl<'a> VariablesBuilder<'a> {
    pub fn new() -> Self {
        Self {
            variables: HashMap::new(),
        }
    }

    pub fn variable<K, V>(mut self, key: K, value: V) -> Self
    where
        K: Into<String>,
        V: Into<Cow<'a, str>>,
    {
        self.add_variable(key, value);
        self
    }

    pub fn add_variable<K, V>(&mut self, key: K, value: V)
    where
        K: Into<String>,
        V: Into<Cow<'a, str>>,
    {
        self.variables.insert(key.into(), value.into());
    }

    pub fn set_variables<K, V, I>(&mut self, kv_pairs: I)
    where
        K: Into<String>,
        V: Into<Cow<'a, str>>,
        I: IntoIterator<Item = (K, V)>,
    {
        self.variables = kv_pairs
            .into_iter()
            .map(|(k, v)| (k.into(), v.into()))
            .collect();
    }

    pub fn unset_variable(&mut self) {
        self.variables.clear();
    }
}

impl<'a> From<VariablesBuilder<'a>> for Variables<'a> {
    fn from(value: VariablesBuilder<'a>) -> Self {
        value.variables
    }
}

/// Optional overrides for modifiers.
#[derive(Default)]
pub struct ModifierData<'a> {
    subtitle: Option<Cow<'a, str>>,
    arg: Option<Arg<'a>>,
    valid: Option<bool>,
    icon: Option<Icon<'a>>,
    variables: Variables<'a>,
}

impl<'a> From<ModifierData<'a>> for Value {
    fn from(value: ModifierData<'a>) -> Self {
        let mut map = serde_json::Map::new();
        if let Some(subtitle) = value.subtitle {
            map.insert("subtitle".to_string(), json!(subtitle));
        }
        if let Some(arg) = value.arg {
            map.insert("arg".to_string(), arg.into());
        }
        if let Some(valid) = value.valid {
            map.insert("valid".to_string(), json!(valid));
        }
        if let Some(icon) = value.icon {
            map.insert("icon".to_string(), icon.into());
        }
        if !value.variables.is_empty() {
            map.insert(
                "variables".to_string(),
                HashMapWrapperVariables(value.variables).into(),
            );
        }

        Value::Object(map)
    }
}

impl<'a> ModifierData<'a> {
    pub fn set_subtitle<S: Into<Cow<'a, str>>>(&mut self, subtitle: S) {
        self.subtitle = Some(subtitle.into());
    }

    pub fn unset_subtitle(&mut self) {
        self.subtitle = None;
    }

    pub fn set_arg(&mut self, arg: Arg<'a>) {
        self.arg = Some(arg);
    }

    pub fn unset_arg(&mut self) {
        self.arg = None;
    }

    pub fn set_valid(&mut self, valid: bool) {
        self.valid = Some(valid)
    }

    pub fn unset_valid(&mut self) {
        self.valid = None;
    }

    pub fn set_icon(&mut self, icon: Icon<'a>) {
        self.icon = Some(icon);
    }

    pub fn unset_icon(&mut self) {
        self.icon = None;
    }

    pub fn set_variables(&mut self, variables: Variables<'a>) {
        self.variables = variables;
    }
}

/// Builder for a `ModifierData`.
pub struct ModifierDataBuilder<'a> {
    data: ModifierData<'a>,
}

impl<'a> From<ModifierDataBuilder<'a>> for ModifierData<'a> {
    /// Return the data built.
    fn from(value: ModifierDataBuilder<'a>) -> Self {
        value.data
    }
}

impl<'a> ModifierDataBuilder<'a> {
    pub fn new() -> Self {
        Self {
            data: Default::default(),
        }
    }

    pub fn subtitle<S: Into<Cow<'a, str>>>(mut self, subtitle: S) -> Self {
        self.data.set_subtitle(subtitle);
        self
    }

    pub fn arg(mut self, arg: Arg<'a>) -> Self {
        self.data.set_arg(arg);
        self
    }

    pub fn valid(mut self, valid: bool) -> Self {
        self.data.set_valid(valid);
        self
    }

    pub fn icon(mut self, icon: Icon<'a>) -> Self {
        self.data.set_icon(icon);
        self
    }

    pub fn variables(mut self, variables: Variables<'a>) -> Self {
        self.data.set_variables(variables);
        self
    }
}

/// Used for universal action.
pub enum Action<'a> {
    Simple(Arg<'a>),
    Typed {
        text: Option<Arg<'a>>,
        url: Option<Arg<'a>>,
        file: Option<Arg<'a>>,
        auto: Option<Arg<'a>>,
    },
}

impl<'a> From<Action<'a>> for Value {
    fn from(value: Action<'a>) -> Self {
        use Action::*;
        match value {
            Simple(a) => a.into(),
            Typed {
                text,
                url,
                file,
                auto,
            } => {
                let mut obj = serde_json::Map::new();
                if let Some(text) = text {
                    obj.insert("text".to_string(), text.into());
                }
                if let Some(url) = url {
                    obj.insert("url".to_string(), url.into());
                }
                if let Some(file) = file {
                    obj.insert("file".to_string(), file.into());
                }
                if let Some(auto) = auto {
                    obj.insert("auto".to_string(), auto.into());
                }
                Value::Object(obj)
            }
        }
    }
}

/// Builder for a typed action.
pub struct TypedActionBuilder<'a> {
    text: Option<Arg<'a>>,
    url: Option<Arg<'a>>,
    file: Option<Arg<'a>>,
    auto: Option<Arg<'a>>,
}

impl<'a> From<TypedActionBuilder<'a>> for Action<'a> {
    /// Return the action object built.
    fn from(value: TypedActionBuilder<'a>) -> Self {
        Self::Typed {
            text: value.text,
            url: value.url,
            file: value.file,
            auto: value.auto,
        }
    }
}

impl<'a> TypedActionBuilder<'a> {
    pub fn new() -> Self {
        Self {
            text: None,
            url: None,
            file: None,
            auto: None,
        }
    }

    pub fn text(mut self, arg: Arg<'a>) -> Self {
        self.text = Some(arg);
        self
    }

    pub fn url(mut self, arg: Arg<'a>) -> Self {
        self.url = Some(arg);
        self
    }

    pub fn file(mut self, arg: Arg<'a>) -> Self {
        self.file = Some(arg);
        self
    }

    pub fn auto(mut self, arg: Arg<'a>) -> Self {
        self.auto = Some(arg);
        self
    }
}

/// The text object.
pub struct Text<'a> {
    copy: Option<Cow<'a, str>>,
    largetype: Option<Cow<'a, str>>,
}

impl<'a> From<Text<'a>> for Value {
    fn from(value: Text<'a>) -> Self {
        let mut obj = serde_json::Map::new();
        if let Some(copy) = value.copy {
            obj.insert("copy".to_string(), json!(copy));
        }
        if let Some(largetype) = value.largetype {
            obj.insert("largetype".to_string(), json!(largetype));
        }
        Value::Object(obj)
    }
}

/// Builder for a `Text` object.
pub struct TextBuilder<'a> {
    text: Text<'a>,
}

impl<'a> TextBuilder<'a> {
    pub fn new() -> Self {
        Self {
            text: Text {
                copy: None,
                largetype: None,
            },
        }
    }

    pub fn copy<S: Into<Cow<'a, str>>>(mut self, copy: S) -> Self {
        self.text.copy = Some(copy.into());
        self
    }

    pub fn largetype<S: Into<Cow<'a, str>>>(mut self, largetype: S) -> Self {
        self.text.largetype = Some(largetype.into());
        self
    }
}

impl<'a> From<TextBuilder<'a>> for Text<'a> {
    /// Return the text built.
    fn from(value: TextBuilder<'a>) -> Self {
        value.text
    }
}

/// A script filter item.
pub struct Item<'a> {
    uid: Option<Cow<'a, str>>,
    title: Cow<'a, str>,
    subtitle: Option<Cow<'a, str>>,
    arg: Option<Arg<'a>>,
    icon: Option<Icon<'a>>,
    valid: Option<bool>,
    // intentionally allow list for my extension
    match_: Option<Arg<'a>>,
    autocomplete: Option<Cow<'a, str>>,
    type_: Option<ItemType>,
    mods: HashMap<ModifiersComb, ModifierData<'a>>,
    action: Option<Action<'a>>,
    text: Option<Text<'a>>,
    quicklookurl: Option<Cow<'a, str>>,
    variables: Variables<'a>,
}

struct HashMapWrapperModifier<'a>(HashMap<ModifiersComb, ModifierData<'a>>);

impl<'a> From<HashMapWrapperModifier<'a>> for Value {
    fn from(value: HashMapWrapperModifier<'a>) -> Self {
        let value = value.0;
        let mut obj = serde_json::Map::with_capacity(value.len());
        for (key, value) in value.into_iter() {
            obj.insert(key.to_string(), value.into());
        }
        Value::Object(obj)
    }
}

impl<'a> From<Item<'a>> for Value {
    fn from(value: Item<'a>) -> Self {
        let mut obj = serde_json::Map::new();
        obj.insert("title".to_string(), json!(value.title));
        if let Some(uid) = value.uid {
            obj.insert("uid".to_string(), json!(uid));
        }
        if let Some(subtitle) = value.subtitle {
            obj.insert("subtitle".to_string(), json!(subtitle));
        }
        if let Some(arg) = value.arg {
            obj.insert("arg".to_string(), arg.into());
        }
        if let Some(icon) = value.icon {
            obj.insert("icon".to_string(), icon.into());
        }
        if let Some(valid) = value.valid {
            obj.insert("valid".to_string(), json!(valid));
        }
        if let Some(match_) = value.match_ {
            obj.insert("match".to_string(), match_.into());
        }
        if let Some(autocomplete) = value.autocomplete {
            obj.insert("autocomplete".to_string(), json!(autocomplete));
        }
        if let Some(type_) = value.type_ {
            obj.insert("type".to_string(), type_.into());
        }
        if !value.mods.is_empty() {
            obj.insert(
                "mods".to_string(),
                HashMapWrapperModifier(value.mods).into(),
            );
        }
        if let Some(action) = value.action {
            obj.insert("action".to_string(), action.into());
        }
        if let Some(text) = value.text {
            obj.insert("text".to_string(), text.into());
        }
        if let Some(quicklookurl) = value.quicklookurl {
            obj.insert("quicklookurl".to_string(), json!(quicklookurl));
        }
        if !value.variables.is_empty() {
            obj.insert(
                "variables".to_string(),
                HashMapWrapperVariables(value.variables).into(),
            );
        }
        Value::Object(obj)
    }
}

/// Builder for an Item.
pub struct ItemBuilder<'a> {
    item: Item<'a>,
}

impl<'a> From<ItemBuilder<'a>> for Item<'a> {
    /// Return the item built.
    fn from(value: ItemBuilder<'a>) -> Self {
        value.item
    }
}

impl<'a> ItemBuilder<'a> {
    /// A new item with title.
    pub fn new<S: Into<Cow<'a, str>>>(title: S) -> Self {
        Self {
            item: Item {
                uid: None,
                title: title.into(),
                subtitle: None,
                arg: None,
                icon: None,
                valid: None,
                match_: None,
                autocomplete: None,
                type_: None,
                mods: HashMap::new(),
                action: None,
                text: None,
                quicklookurl: None,
                variables: HashMap::new(),
            },
        }
    }

    pub fn set_uid<S: Into<Cow<'a, str>>>(&mut self, uid: S) {
        self.item.uid = Some(uid.into());
    }

    pub fn unset_uid(&mut self) {
        self.item.uid = None;
    }

    pub fn uid<S: Into<Cow<'a, str>>>(mut self, uid: S) -> Self {
        self.set_uid(uid);
        self
    }

    pub fn set_subtitle<S: Into<Cow<'a, str>>>(&mut self, subtitle: S) {
        self.item.subtitle = Some(subtitle.into());
    }

    pub fn reset_subtitle(&mut self) {
        self.item.subtitle = None;
    }

    pub fn subtitle<S: Into<Cow<'a, str>>>(mut self, subtitle: S) -> Self {
        self.set_subtitle(subtitle);
        self
    }

    pub fn set_arg(&mut self, arg: Arg<'a>) {
        self.item.arg = Some(arg);
    }

    pub fn unset_arg(&mut self) {
        self.item.arg = None;
    }

    pub fn arg(mut self, arg: Arg<'a>) -> Self {
        self.set_arg(arg);
        self
    }

    pub fn set_icon(&mut self, icon: Icon<'a>) {
        self.item.icon = Some(icon);
    }

    pub fn unset_icon(&mut self) {
        self.item.icon = None;
    }

    pub fn icon(mut self, icon: Icon<'a>) -> Self {
        self.set_icon(icon);
        self
    }

    pub fn set_valid(&mut self, valid: bool) {
        self.item.valid = Some(valid);
    }

    pub fn unset_valid(&mut self) {
        self.item.valid = None;
    }

    pub fn valid(mut self, valid: bool) -> Self {
        self.set_valid(valid);
        self
    }

    pub fn set_match(&mut self, arg: Arg<'a>) {
        self.item.match_ = Some(arg);
    }

    pub fn unset_match(&mut self) {
        self.item.match_ = None;
    }

    pub fn match_(mut self, arg: Arg<'a>) -> Self {
        self.set_match(arg);
        self
    }

    pub fn set_autocomplete<S: Into<Cow<'a, str>>>(&mut self, autocomplete: S) {
        self.item.autocomplete = Some(autocomplete.into());
    }

    pub fn unset_autocomplete(&mut self) {
        self.item.autocomplete = None;
    }

    pub fn autocomplete<S: Into<Cow<'a, str>>>(
        mut self,
        autocomplete: S,
    ) -> Self {
        self.set_autocomplete(autocomplete);
        self
    }

    pub fn set_type(&mut self, type_: ItemType) {
        self.item.type_ = Some(type_);
    }

    pub fn unset_type(&mut self) {
        self.item.type_ = None;
    }

    pub fn type_(mut self, type_: ItemType) -> Self {
        self.set_type(type_);
        self
    }

    pub fn get_mod_mut(&mut self, key: ModifiersComb) -> &mut ModifierData<'a> {
        self.item.mods.entry(key).or_insert_with(Default::default)
    }

    pub fn mod_(mut self, key: ModifiersComb, data: ModifierData<'a>) -> Self {
        self.item.mods.insert(key, data);
        self
    }

    pub fn set_action(&mut self, arg: Arg<'a>) {
        self.item.action = Some(Action::Simple(arg));
    }

    pub fn set_typed_action(&mut self, arg: Action<'a>) {
        self.item.action = Some(arg);
    }

    pub fn unset_action(&mut self) {
        self.item.action = None;
    }

    pub fn action(mut self, arg: Arg<'a>) -> Self {
        self.set_action(arg);
        self
    }

    pub fn typed_action(mut self, arg: Action<'a>) -> Self {
        self.set_typed_action(arg);
        self
    }

    pub fn set_text(&mut self, text: Text<'a>) {
        self.item.text = Some(text);
    }

    pub fn unset_text(&mut self) {
        self.item.text = None;
    }

    pub fn text(mut self, text: Text<'a>) -> Self {
        self.set_text(text);
        self
    }

    pub fn set_quicklookurl<S: Into<Cow<'a, str>>>(&mut self, quicklookurl: S) {
        self.item.quicklookurl = Some(quicklookurl.into());
    }

    pub fn unset_quicklookurl(&mut self) {
        self.item.quicklookurl = None;
    }

    pub fn quicklookurl<S: Into<Cow<'a, str>>>(
        mut self,
        quicklookurl: S,
    ) -> Self {
        self.set_quicklookurl(quicklookurl);
        self
    }

    pub fn set_variables(&mut self, variables: Variables<'a>) {
        self.item.variables = variables;
    }

    pub fn variables(mut self, variables: Variables<'a>) -> Self {
        self.set_variables(variables);
        self
    }
}

pub struct ScriptFilterOutput<'a> {
    items: Vec<Item<'a>>,
    /// Item variables
    variables: Variables<'a>,
    /// Rerun script filters
    rerun: Option<f32>,
}

impl<'a> From<ScriptFilterOutput<'a>> for Value {
    fn from(value: ScriptFilterOutput<'a>) -> Self {
        let mut obj = serde_json::Map::new();
        obj.insert(
            "items".to_string(),
            Value::Array(value.items.into_iter().map(Into::into).collect()),
        );
        if !value.variables.is_empty() {
            obj.insert(
                "variables".to_string(),
                HashMapWrapperVariables(value.variables).into(),
            );
        }
        if let Some(rerun) = value.rerun {
            obj.insert("rerun".to_string(), json!(rerun));
        }
        Value::Object(obj)
    }
}

/// Builder for `ScriptFilterOutput`.
///
/// Example:
///
/// ```
/// use alfred_json::{ItemBuilder, ScriptFilterOutput, ScriptFilterOutputBuilder};
/// let sf: ScriptFilterOutput = ScriptFilterOutputBuilder::from([
///     ItemBuilder::new("foo").into(),
///     ItemBuilder::new("bar").into(),
/// ]).into();
/// ```
pub struct ScriptFilterOutputBuilder<'a> {
    resp: ScriptFilterOutput<'a>,
}

impl<'a> From<ScriptFilterOutputBuilder<'a>> for ScriptFilterOutput<'a> {
    /// Return the output built.
    fn from(value: ScriptFilterOutputBuilder<'a>) -> Self {
        value.resp
    }
}

impl<'a> ScriptFilterOutputBuilder<'a> {
    pub fn new() -> Self {
        Self {
            resp: ScriptFilterOutput {
                items: Vec::new(),
                variables: HashMap::new(),
                rerun: None,
            },
        }
    }

    pub fn set_variables(&mut self, variables: Variables<'a>) {
        self.resp.variables = variables;
    }

    pub fn variables(mut self, variables: Variables<'a>) -> Self {
        self.set_variables(variables);
        self
    }

    pub fn set_rerun(&mut self, rerun: f32) {
        self.resp.rerun = Some(rerun);
    }

    pub fn unset_rerun(&mut self) {
        self.resp.rerun = None;
    }

    pub fn rerun(mut self, rerun: f32) -> Self {
        self.set_rerun(rerun);
        self
    }
}

impl<'a> From<Item<'a>> for ScriptFilterOutputBuilder<'a> {
    fn from(value: Item<'a>) -> Self {
        Self {
            resp: ScriptFilterOutput {
                items: vec![value],
                variables: HashMap::new(),
                rerun: None,
            },
        }
    }
}

impl<'a, I> From<I> for ScriptFilterOutputBuilder<'a>
where
    I: IntoIterator<Item = Item<'a>>,
{
    fn from(value: I) -> Self {
        Self {
            resp: ScriptFilterOutput {
                items: value.into_iter().collect(),
                variables: HashMap::new(),
                rerun: None,
            },
        }
    }
}

/// The JSON config object.
pub struct JsonConfig<'a> {
    arg: Option<Arg<'a>>,
    variables: Variables<'a>,
}

impl<'a> From<JsonConfig<'a>> for Value {
    fn from(value: JsonConfig<'a>) -> Self {
        let mut obj = serde_json::Map::new();
        if let Some(arg) = value.arg {
            obj.insert("arg".to_string(), arg.into());
        }
        if !value.variables.is_empty() {
            obj.insert(
                "variables".to_string(),
                HashMapWrapperVariables(value.variables).into(),
            );
        }
        Value::Object(serde_json::Map::from_iter([(
            "alfredworkflow".to_string(),
            Value::Object(obj),
        )]))
    }
}

/// Builder for `JsonConfig`.
///
/// Example:
///
/// ```
/// use alfred_json::{ArgBuilder, JsonConfig, JsonConfigBuilder};
/// let config: JsonConfig = JsonConfigBuilder::new()
///     .arg(ArgBuilder::one("foo").into())
///     .into();
/// ```
pub struct JsonConfigBuilder<'a> {
    config: JsonConfig<'a>,
}

impl<'a> From<JsonConfigBuilder<'a>> for JsonConfig<'a> {
    fn from(value: JsonConfigBuilder<'a>) -> Self {
        value.config
    }
}

impl<'a> JsonConfigBuilder<'a> {
    pub fn new() -> Self {
        Self {
            config: JsonConfig {
                arg: None,
                variables: HashMap::new(),
            },
        }
    }

    pub fn set_arg(&mut self, arg: Arg<'a>) {
        self.config.arg = Some(arg);
    }

    pub fn unset_arg(&mut self) {
        self.config.arg = None;
    }

    pub fn arg(mut self, arg: Arg<'a>) -> Self {
        self.set_arg(arg);
        self
    }

    pub fn set_variables(&mut self, variables: Variables<'a>) {
        self.config.variables = variables;
    }

    pub fn variables(mut self, variables: Variables<'a>) -> Self {
        self.set_variables(variables);
        self
    }
}

#[cfg(test)]
mod tests {
    use crate::scriptfilter::{ModifierType, ModifiersComb};
    use std::collections::HashSet;
    use std::hash::Hash;

    #[test]
    fn test_modifiers_comb_display() {
        let mfc = ModifiersComb::new_comb([
            ModifierType::Command,
            ModifierType::Option,
        ])
        .unwrap();
        assert!(vec!["cmd+alt", "alt+cmd"].contains(&mfc.to_string().as_str()))
    }

    #[test]
    #[should_panic]
    fn test_modifiers_comb_new_comb_empty() {
        ModifiersComb::new_comb([]).unwrap();
    }

    fn into_hashset<T: Eq + Hash, I: IntoIterator<Item = T>>(
        iter: I,
    ) -> HashSet<T> {
        iter.into_iter().collect()
    }

    #[test]
    fn test_modifiers_comb_new_comb() {
        ModifiersComb::new_comb([
            ModifierType::Command,
            ModifierType::Option,
            ModifierType::Command,
        ])
        .unwrap_err();
        assert_eq!(
            into_hashset(
                ModifiersComb::new_comb([
                    ModifierType::Command,
                    ModifierType::Option
                ])
                .unwrap()
                .keys
            ),
            into_hashset([ModifierType::Command, ModifierType::Option])
        );
    }

    #[test]
    fn test_modifiers_comb_try_from_str() {
        assert_eq!(
            ModifiersComb::try_from("cmd").unwrap(),
            ModifiersComb::new(ModifierType::Command)
        );
        assert_eq!(
            into_hashset(ModifiersComb::try_from("cmd+alt").unwrap().keys),
            into_hashset([ModifierType::Command, ModifierType::Option])
        );
        assert_eq!(ModifiersComb::try_from("xyz"), Err(()));
    }
}
