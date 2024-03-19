//! Helpers for writing Alfred script filter output.
//!
//! Example:
//!
//! ```
//! use alfred_json::scriptfilter::{ItemBuilder, ScriptFilterOutputBuilder, IntoJson};
//! let output = ScriptFilterOutputBuilder::from_items([
//!     ItemBuilder::new("Item 1").subtitle("subtitle").into_item(),
//!     ItemBuilder::new("Item 2").valid(false).into_item(),
//! ]).into_output();
//! println!("{}", output.into_json());
//! ```

use serde_json::{json, Value};
use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;

#[derive(PartialEq, Eq, Hash)]
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

impl fmt::Display for ModifierType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let str = match &self {
            Self::Command => "cmd",
            Self::Option => "alt",
            Self::Control => "ctrl",
            Self::Shift => "shift",
            Self::Fn => "fn",
        };
        write!(f, "{}", str)
    }
}

#[derive(Eq, PartialEq, Hash)]
enum ModifiersCombVariants {
    One(ModifierType),
    Two(ModifierType, ModifierType),
    Three(ModifierType, ModifierType, ModifierType),
    Four(ModifierType, ModifierType, ModifierType, ModifierType),
    Five(
        ModifierType,
        ModifierType,
        ModifierType,
        ModifierType,
        ModifierType,
    ),
}

/// A modifier key or a combination of modifier keys.
#[derive(Eq, PartialEq, Hash)]
pub struct ModifiersComb {
    keys: ModifiersCombVariants,
}

impl fmt::Display for ModifiersComb {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.keys {
            ModifiersCombVariants::One(m1) => write!(f, "{}", m1),
            ModifiersCombVariants::Two(m1, m2) => write!(f, "{}+{}", m1, m2),
            ModifiersCombVariants::Three(m1, m2, m3) => {
                write!(f, "{}+{}+{}", m1, m2, m3)
            }
            ModifiersCombVariants::Four(m1, m2, m3, m4) => {
                write!(f, "{}+{}+{}+{}", m1, m2, m3, m4)
            }
            ModifiersCombVariants::Five(m1, m2, m3, m4, m5) => {
                write!(f, "{}+{}+{}+{}+{}", m1, m2, m3, m4, m5)
            }
        }
    }
}

/// Indicate that there's duplicate in a combination of modifier keys.
#[derive(Debug)]
pub struct DuplicateModifierTypeError;

impl ModifiersComb {
    /// This is simply a wrapper over `ModifierType`.
    pub fn new(m: ModifierType) -> Self {
        Self {
            keys: ModifiersCombVariants::One(m),
        }
    }

    /// New modifier key combination of two different modifier keys.
    pub fn new_comb(
        m1: ModifierType,
        m2: ModifierType,
    ) -> Result<Self, DuplicateModifierTypeError> {
        if m1 == m2 {
            return Err(DuplicateModifierTypeError);
        }
        Ok(Self {
            keys: ModifiersCombVariants::Two(m1, m2),
        })
    }

    /// New modifier key combination of three different modifier keys.
    pub fn new_comb3(
        m1: ModifierType,
        m2: ModifierType,
        m3: ModifierType,
    ) -> Result<Self, DuplicateModifierTypeError> {
        if m1 == m2 || m2 == m3 {
            return Err(DuplicateModifierTypeError);
        }
        Ok(Self {
            keys: ModifiersCombVariants::Three(m1, m2, m3),
        })
    }

    /// New modifier key combination of four different modifier keys.
    pub fn new_comb4(
        m1: ModifierType,
        m2: ModifierType,
        m3: ModifierType,
        m4: ModifierType,
    ) -> Result<Self, DuplicateModifierTypeError> {
        if m1 == m2 || m2 == m3 || m3 == m4 {
            return Err(DuplicateModifierTypeError);
        }
        Ok(Self {
            keys: ModifiersCombVariants::Four(m1, m2, m3, m4),
        })
    }

    /// New modifier key combination of five different modifier keys.
    pub fn new_comb5(
        m1: ModifierType,
        m2: ModifierType,
        m3: ModifierType,
        m4: ModifierType,
        m5: ModifierType,
    ) -> Result<Self, DuplicateModifierTypeError> {
        if m1 == m2 || m2 == m3 || m3 == m4 || m4 == m5 {
            return Err(DuplicateModifierTypeError);
        }
        Ok(Self {
            keys: ModifiersCombVariants::Five(m1, m2, m3, m4, m5),
        })
    }
}

pub trait IntoJson {
    fn into_json(self) -> Value;
}

impl<'a> IntoJson for HashMap<Cow<'a, str>, Cow<'a, str>> {
    fn into_json(self) -> Value {
        let mut vars = serde_json::Map::with_capacity(self.len());
        for (key, value) in self.into_iter() {
            vars.insert(key.into_owned(), json!(value));
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

impl<'a> IntoJson for Icon<'a> {
    fn into_json(self) -> Value {
        match self {
            Self::Path(p) => json!({"path": p}),
            Self::File(p) => json!({"type": "fileicon", "path": p}),
            Self::FileType(uti) => json!({"type": "filetype", "path": uti}),
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

    /// Return the icon built.
    pub fn into_icon(self) -> Icon<'a> {
        self.icon
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

impl IntoJson for ItemType {
    fn into_json(self) -> Value {
        match self {
            Self::Default => json!("default"),
            Self::File => json!("file"),
            Self::FileSkipCheck => json!("file:skipcheck"),
        }
    }
}

/// An argument.
pub enum Arg<'a> {
    One(Cow<'a, str>),
    Many(Vec<Cow<'a, str>>),
}

impl<'a> IntoJson for Arg<'a> {
    fn into_json(self) -> Value {
        match self {
            Self::One(a) => json!(a),
            Self::Many(args) => {
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

    /// Return the arg built.
    pub fn into_arg(self) -> Arg<'a> {
        self.arg
    }
}

/// Builder for a collection of variables.
pub struct VariablesBuilder<'a> {
    variables: HashMap<Cow<'a, str>, Cow<'a, str>>,
}

impl<'a> VariablesBuilder<'a> {
    pub fn new() -> Self {
        Self {
            variables: HashMap::new(),
        }
    }

    pub fn from<K, V, I>(kv_pairs: I) -> Self
    where
        K: Into<Cow<'a, str>>,
        V: Into<Cow<'a, str>>,
        I: IntoIterator<Item = (K, V)>,
    {
        Self {
            variables: HashMap::from_iter(
                kv_pairs.into_iter().map(|(k, v)| (k.into(), v.into())),
            ),
        }
    }

    /// Return the variables built.
    pub fn into_variables(self) -> HashMap<Cow<'a, str>, Cow<'a, str>> {
        self.variables
    }

    pub fn add_variable<K, V>(&mut self, key: K, value: V)
    where
        K: Into<Cow<'a, str>>,
        V: Into<Cow<'a, str>>,
    {
        self.variables.insert(key.into(), value.into());
    }

    pub fn set_variables<K, V, I>(&mut self, kv_pairs: I)
    where
        K: Into<Cow<'a, str>>,
        V: Into<Cow<'a, str>>,
        I: IntoIterator<Item = (K, V)>,
    {
        self.variables.clear();
        self.variables
            .extend(kv_pairs.into_iter().map(|(k, v)| (k.into(), v.into())));
    }

    pub fn unset_variable(&mut self) {
        self.variables.clear();
    }
}

/// Optional overrides for modifiers.
#[derive(Default)]
pub struct ModifierData<'a> {
    subtitle: Option<Cow<'a, str>>,
    arg: Option<Arg<'a>>,
    valid: Option<bool>,
    icon: Option<Icon<'a>>,
    variables: HashMap<Cow<'a, str>, Cow<'a, str>>,
}

impl<'a> IntoJson for ModifierData<'a> {
    fn into_json(self) -> Value {
        let mut map = serde_json::Map::new();
        if let Some(subtitle) = self.subtitle {
            map.insert("subtitle".to_string(), json!(subtitle));
        }
        if let Some(arg) = self.arg {
            map.insert("arg".to_string(), arg.into_json());
        }
        if let Some(valid) = self.valid {
            map.insert("valid".to_string(), json!(valid));
        }
        if let Some(icon) = self.icon {
            map.insert("icon".to_string(), icon.into_json());
        }
        if !self.variables.is_empty() {
            map.insert("variables".to_string(), self.variables.into_json());
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

    pub fn set_variables(
        &mut self,
        variables: HashMap<Cow<'a, str>, Cow<'a, str>>,
    ) {
        self.variables.clear();
        self.variables.extend(variables);
    }
}

/// Builder for a `ModifierData`.
pub struct ModifierDataBuilder<'a> {
    data: ModifierData<'a>,
}

impl<'a> ModifierDataBuilder<'a> {
    pub fn new() -> Self {
        Self {
            data: Default::default(),
        }
    }

    /// Return the data built.
    pub fn into_modifier_data(self) -> ModifierData<'a> {
        self.data
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

    pub fn variables<K, V, I>(
        mut self,
        variables: HashMap<Cow<'a, str>, Cow<'a, str>>,
    ) -> Self {
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

impl<'a> IntoJson for Action<'a> {
    fn into_json(self) -> Value {
        match self {
            Self::Simple(a) => a.into_json(),
            Self::Typed {
                text,
                url,
                file,
                auto,
            } => {
                let mut obj = serde_json::Map::new();
                if let Some(text) = text {
                    obj.insert("text".to_string(), text.into_json());
                }
                if let Some(url) = url {
                    obj.insert("url".to_string(), url.into_json());
                }
                if let Some(file) = file {
                    obj.insert("file".to_string(), file.into_json());
                }
                if let Some(auto) = auto {
                    obj.insert("auto".to_string(), auto.into_json());
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

impl<'a> TypedActionBuilder<'a> {
    pub fn new() -> Self {
        Self {
            text: None,
            url: None,
            file: None,
            auto: None,
        }
    }

    /// Return the action object built.
    pub fn into_action(self) -> Action<'a> {
        Action::Typed {
            text: self.text,
            url: self.url,
            file: self.file,
            auto: self.auto,
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

impl<'a> IntoJson for Text<'a> {
    fn into_json(self) -> Value {
        let mut obj = serde_json::Map::new();
        if let Some(copy) = self.copy {
            obj.insert("copy".to_string(), json!(copy));
        }
        if let Some(largetype) = self.largetype {
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

    /// Return the text built.
    pub fn into_text(self) -> Text<'a> {
        self.text
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
    variables: HashMap<Cow<'a, str>, Cow<'a, str>>,
}

impl<'a> IntoJson for HashMap<ModifiersComb, ModifierData<'a>> {
    fn into_json(self) -> Value {
        let mut obj = serde_json::Map::with_capacity(self.len());
        for (key, value) in self.into_iter() {
            obj.insert(key.to_string(), value.into_json());
        }
        Value::Object(obj)
    }
}

impl<'a> IntoJson for Item<'a> {
    fn into_json(self) -> Value {
        let mut obj = serde_json::Map::new();
        obj.insert("title".to_string(), json!(self.title));
        if let Some(uid) = self.uid {
            obj.insert("uid".to_string(), json!(uid));
        }
        if let Some(subtitle) = self.subtitle {
            obj.insert("subtitle".to_string(), json!(subtitle));
        }
        if let Some(arg) = self.arg {
            obj.insert("arg".to_string(), arg.into_json());
        }
        if let Some(icon) = self.icon {
            obj.insert("icon".to_string(), icon.into_json());
        }
        if let Some(valid) = self.valid {
            obj.insert("valid".to_string(), json!(valid));
        }
        if let Some(match_) = self.match_ {
            obj.insert("match".to_string(), match_.into_json());
        }
        if let Some(autocomplete) = self.autocomplete {
            obj.insert("autocomplete".to_string(), json!(autocomplete));
        }
        if let Some(type_) = self.type_ {
            obj.insert("type".to_string(), type_.into_json());
        }
        if !self.mods.is_empty() {
            obj.insert("mods".to_string(), self.mods.into_json());
        }
        if let Some(action) = self.action {
            obj.insert("action".to_string(), action.into_json());
        }
        if let Some(text) = self.text {
            obj.insert("text".to_string(), text.into_json());
        }
        if let Some(quicklookurl) = self.quicklookurl {
            obj.insert("quicklookurl".to_string(), json!(quicklookurl));
        }
        if !self.variables.is_empty() {
            obj.insert("variables".to_string(), self.variables.into_json());
        }
        Value::Object(obj)
    }
}

/// Builder for an Item.
pub struct ItemBuilder<'a> {
    item: Item<'a>,
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

    /// Return the item built.
    pub fn into_item(self) -> Item<'a> {
        self.item
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

    pub fn set_variables(
        &mut self,
        variables: HashMap<Cow<'a, str>, Cow<'a, str>>,
    ) {
        self.item.variables.clear();
        self.item.variables.extend(variables);
    }

    pub fn variables(
        mut self,
        variables: HashMap<Cow<'a, str>, Cow<'a, str>>,
    ) -> Self {
        self.set_variables(variables);
        self
    }
}

pub struct ScriptFilterOutput<'a> {
    items: Vec<Item<'a>>,
    /// Item variables
    variables: HashMap<Cow<'a, str>, Cow<'a, str>>,
    /// Rerun script filters
    rerun: Option<f32>,
}

impl<'a> IntoJson for ScriptFilterOutput<'a> {
    fn into_json(self) -> Value {
        let mut obj = serde_json::Map::new();
        obj.insert(
            "items".to_string(),
            Value::Array(
                self.items.into_iter().map(IntoJson::into_json).collect(),
            ),
        );
        if !self.variables.is_empty() {
            obj.insert("variables".to_string(), self.variables.into_json());
        }
        if let Some(rerun) = self.rerun {
            obj.insert("rerun".to_string(), json!(rerun));
        }
        Value::Object(obj)
    }
}

/// Builder for `ScriptFilterOutput`.
pub struct ScriptFilterOutputBuilder<'a> {
    resp: ScriptFilterOutput<'a>,
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

    pub fn from_items<I: IntoIterator<Item = Item<'a>>>(items: I) -> Self {
        Self {
            resp: ScriptFilterOutput {
                items: items.into_iter().collect(),
                variables: HashMap::new(),
                rerun: None,
            },
        }
    }

    pub fn from_item(item: Item<'a>) -> Self {
        Self {
            resp: ScriptFilterOutput {
                items: vec![item],
                variables: HashMap::new(),
                rerun: None,
            },
        }
    }

    pub fn set_variables(
        &mut self,
        variables: HashMap<Cow<'a, str>, Cow<'a, str>>,
    ) {
        self.resp.variables.clear();
        self.resp.variables.extend(variables);
    }

    pub fn variables(
        mut self,
        variables: HashMap<Cow<'a, str>, Cow<'a, str>>,
    ) -> Self {
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

    /// Return the output built.
    pub fn into_output(self) -> ScriptFilterOutput<'a> {
        self.resp
    }
}
