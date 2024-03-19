//! Helpers for writing Alfred JSON config output.
//! 
//! Example:
//! 
//! ```
//! use alfred_json::scriptfilter::{ArgBuilder, IntoJson};
//! use alfred_json::jsonconfig::WorkflowBuilder;
//! let output = WorkflowBuilder::new()
//!     .arg(ArgBuilder::many(["hello", "world"]).into_arg())
//!     .into_workflow();
//! println!("{}", output.into_json());
//! ```

use crate::scriptfilter::{Arg, IntoJson};
use serde_json::Value;
use std::borrow::Cow;
use std::collections::HashMap;

/// The JSON config object.
pub struct Workflow<'a> {
    arg: Option<Arg<'a>>,
    variables: HashMap<Cow<'a, str>, Cow<'a, str>>,
}

impl<'a> IntoJson for Workflow<'a> {
    fn into_json(self) -> Value {
        let mut obj = serde_json::Map::new();
        if let Some(arg) = self.arg {
            obj.insert("arg".to_string(), arg.into_json());
        }
        if !self.variables.is_empty() {
            obj.insert("variables".to_string(), self.variables.into_json());
        }
        Value::Object(serde_json::Map::from_iter([(
            "alfredworkflow".to_string(),
            Value::Object(obj),
        )]))
    }
}

/// Builder for `Workflow`.
pub struct WorkflowBuilder<'a> {
    workflow: Workflow<'a>,
}

impl<'a> WorkflowBuilder<'a> {
    pub fn new() -> Self {
        Self {
            workflow: Workflow {
                arg: None,
                variables: HashMap::new(),
            },
        }
    }

    pub fn set_arg(&mut self, arg: Arg<'a>) {
        self.workflow.arg = Some(arg);
    }

    pub fn unset_arg(&mut self) {
        self.workflow.arg = None;
    }

    pub fn arg(mut self, arg: Arg<'a>) -> Self {
        self.set_arg(arg);
        self
    }

    pub fn set_variables(
        &mut self,
        variables: HashMap<Cow<'a, str>, Cow<'a, str>>,
    ) {
        self.workflow.variables.clear();
        self.workflow.variables.extend(variables);
    }

    pub fn variables(
        mut self,
        variables: HashMap<Cow<'a, str>, Cow<'a, str>>,
    ) -> Self {
        self.set_variables(variables);
        self
    }

    pub fn into_workflow(self) -> Workflow<'a> {
        self.workflow
    }
}
