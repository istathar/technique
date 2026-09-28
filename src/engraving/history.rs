//! The fold of a journal into the tree of activations it records. The walker,
//! the review cursor, and `log` all read a run through this.

use std::collections::HashMap;

use super::record::{InvokeTarget, Record, Serial, State, Supplied};

/// Where an activation stands after the fold.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Standing {
    /// Begun and not closed: in flight, or stopped mid-way.
    Open,
    Closed,
    /// A revoked activation enclosing nothing; the next walk re-activates it.
    Withdrawn,
    /// A revoked activation enclosing children, or an ancestor of any revoked
    /// one; the next walk continues it and closes it again.
    Reopened,
}

/// One effectful host call made within an activation.
#[derive(Debug, Clone, PartialEq)]
pub struct Effect {
    pub function: String,
    /// `None` until its `Return` is read; `Some(None)` for a bare `Return`.
    pub returned: Option<Option<crate::value::Value>>,
}

/// The current activation of one slot.
#[derive(Debug, Clone, PartialEq)]
pub struct Activation {
    pub serial: Serial,
    pub parent: Serial,
    pub path: String,
    pub edge: String,
    pub occurrence: usize,
    pub began: Vec<Supplied>,
    pub bound: Vec<Supplied>,
    /// `Done`, `Skip` or `Fail`.
    pub outcome: Option<State>,
    pub standing: Standing,
    pub effects: Vec<Effect>,
    pub invoked: Vec<InvokeTarget>,
    /// Current children, in the order their slots were first begun.
    pub children: Vec<Serial>,
    /// What this slot last bound and concluded before a `Revoke` or a
    /// superseding `Begin`, for seeding the prompts that ask it again.
    pub former_bound: Vec<Supplied>,
    pub former_outcome: Option<State>,
}

/// A journal folded. See `plans/rewrite/DESIGN.md` §1 for the rules.
#[derive(Debug)]
pub struct History {
    activations: HashMap<Serial, Activation>,
    slots: HashMap<(Serial, String, usize), Serial>,
    /// Children of the lifecycle root, i.e. the entry procedure's activation.
    roots: Vec<Serial>,
    highest: Serial,
    finished: bool,
}

impl History {
    pub fn new(records: &[Record]) -> History {
        let _ = records;
        todo!()
    }

    pub fn get(&self, serial: Serial) -> Option<&Activation> {
        self.activations
            .get(&serial)
    }

    /// The serial recorded for a slot, if any walk reached it.
    pub fn slot(&self, parent: Serial, edge: &str, occurrence: usize) -> Option<Serial> {
        self.slots
            .get(&(parent, edge.to_string(), occurrence))
            .copied()
    }

    pub fn roots(&self) -> &[Serial] {
        &self.roots
    }

    /// The next serial never yet written.
    pub fn next_serial(&self) -> Serial {
        Serial(
            self.highest
                .0
                + 1,
        )
    }

    /// Whether the last session to write ended with `Finish`.
    pub fn finished(&self) -> bool {
        self.finished
    }
}

/// A path relative to its parent's: the suffix when the parent's path is a
/// prefix, the whole path otherwise (a callee's lexical address).
pub fn edge<'a>(parent: &str, path: &'a str) -> &'a str {
    match path.strip_prefix(parent) {
        Some(rest) if !parent.is_empty() && rest.starts_with('/') => rest,
        _ => path,
    }
}

#[cfg(test)]
#[path = "checks/history.rs"]
mod check;
