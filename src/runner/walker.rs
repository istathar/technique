//! One walk of a program from the top against the History of its journal,
//! appending only what is new. See `plans/rewrite/DESIGN.md` §2.

use std::collections::HashMap;

use super::driver::{
    Answer, Driver, Event, Kind, Marker, Offer, Prompt, Question, Standing, Verdict,
};
use super::error::RunnerError;
use super::evaluator::{self, Environment};
use super::library::Nature;
use super::path::{PathSegment, QualifiedPath, render_path};
use super::session::{Reviewed, Runner};
use crate::engraving::{self, Activation, History, InvokeTarget, Serial, State, Supplied, edge};
use crate::formatting::{self, Identity};
use crate::language;
use crate::program::{
    Executable, ExecutableRef, Fragment, Invocable, Locale, Operation, Ordinal, Subroutine,
    SubroutineRef,
};
use crate::value::Value;

/// What a scope concluded.
#[derive(Debug, Clone, PartialEq)]
pub enum Outcome {
    Done(Value),
    /// Carries the body's value in memory; recorded bare.
    Skip(Value),
    Fail(String),
}

/// A change chosen in review, handed to the next walk.
#[derive(Debug, Clone, PartialEq)]
pub struct Amendment {
    pub serial: Serial,
    pub change: Change,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Change {
    Redo,
    Skip,
    Fail(String),
    Override,
    /// Ask an invocation's prompted arguments again.
    Reask,
}

/// Why a walk ended before its entry closed.
#[derive(Debug)]
pub(super) enum Halt {
    /// The `Stop` is already written.
    Stop,
    /// The `Revoke` is already written.
    Restart(Amendment),
    Error(RunnerError),
}

impl From<RunnerError> for Halt {
    fn from(error: RunnerError) -> Self {
        Halt::Error(error)
    }
}

/// What walking one operation yields. `Throwing` is a failed effect on its way
/// to the nearest scope that catches it.
enum Flow {
    Completed(Outcome),
    Throwing(String),
}

enum Reply {
    Done(Value),
    Skip,
    Fail(String),
    Override,
}

#[derive(Clone, Copy)]
enum Stance<'h> {
    Fresh,
    /// Begun again at the same serial: nothing recorded beneath it stands.
    Again,
    Restore(&'h Activation),
    Continue(&'h Activation),
}

enum Closing {
    Restored(Outcome),
    Given(Outcome),
    Ask,
}

struct Slot<'h> {
    serial: Serial,
    prior: Option<&'h Activation>,
    /// Whatever was recorded at this slot, standing or not.
    seed: Option<&'h Activation>,
}

struct Scope<'h> {
    serial: Serial,
    path: String,
    prior: Option<&'h Activation>,
    seed: Option<&'h Activation>,
    /// The recorded children still standing, which this walk may reach.
    children: &'h [Serial],
    /// `written` when the scope was entered.
    mark: usize,
    bound: Vec<Supplied>,
    effects: usize,
    invokes: usize,
    occurrences: HashMap<String, usize>,
    iterations: usize,
    reached: Vec<Serial>,
}

impl<'h> Scope<'h> {
    fn new(serial: Serial, path: &str, children: &'h [Serial], mark: usize) -> Self {
        Scope {
            serial,
            path: path.to_string(),
            prior: None,
            seed: None,
            children,
            mark,
            bound: Vec::new(),
            effects: 0,
            invokes: 0,
            occurrences: HashMap::new(),
            iterations: 0,
            reached: Vec::new(),
        }
    }
}

const CONFIRM: &[Offer] = &[Offer::Edit, Offer::Skip, Offer::Fail, Offer::Quit];
const OVERRULE: &[Offer] = &[
    Offer::Edit,
    Offer::Skip,
    Offer::Fail,
    Offer::Override,
    Offer::Quit,
];
const BOUNDARY: &[Offer] = &[Offer::Skip, Offer::Fail, Offer::Quit];

/// Walk the program once. `arguments` are the entry's when the journal has
/// not begun it.
pub(super) fn walk<'i, D: Driver>(
    runner: &mut Runner<'i, D>,
    history: &History,
    amendment: Option<Amendment>,
    arguments: &[Supplied],
) -> Result<Outcome, Halt> {
    let mut walker = Walker {
        next: history.next_serial(),
        scopes: vec![Scope::new(Serial::LIFECYCLE, "", history.roots(), 0)],
        runner,
        history,
        amendment,
        path: QualifiedPath::new(),
        written: 0,
        constraints: Vec::new(),
        asked: Vec::new(),
    };
    walker.run(arguments)
}

struct Walker<'i, 'h, 'r, D: Driver> {
    runner: &'r mut Runner<'i, D>,
    history: &'h History,
    amendment: Option<Amendment>,
    path: QualifiedPath<'i>,
    scopes: Vec<Scope<'h>>,
    next: Serial,
    written: usize,
    constraints: Vec<Value>,
    /// Invocations this walk passed whose arguments were prompted.
    asked: Vec<Serial>,
}

impl<'i, 'h, 'r, D: Driver> Walker<'i, 'h, 'r, D> {
    fn run(&mut self, arguments: &[Supplied]) -> Result<Outcome, Halt> {
        let program = self
            .runner
            .program;
        let entry = program
            .subroutines
            .first()
            .ok_or(RunnerError::MissingEntryProcedure)?;
        let name = entry
            .name
            .as_ref()
            .map(|n| n.value);
        if let Some(name) = name {
            self.path
                .push(PathSegment::Procedure(name));
        }
        let path = self
            .path
            .render();
        let slot = self.slot(&path);
        let inputs = match slot.prior {
            Some(a) => a
                .began
                .clone(),
            None => arguments.to_vec(),
        };
        let mut env = Environment::new();
        bind_supplied(&mut env, &inputs);
        let stance = stance(slot.prior, &inputs);
        if let Stance::Restore(a) = stance {
            return match self.restore(&mut env, a, Marker::Close)? {
                Flow::Completed(outcome) => Ok(outcome),
                Flow::Throwing(reason) => Ok(Outcome::Fail(reason)),
            };
        }
        let again = self.open(&slot, &path, inputs, stance)?;
        if name.is_some() {
            self.announce(entry, &path, &env);
        }
        let flow = self.perform(&mut env, &entry.body, again)?;
        self.seal(&mut env, &path, flow, kind_of_scope(&entry.body))
    }

    fn walk(&mut self, env: &mut Environment, op: &'i Operation<'i>) -> Result<Flow, Halt> {
        match op {
            Operation::Sequence(ops, _) => self.walk_sequence(env, ops),
            Operation::Prologue(ops, _) => self.walk_prologue(env, ops),
            Operation::Section {
                numeral,
                title,
                body,
                ..
            } => self.walk_section(env, numeral, title, body),
            Operation::Step { .. } => {
                unreachable!() // a Step is always walked as a Sequence member
            }
            Operation::Loop {
                names, over, body, ..
            } => self.walk_loop(env, names, over, body),
            Operation::Within { bound, body, .. } => {
                let budget = match self.value(env, bound)? {
                    Ok(value) => value,
                    Err(flow) => return Ok(flow),
                };
                self.constraints
                    .push(budget);
                let flow = self.walk(env, body)?;
                self.constraints
                    .pop();
                Ok(flow)
            }
            Operation::Cost(inner, _) => match self.value(env, inner)? {
                Ok(Value::Quanticle(numeric)) => Ok(done(Value::Intratempse(numeric))),
                Ok(_) => Err(RunnerError::InvalidCost.into()),
                Err(flow) => Ok(flow),
            },
            Operation::Invoke(invocable, _) => match &invocable.target {
                SubroutineRef::Resolved(id) => {
                    let program = self
                        .runner
                        .program;
                    self.walk_procedure(env, &program.subroutines[id.0], invocable)
                }
                SubroutineRef::Deferred(external) => {
                    self.walk_external(env, external.value, &invocable.arguments)
                }
                SubroutineRef::Unresolved(_) => {
                    unreachable!() // resolution resolves every procedure name
                }
            },
            Operation::Execute(executable, _) => self.walk_execute(env, executable),
            Operation::Bind {
                names,
                value,
                inferred,
                ..
            } => self.walk_bind(env, names, value, inferred.as_ref()),
            Operation::String(fragments, _) => match self.text(env, fragments)? {
                Ok(text) => Ok(done(Value::Literali(text))),
                Err(flow) => Ok(flow),
            },
            Operation::List(items, _) => match self.values(env, items)? {
                Ok(values) => Ok(done(Value::Arraeum(values))),
                Err(flow) => Ok(flow),
            },
            Operation::Tuple(items, _) => match self.values(env, items)? {
                Ok(values) => Ok(done(Value::Parametriq(values))),
                Err(flow) => Ok(flow),
            },
            Operation::Tablet(entries, _) => {
                let mut pairs = Vec::with_capacity(entries.len());
                for entry in entries {
                    let value = match self.value(env, &entry.value)? {
                        Ok(value) => value,
                        Err(flow) => return Ok(flow),
                    };
                    let label = match self.text(env, &entry.label)? {
                        Ok(label) => label,
                        Err(flow) => return Ok(flow),
                    };
                    pairs.push((label, value));
                }
                Ok(done(Value::Tabularum(pairs)))
            }
            Operation::Variable(_, _)
            | Operation::Number(_, _)
            | Operation::Response(_, _)
            | Operation::Verbatim(_, _)
            | Operation::Prose(_, _)
            | Operation::Hole(_)
            | Operation::Unit(_) => {
                let value = evaluator::evaluate(
                    &self
                        .runner
                        .library,
                    &self
                        .runner
                        .context,
                    env,
                    op,
                )?;
                Ok(done(value))
            }
        }
    }

    // Walk an operation for its value; anything other than Done is handed
    // back to propagate, a Skip carrying no value.
    fn value(
        &mut self,
        env: &mut Environment,
        op: &'i Operation<'i>,
    ) -> Result<Result<Value, Flow>, Halt> {
        Ok(match self.walk(env, op)? {
            Flow::Completed(Outcome::Done(value)) => Ok(value),
            Flow::Completed(Outcome::Skip(_)) => Err(Flow::Completed(Outcome::Skip(Value::Unitus))),
            other => Err(other),
        })
    }

    fn values(
        &mut self,
        env: &mut Environment,
        ops: &'i [Operation<'i>],
    ) -> Result<Result<Vec<Value>, Flow>, Halt> {
        let mut values = Vec::with_capacity(ops.len());
        for op in ops {
            match self.value(env, op)? {
                Ok(value) => values.push(value),
                Err(flow) => return Ok(Err(flow)),
            }
        }
        Ok(Ok(values))
    }

    fn text(
        &mut self,
        env: &mut Environment,
        fragments: &'i [Fragment<'i>],
    ) -> Result<Result<String, Flow>, Halt> {
        let mut text = String::new();
        for fragment in fragments {
            match fragment {
                Fragment::Text(t) => text.push_str(t),
                Fragment::Escaped(c) => text.push(*c),
                Fragment::Interpolation(inner) => match self.value(env, inner)? {
                    Ok(Value::Literali(s)) => text.push_str(&s),
                    Ok(other) => text.push_str(&other.to_string()),
                    Err(flow) => return Ok(Err(flow)),
                },
            }
        }
        Ok(Ok(text))
    }

    fn walk_sequence(
        &mut self,
        env: &mut Environment,
        ops: &'i [Operation<'i>],
    ) -> Result<Flow, Halt> {
        let mut parallel = 0;
        let mut rollup = Rollup::new();
        for op in ops {
            let flow = match op {
                Operation::Step { ordinal, .. } => {
                    if let Ordinal::Parallel = ordinal {
                        parallel += 1;
                    }
                    self.walk_step(env, op, parallel)?
                }
                _ => self.walk(env, op)?,
            };
            // Prose contributes its value but no verdict.
            if let Operation::Prose(_, _) = op {
                if let Flow::Completed(Outcome::Done(value)) = flow {
                    rollup.observe(value);
                }
                continue;
            }
            match flow {
                Flow::Completed(outcome) => rollup.absorb(outcome),
                throwing => return Ok(throwing),
            }
        }
        Ok(Flow::Completed(rollup.settle()))
    }

    fn walk_step(
        &mut self,
        env: &mut Environment,
        op: &'i Operation<'i>,
        parallel: usize,
    ) -> Result<Flow, Halt> {
        let Operation::Step {
            ordinal,
            attributes,
            ..
        } = op
        else {
            unreachable!() // walk_sequence passes only Steps
        };
        let frames: Vec<&'i [language::Attribute<'i>]> = attributes
            .iter()
            .copied()
            .filter(|frame| {
                !self
                    .path
                    .holds(frame)
            })
            .collect();
        for frame in &frames {
            self.path
                .push(PathSegment::Attributes(frame));
        }
        self.path
            .push(match ordinal {
                Ordinal::Dependent(s) => PathSegment::DependentStep(s),
                Ordinal::Parallel => PathSegment::ParallelStep(parallel),
            });
        let flow = self.perform_step(env, op)?;
        self.path
            .pop();
        for _ in &frames {
            self.path
                .pop();
        }
        Ok(flow)
    }

    fn perform_step(&mut self, env: &mut Environment, op: &'i Operation<'i>) -> Result<Flow, Halt> {
        let Operation::Step {
            source,
            body,
            responses,
            ..
        } = op
        else {
            unreachable!() // walk_step passes only Steps
        };
        let path = self
            .path
            .render();
        let reads = read_values(body, env);
        let slot = self.slot(&path);
        let stance = stance(slot.prior, &reads);
        if let Stance::Restore(a) = stance {
            return self.restore(env, a, Marker::Step);
        }
        let again = self.open(&slot, &path, reads, stance)?;
        self.display_step(env, source, &path);

        // A descriptive binding with responses takes its value from the choice.
        let chooses = !responses.is_empty() && binds_descriptively(body);
        let flow = if chooses {
            done(Value::Unitus)
        } else {
            self.perform(env, body, again)?
        };
        let acquired = responses.is_empty() && binds_descriptively(body);
        let choices: Vec<&str> = responses
            .iter()
            .map(|r| r.value)
            .collect();
        let kind = kind_of_step(
            &self
                .runner
                .library,
            op,
        );
        let rollup = outcome_of(&flow);
        let (outcome, restored) = self.resolve(env, &rollup, |walker| match flow {
            Flow::Completed(Outcome::Done(produced)) if !acquired => {
                let reply = walker.ask(
                    Marker::Step,
                    &path,
                    Prompt::Confirm {
                        standing: Standing::Done,
                        kind,
                        produced: &produced,
                        choices: &choices,
                    },
                    CONFIRM,
                )?;
                Ok(answered(reply, produced))
            }
            Flow::Completed(Outcome::Fail(_)) => {
                let reply = walker.ask(
                    Marker::Step,
                    &path,
                    Prompt::Confirm {
                        standing: Standing::Fail,
                        kind: Kind::Prose,
                        produced: &Value::Unitus,
                        choices: &[],
                    },
                    OVERRULE,
                )?;
                Ok(answered(reply, Value::Unitus))
            }
            // The body answered for itself: an acquire, a declined gate, a
            // failed command.
            _ => Ok(rollup.clone()),
        })?;
        if chooses && !restored {
            if let Some(names) = binding_names(body) {
                let chosen = match &outcome {
                    Outcome::Done(value) => Some(value.clone()),
                    Outcome::Skip(_) => Some(Value::Unitus),
                    Outcome::Fail(_) => None,
                };
                if let Some(value) = chosen {
                    evaluator::bind_names(env, names, value)?;
                    for name in names {
                        self.note(env, name.value);
                    }
                }
            }
        }
        self.finish(env, Marker::Step, &path, &outcome, restored)?;
        Ok(Flow::Completed(outcome))
    }

    fn walk_prologue(
        &mut self,
        env: &mut Environment,
        ops: &'i [Operation<'i>],
    ) -> Result<Flow, Halt> {
        self.path
            .push(PathSegment::Prologue);
        let path = self
            .path
            .render();
        let slot = self.slot(&path);
        let stance = stance(slot.prior, &[]);
        let flow = match stance {
            Stance::Restore(a) => unwind(self.restore_quietly(env, a), a),
            _ => {
                let again = self.open(&slot, &path, Vec::new(), stance)?;
                let flow = if again && self.pending() {
                    done(Value::Unitus)
                } else {
                    self.walk_sequence(env, ops)?
                };
                let rollup = outcome_of(&flow);
                let (outcome, restored) = self.resolve(env, &rollup, |_| Ok(rollup.clone()))?;
                self.record(env, &path, &outcome, restored)?;
                rethrow(flow, outcome)
            }
        };
        self.path
            .pop();
        Ok(flow)
    }

    fn walk_section(
        &mut self,
        env: &mut Environment,
        numeral: &'i str,
        title: &'i Option<Box<Operation<'i>>>,
        body: &'i Operation<'i>,
    ) -> Result<Flow, Halt> {
        self.path
            .push(PathSegment::Section(numeral));
        let path = self
            .path
            .render();
        let slot = self.slot(&path);
        let stance = stance(slot.prior, &[]);
        let flow = match stance {
            Stance::Restore(a) => self.restore(env, a, Marker::Close)?,
            _ => {
                let again = self.open(&slot, &path, Vec::new(), stance)?;
                let heading = match title {
                    Some(title) => match self.value(env, title)? {
                        Ok(Value::Literali(text)) => text,
                        Ok(other) => other.to_string(),
                        Err(_) => String::new(),
                    },
                    None => String::new(),
                };
                self.runner
                    .driver
                    .show(Event::Section {
                        path: &path,
                        numeral,
                        title: &heading,
                    });
                let flow = self.perform(env, body, again)?;
                let outcome = self.seal(env, &path, flow, kind_of_scope(body))?;
                Flow::Completed(outcome)
            }
        };
        self.path
            .pop();
        Ok(flow)
    }

    fn walk_loop(
        &mut self,
        env: &mut Environment,
        names: &'i [language::Identifier<'i>],
        over: &'i Option<Box<Operation<'i>>>,
        body: &'i Operation<'i>,
    ) -> Result<Flow, Halt> {
        let Some(over) = over else {
            loop {
                let number = self.number();
                self.walk_iteration(env, names, number, body)?;
            }
        };
        // Resolution guarantees the name is in scope, not that it holds a value.
        if let Operation::Variable(id, _) = over.as_ref() {
            if env
                .lookup(id.value)
                .is_none()
            {
                return Ok(done(Value::Unitus));
            }
        }
        let items = match self.value(env, over)? {
            Ok(value) => evaluator::coerce_to_list(value)?,
            Err(flow) => return Ok(flow),
        };
        let mut rollup = Rollup::new();
        for item in items {
            evaluator::bind_names(env, names, item)?;
            let number = self.number();
            match self.walk_iteration(env, names, number, body)? {
                Flow::Completed(outcome) => rollup.absorb(outcome),
                throwing => return Ok(throwing),
            }
        }
        // A loop yields unit, keeping only its verdict.
        Ok(Flow::Completed(match rollup.settle() {
            Outcome::Done(_) => Outcome::Done(Value::Unitus),
            Outcome::Skip(_) => Outcome::Skip(Value::Unitus),
            failed => failed,
        }))
    }

    // Sibling loops in one scope share numbering.
    fn number(&mut self) -> usize {
        let scope = self.top();
        scope.iterations += 1;
        scope.iterations
    }

    fn walk_iteration(
        &mut self,
        env: &mut Environment,
        names: &'i [language::Identifier<'i>],
        number: usize,
        body: &'i Operation<'i>,
    ) -> Result<Flow, Halt> {
        self.path
            .push(PathSegment::Iteration(number));
        let path = self
            .path
            .render();
        let inputs = iteration_values(names, env);
        let slot = self.slot(&path);
        let stance = stance(slot.prior, &inputs);
        let flow = match stance {
            Stance::Restore(a) => unwind(self.restore(env, a, Marker::Close)?, a),
            _ => {
                let again = self.open(&slot, &path, inputs, stance)?;
                let echo = render_iteration_echo(names, env);
                self.runner
                    .driver
                    .show(Event::Enter {
                        path: &path,
                        echo: &echo,
                    });
                let flow = self.perform(env, body, again)?;
                let rollup = outcome_of(&flow);
                let (outcome, restored) = self.resolve(env, &rollup, |_| Ok(rollup.clone()))?;
                self.finish(env, Marker::Close, &path, &outcome, restored)?;
                rethrow(flow, outcome)
            }
        };
        self.path
            .pop();
        Ok(flow)
    }

    fn walk_procedure(
        &mut self,
        env: &mut Environment,
        subroutine: &'i Subroutine<'i>,
        invocable: &'i Invocable<'i>,
    ) -> Result<Flow, Halt> {
        let Some(name) = subroutine
            .name
            .as_ref()
            .map(|n| n.value)
        else {
            unreachable!() // only the entry is anonymous
        };
        let caller = self
            .path
            .render();
        let arguments = &invocable.arguments;
        let count = if invocable.elided {
            subroutine.arity()
        } else {
            arguments.len()
        };
        let mut given: Vec<Option<Value>> = Vec::with_capacity(count);
        for i in 0..count {
            let prompted = invocable.elided || is_hole(&arguments[i]);
            if prompted {
                given.push(None);
            } else {
                match self.value(env, &arguments[i])? {
                    Ok(value) => given.push(Some(value)),
                    Err(flow) => return Ok(flow),
                }
            }
        }

        let segments: Vec<PathSegment<'i>> = subroutine
            .locale
            .iter()
            .map(|locale| match *locale {
                Locale::Procedure(n) => PathSegment::Procedure(n),
                Locale::Section(n) => PathSegment::Section(n),
            })
            .collect();
        let lexical = render_path(&segments);
        let slot = self.slot(&lexical);
        let reask = self.reasking(slot.serial);
        // A call declined at an argument prompt stands as declined.
        if let Some(a) = slot.prior {
            if !reask
                && a.standing == engraving::Standing::Closed
                && a.children
                    .is_empty()
                && a.began
                    .len()
                    < count
            {
                self.invoke(&caller, InvokeTarget::Procedure(name.to_string()))?;
                return self.restore(&mut Environment::new(), a, Marker::Close);
            }
        }
        let recorded = match slot.prior {
            Some(a) if !reask && a.standing != engraving::Standing::Withdrawn => Some(&a.began),
            _ => None,
        };
        self.invoke(&caller, InvokeTarget::Procedure(name.to_string()))?;

        let formae = render_parameter_formae(subroutine.signature);
        let label = format!("<{}>", name);
        let mut supplied: Vec<Supplied> = Vec::with_capacity(count);
        let mut asked = false;
        for (i, value) in given
            .into_iter()
            .enumerate()
        {
            let bind = subroutine
                .parameters
                .get(i)
                .cloned()
                .flatten();
            let value = match value {
                Some(value) => value,
                None => {
                    asked = true;
                    match recorded.and_then(|began| began.get(i)) {
                        Some(item) => item
                            .value
                            .clone(),
                        None => {
                            let seed = slot
                                .seed
                                .and_then(|a| {
                                    a.began
                                        .get(i)
                                })
                                .map(|item| &item.value);
                            let forma = formae
                                .get(i)
                                .map(|f| f.as_str());
                            let named = match &bind {
                                Some(bind) => Some(bind.as_str()),
                                None => None,
                            };
                            match self.acquire(&caller, &label, named, forma, seed)? {
                                Reply::Done(value) => value,
                                Reply::Override => Value::Unitus,
                                Reply::Skip => {
                                    return self.abandon(
                                        &slot,
                                        &lexical,
                                        supplied,
                                        Outcome::Skip(Value::Unitus),
                                    );
                                }
                                Reply::Fail(reason) => {
                                    return self.abandon(
                                        &slot,
                                        &lexical,
                                        supplied,
                                        Outcome::Fail(reason),
                                    );
                                }
                            }
                        }
                    }
                }
            };
            supplied.push(Supplied { value, name: bind });
        }
        if asked {
            self.asked
                .push(slot.serial);
        }

        // The callee sees only its parameters.
        let mut local = Environment::new();
        bind_supplied(&mut local, &supplied);
        let stance = stance(slot.prior, &supplied);
        if let Stance::Restore(a) = stance {
            return self.restore(&mut local, a, Marker::Close);
        }
        let again = self.open(&slot, &lexical, supplied, stance)?;
        let saved = self
            .path
            .replace(segments);
        self.announce(subroutine, &lexical, &local);
        let flow = self.perform(&mut local, &subroutine.body, again)?;
        let outcome = self.seal(&mut local, &lexical, flow, kind_of_scope(&subroutine.body))?;
        self.path
            .replace(saved);
        Ok(Flow::Completed(outcome))
    }

    // An invocation declined at an argument prompt closes at the callee's path.
    fn abandon(
        &mut self,
        slot: &Slot<'h>,
        path: &str,
        supplied: Vec<Supplied>,
        outcome: Outcome,
    ) -> Result<Flow, Halt> {
        self.write(slot.serial, path, State::Begin(supplied))?;
        self.write(slot.serial, path, state_of(&outcome))?;
        Ok(Flow::Completed(outcome))
    }

    fn walk_external(
        &mut self,
        env: &mut Environment,
        uri: &'i str,
        arguments: &'i [Operation<'i>],
    ) -> Result<Flow, Halt> {
        let caller = self
            .path
            .render();
        self.path
            .push(PathSegment::External(uri));
        let path = self
            .path
            .render();
        let slot = self.slot(&path);
        self.invoke(&caller, InvokeTarget::Uri(uri.to_string()))?;
        let stance = stance(slot.prior, &[]);
        let flow = match stance {
            Stance::Restore(a) => self.restore(env, a, Marker::Return)?,
            _ => {
                self.open(&slot, &path, Vec::new(), stance)?;
                let echo = match self.echo(env, arguments)? {
                    Ok(echo) => echo,
                    Err(flow) => return Ok(flow),
                };
                let (outcome, restored) =
                    self.resolve(env, &Outcome::Done(Value::Unitus), |walker| {
                        match walker.ask(
                            Marker::Depart,
                            &path,
                            Prompt::Depart { echo: &echo },
                            BOUNDARY,
                        )? {
                            Reply::Skip => return Ok(Outcome::Skip(Value::Unitus)),
                            Reply::Fail(reason) => return Ok(Outcome::Fail(reason)),
                            Reply::Done(_) | Reply::Override => {}
                        }
                        walker
                            .runner
                            .driver
                            .show(Event::Depart {
                                path: &path,
                                echo: &echo,
                            });
                        let reply =
                            walker.ask(Marker::Return, &path, Prompt::External, BOUNDARY)?;
                        Ok(answered(reply, Value::Unitus))
                    })?;
                self.finish(env, Marker::Return, &path, &outcome, restored)?;
                Flow::Completed(outcome)
            }
        };
        self.path
            .pop();
        Ok(flow)
    }

    // A deferred external's arguments, `value ~ name` where a variable.
    fn echo(
        &mut self,
        env: &mut Environment,
        arguments: &'i [Operation<'i>],
    ) -> Result<Result<String, Flow>, Halt> {
        if arguments.is_empty() {
            return Ok(Ok(String::new()));
        }
        let mut parts = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let value = match self.value(env, argument)? {
                Ok(value) => value,
                Err(flow) => return Ok(Err(flow)),
            };
            parts.push(match argument {
                Operation::Variable(id, _) => format!("{} ~ {}", value, id.value),
                _ => value.to_string(),
            });
        }
        Ok(Ok(format!("({})", parts.join(", "))))
    }

    fn walk_execute(
        &mut self,
        env: &mut Environment,
        executable: &'i Executable<'i>,
    ) -> Result<Flow, Halt> {
        let values = match self.values(env, &executable.arguments)? {
            Ok(values) => values,
            Err(flow) => return Ok(flow),
        };
        let id = match &executable.target {
            ExecutableRef::Resolved(id) => *id,
            ExecutableRef::Unresolved(target) => {
                return Err(RunnerError::UnknownFunction(
                    target
                        .value
                        .to_string(),
                )
                .into());
            }
        };
        let function = self
            .runner
            .library
            .name(id);
        let described = format!("{}()", function);
        let nature = self
            .runner
            .library
            .nature(id);
        if let Nature::Pure = nature {
            self.runner
                .driver
                .show(Event::Announce(&described));
            return Ok(done(self.call(id, env, &values)?));
        }

        let scope = self.top();
        let k = scope.effects;
        scope.effects += 1;
        let serial = scope.serial;
        let prior = scope.prior;
        // A throw is its activation's last effect, after every child it reached.
        let last = match prior {
            Some(a) => {
                k + 1
                    == a.effects
                        .len()
                    && a.children
                        .iter()
                        .all(|c| {
                            scope
                                .reached
                                .contains(c)
                        })
            }
            None => false,
        };
        let recorded = prior.and_then(|a| {
            a.effects
                .get(k)
        });
        // A continued activation reuses the k-th recorded Return.
        if let Some(effect) = recorded {
            if let Some(returned) = &effect.returned {
                self.runner
                    .driver
                    .show(Event::Announce(&described));
                return Ok(match (returned, prior.and_then(thrown)) {
                    (Some(value), _) => done(value.clone()),
                    (None, Some(reason)) if last => Flow::Throwing(reason),
                    (None, _) => Flow::Completed(Outcome::Skip(Value::Unitus)),
                });
            }
        }
        let path = self
            .path
            .render();
        if recorded.is_none() {
            self.write(
                serial,
                &path,
                State::Execute {
                    function: function.to_string(),
                },
            )?;
        }
        let flow = match nature {
            Nature::Command => {
                let script = match values.first() {
                    Some(Value::Literali(text)) => text.clone(),
                    Some(other) => other.to_string(),
                    None => String::new(),
                };
                match self.ask(
                    Marker::Step,
                    &path,
                    Prompt::Command { script: &script },
                    BOUNDARY,
                )? {
                    Reply::Done(chosen) => self.command(env, id, &path, chosen)?,
                    Reply::Override => self.command(env, id, &path, Value::Literali(script))?,
                    Reply::Skip => Flow::Completed(Outcome::Skip(Value::Unitus)),
                    Reply::Fail(reason) => Flow::Throwing(reason),
                }
            }
            Nature::Action => {
                let verb = self
                    .runner
                    .library
                    .display(id)
                    .unwrap_or(function);
                let shown = match values.first() {
                    Some(value) => value.clone(),
                    None => Value::Unitus,
                };
                match self.ask(
                    Marker::Action,
                    &path,
                    Prompt::Action {
                        function,
                        verb,
                        value: &shown,
                    },
                    BOUNDARY,
                )? {
                    Reply::Done(_) | Reply::Override => {
                        self.runner
                            .driver
                            .show(Event::Action {
                                path: &path,
                                function,
                            });
                        done(self.call(id, env, &values)?)
                    }
                    Reply::Skip => Flow::Completed(Outcome::Skip(Value::Unitus)),
                    Reply::Fail(reason) => Flow::Throwing(reason),
                }
            }
            Nature::Instant => done(self.call(id, env, &values)?),
            Nature::Pure => unreachable!(), // announced and returned above
        };
        let returned = match &flow {
            Flow::Completed(Outcome::Done(value)) => Some(value.clone()),
            _ => None,
        };
        self.write(serial, &path, State::Return(returned))?;
        Ok(flow)
    }

    // Run a gated command with the script the user chose, and only that.
    fn command(
        &mut self,
        env: &Environment,
        id: crate::program::ExecutableId,
        path: &str,
        chosen: Value,
    ) -> Result<Flow, Halt> {
        let script = match &chosen {
            Value::Literali(text) => text.clone(),
            other => other.to_string(),
        };
        self.runner
            .driver
            .show(Event::Command {
                path,
                script: &script,
            });
        match self.call(id, env, &[chosen]) {
            Ok(value) => Ok(done(value)),
            Err(RunnerError::CommandFailed(code)) => Ok(Flow::Throwing(format!(
                "External command exited with status {}",
                code
            ))),
            Err(error) => Err(error.into()),
        }
    }

    fn call(
        &self,
        id: crate::program::ExecutableId,
        env: &Environment,
        values: &[Value],
    ) -> Result<Value, RunnerError> {
        self.runner
            .library
            .call(
                id,
                &self
                    .runner
                    .context,
                env,
                values,
            )
    }

    fn walk_bind(
        &mut self,
        env: &mut Environment,
        names: &'i [language::Identifier<'i>],
        value: &'i Operation<'i>,
        inferred: Option<&'i language::Genus<'i>>,
    ) -> Result<Flow, Halt> {
        if !is_empty_sequence(value) {
            return match self.walk(env, value)? {
                Flow::Completed(Outcome::Done(value)) => {
                    evaluator::bind_names(env, names, value)?;
                    for name in names {
                        self.note(env, name.value);
                    }
                    Ok(done(Value::Unitus))
                }
                Flow::Completed(Outcome::Skip(_)) => {
                    self.unbind(env, names);
                    Ok(Flow::Completed(Outcome::Skip(Value::Unitus)))
                }
                other => Ok(other),
            };
        }

        // Descriptive: each name is acquired from the user, unless the scope
        // being continued bound it already.
        let path = self
            .path
            .render();
        let forma = inferred.map(|genus| formatting::render_genus(genus, &Identity));
        let scope = self.top();
        let prior = scope.prior;
        let seed = scope.seed;
        let mut acquired = Vec::with_capacity(names.len());
        for name in names {
            let value = match prior
                .and_then(concluded)
                .and_then(|(_, bound)| lookup(bound, name.value))
            {
                Some(value) => value.clone(),
                None => {
                    let seed = seed.and_then(|a| lookup(kept(a), name.value));
                    let forma = match &forma {
                        Some(text) => Some(text.as_str()),
                        None => None,
                    };
                    match self.acquire(&path, "", Some(name.value), forma, seed)? {
                        Reply::Done(value) => value,
                        Reply::Override => Value::Unitus,
                        Reply::Skip => {
                            self.unbind(env, names);
                            return Ok(Flow::Completed(Outcome::Skip(Value::Unitus)));
                        }
                        Reply::Fail(reason) => return Ok(Flow::Completed(Outcome::Fail(reason))),
                    }
                }
            };
            acquired.push(value);
        }
        for (name, value) in names
            .iter()
            .zip(acquired)
        {
            env.extend(
                name.value
                    .to_string(),
                value,
            );
            self.note(env, name.value);
        }
        Ok(done(Value::Unitus))
    }

    // A skipped binding binds each name to unit, and records that it did.
    fn unbind(&mut self, env: &mut Environment, names: &[language::Identifier<'_>]) {
        for name in names {
            env.extend(
                name.value
                    .to_string(),
                Value::Unitus,
            );
            self.note(env, name.value);
        }
    }

    fn note(&mut self, env: &Environment, name: &str) {
        let value = match env.lookup(name) {
            Some(value) => value.clone(),
            None => Value::Unitus,
        };
        let bound = &mut self
            .top()
            .bound;
        bound.retain(|item| match &item.name {
            Some(bound) => bound != name,
            None => true,
        });
        bound.push(Supplied {
            value,
            name: Some(name.to_string()),
        });
    }

    // Walk a scope's body, unless it was begun again only to take a verdict
    // chosen in review; a Skip then binds as a live one does.
    fn perform(
        &mut self,
        env: &mut Environment,
        body: &'i Operation<'i>,
        again: bool,
    ) -> Result<Flow, Halt> {
        if again && self.pending() {
            if let Some(Amendment {
                change: Change::Skip,
                ..
            }) = &self.amendment
            {
                let mut names = Vec::new();
                bindings(body, &mut names);
                for name in names {
                    self.unbind(env, std::slice::from_ref(name));
                }
            }
            return Ok(done(Value::Unitus));
        }
        self.walk(env, body)
    }

    // A structural scope's close: the entry, a section, an invoked procedure.
    fn seal(
        &mut self,
        env: &mut Environment,
        path: &str,
        flow: Flow,
        kind: Kind,
    ) -> Result<Outcome, Halt> {
        let rollup = outcome_of(&flow);
        let (outcome, restored) = self.resolve(env, &rollup, |walker| {
            let (standing, produced, offers) = match &rollup {
                Outcome::Fail(_) => (Standing::Fail, Value::Unitus, OVERRULE),
                Outcome::Skip(_) => (Standing::Skip, Value::Unitus, CONFIRM),
                Outcome::Done(value) => (Standing::Done, value.clone(), CONFIRM),
            };
            let reply = walker.ask(
                Marker::Close,
                path,
                Prompt::Confirm {
                    standing,
                    kind,
                    produced: &produced,
                    choices: &[],
                },
                offers,
            )?;
            Ok(answered(reply, produced))
        })?;
        self.finish(env, Marker::Close, path, &outcome, restored)?;
        Ok(outcome)
    }

    // Decide how the innermost scope closes, asking through `ordinary` only
    // where §2 says the ordinary close logic applies.
    fn resolve(
        &mut self,
        env: &mut Environment,
        rollup: &Outcome,
        ordinary: impl FnOnce(&mut Self) -> Result<Outcome, Halt>,
    ) -> Result<(Outcome, bool), Halt> {
        match self.conclude(rollup)? {
            Closing::Restored(outcome) => {
                if let Some(a) = self
                    .top()
                    .prior
                {
                    bind_supplied(env, &a.bound);
                }
                Ok((outcome, true))
            }
            Closing::Given(outcome) => Ok((outcome, false)),
            Closing::Ask => Ok((ordinary(self)?, false)),
        }
    }

    fn conclude(&mut self, rollup: &Outcome) -> Result<Closing, Halt> {
        let history = self.history;
        let scope = self.top();
        let serial = scope.serial;
        let prior = scope.prior;
        let mark = scope.mark;
        if let Some(a) = prior {
            let unreached: Vec<&Activation> = a
                .children
                .iter()
                .filter(|child| {
                    !scope
                        .reached
                        .contains(child)
                })
                .filter_map(|child| history.get(*child))
                .filter(|child| child.standing != engraving::Standing::Withdrawn)
                .collect();
            for child in unreached {
                self.write(child.serial, &child.path, State::Revoke)?;
            }
        }
        if let Some(outcome) = self.verdict(serial) {
            return Ok(Closing::Given(outcome));
        }
        let Some(a) = prior else {
            return Ok(Closing::Ask);
        };
        if self.written == mark && a.standing == engraving::Standing::Closed {
            return Ok(Closing::Restored(recorded(a)));
        }
        if a.revoked {
            return Ok(Closing::Ask);
        }
        match concluded(a) {
            Some((state, _)) if rank_of_state(state) == rank(rollup) => {
                Ok(Closing::Given(rollup.clone()))
            }
            _ => Ok(Closing::Ask),
        }
    }

    fn finish(
        &mut self,
        env: &mut Environment,
        marker: Marker,
        path: &str,
        outcome: &Outcome,
        restored: bool,
    ) -> Result<(), Halt> {
        self.record(env, path, outcome, restored)?;
        self.show_verdict(marker, path, outcome, restored);
        Ok(())
    }

    // Close the innermost scope, writing its `Bind` and outcome unless its
    // recorded ones were restored.
    fn record(
        &mut self,
        env: &mut Environment,
        path: &str,
        outcome: &Outcome,
        restored: bool,
    ) -> Result<(), Halt> {
        let Some(scope) = self
            .scopes
            .pop()
        else {
            unreachable!() // the root scope is never closed
        };
        if restored {
            return Ok(());
        }
        let mut bound = scope.bound;
        // A continued scope keeps what it bound through a prompt not asked again.
        if bound.is_empty() {
            if let Some((_, before)) = scope
                .prior
                .and_then(concluded)
            {
                bound = before.to_vec();
                bind_supplied(env, &bound);
            }
        }
        if !bound.is_empty() {
            self.write(scope.serial, path, State::Bind(bound))?;
        }
        self.write(scope.serial, path, state_of(outcome))
    }

    // A leaf whose recorded outcome stands: bind what it bound, yield what it
    // concluded.
    fn restore(
        &mut self,
        env: &mut Environment,
        a: &'h Activation,
        marker: Marker,
    ) -> Result<Flow, Halt> {
        let flow = self.restore_quietly(env, a);
        let outcome = recorded(a);
        self.show_verdict(marker, &a.path, &outcome, true);
        Ok(flow)
    }

    fn restore_quietly(&mut self, env: &mut Environment, a: &'h Activation) -> Flow {
        bind_supplied(env, &a.bound);
        Flow::Completed(recorded(a))
    }

    // Take the next slot beneath the innermost scope.
    fn slot(&mut self, path: &str) -> Slot<'h> {
        let history = self.history;
        let n = self
            .scopes
            .len()
            - 1;
        let scope = &mut self.scopes[n];
        let edge = edge(&scope.path, path).to_string();
        let count = scope
            .occurrences
            .entry(edge.clone())
            .or_insert(0);
        let occurrence = *count;
        *count += 1;
        let found = history.slot(scope.serial, &edge, occurrence);
        let serial = match found {
            Some(serial) => serial,
            None => {
                let serial = self.next;
                self.next = Serial(serial.0 + 1);
                serial
            }
        };
        scope
            .reached
            .push(serial);
        let prior = found
            .filter(|s| {
                scope
                    .children
                    .contains(s)
            })
            .and_then(|s| history.get(s));
        let seed = found.and_then(|s| {
            history
                .get(s)
                .or_else(|| history.retired(s))
        });
        Slot {
            serial,
            prior,
            seed,
        }
    }

    // Enter a slot that is not restored, answering whether it was begun again.
    fn open(
        &mut self,
        slot: &Slot<'h>,
        path: &str,
        inputs: Vec<Supplied>,
        stance: Stance<'h>,
    ) -> Result<bool, Halt> {
        let (prior, children, again): (Option<&'h Activation>, &'h [Serial], bool) = match stance {
            Stance::Continue(a) => (Some(a), &a.children, false),
            Stance::Fresh => (None, &[], false),
            Stance::Again => (None, &[], true),
            Stance::Restore(_) => unreachable!(), // restored slots are not entered
        };
        if prior.is_none() {
            self.write(slot.serial, path, State::Begin(inputs))?;
        }
        let mut scope = Scope::new(slot.serial, path, children, self.written);
        scope.prior = prior;
        scope.seed = slot.seed;
        self.scopes
            .push(scope);
        Ok(again)
    }

    // An `Invoke` is written once per activation; a continued one has it.
    fn invoke(&mut self, path: &str, target: InvokeTarget) -> Result<(), Halt> {
        let scope = self.top();
        let k = scope.invokes;
        scope.invokes += 1;
        let serial = scope.serial;
        if let Some(a) = scope.prior {
            if a.invoked
                .len()
                > k
            {
                return Ok(());
            }
        }
        self.write(serial, path, State::Invoke(target))
    }

    // Whether the innermost scope has a verdict waiting from review.
    fn pending(&self) -> bool {
        let serial = self.scopes[self
            .scopes
            .len()
            - 1]
        .serial;
        match &self.amendment {
            Some(Amendment {
                serial: at,
                change: Change::Skip | Change::Fail(_) | Change::Override,
            }) => *at == serial,
            _ => false,
        }
    }

    // Take the verdict chosen in review for this serial, if one waits.
    fn verdict(&mut self, serial: Serial) -> Option<Outcome> {
        let outcome = match &self.amendment {
            Some(Amendment { serial: at, change }) if *at == serial => match change {
                Change::Skip => Outcome::Skip(Value::Unitus),
                Change::Fail(reason) => Outcome::Fail(reason.clone()),
                Change::Override => Outcome::Done(Value::Unitus),
                Change::Redo | Change::Reask => return None,
            },
            _ => return None,
        };
        self.amendment = None;
        Some(outcome)
    }

    fn reasking(&mut self, serial: Serial) -> bool {
        if let Some(Amendment {
            serial: at,
            change: Change::Reask,
        }) = &self.amendment
        {
            if *at == serial {
                self.amendment = None;
                return true;
            }
        }
        false
    }

    // Put a question, taking the user through review for as long as they are
    // there. Quit writes `Stop`; an amendment unwinds the walk.
    fn ask(
        &mut self,
        marker: Marker,
        path: &str,
        prompt: Prompt<'_>,
        offers: &[Offer],
    ) -> Result<Reply, Halt> {
        let mut draft: Option<String> = None;
        loop {
            let question = Question {
                marker,
                path,
                prompt: prompt.clone(),
                offers,
                reviewable: !self
                    .runner
                    .records
                    .is_empty(),
                draft: match &draft {
                    Some(text) => Some(text.as_str()),
                    None => None,
                },
            };
            match self
                .runner
                .driver
                .ask(question)
            {
                Answer::Done(value) => return Ok(Reply::Done(value)),
                Answer::Skip => return Ok(Reply::Skip),
                Answer::Fail(reason) => return Ok(Reply::Fail(reason)),
                Answer::Override => return Ok(Reply::Override),
                Answer::Quit => return Err(self.stop()),
                Answer::Review(typed) => {
                    let serial = self.scopes[self
                        .scopes
                        .len()
                        - 1]
                    .serial;
                    match self
                        .runner
                        .review(Some(serial), &self.asked)?
                    {
                        Reviewed::Leave => draft = typed,
                        Reviewed::Quit => return Err(self.stop()),
                        Reviewed::Amend(amendment) => return Err(Halt::Restart(amendment)),
                    }
                }
            }
        }
    }

    fn acquire(
        &mut self,
        path: &str,
        text: &str,
        name: Option<&str>,
        forma: Option<&str>,
        seed: Option<&Value>,
    ) -> Result<Reply, Halt> {
        self.ask(
            Marker::Enter,
            path,
            Prompt::Acquire {
                text,
                name,
                forma,
                seed,
            },
            BOUNDARY,
        )
    }

    fn stop(&mut self) -> Halt {
        match self.write(Serial::LIFECYCLE, "/", State::Stop) {
            Ok(()) => Halt::Stop,
            Err(halt) => halt,
        }
    }

    fn write(&mut self, serial: Serial, path: &str, state: State) -> Result<(), Halt> {
        self.runner
            .append(serial, path, state)?;
        self.written += 1;
        Ok(())
    }

    fn top(&mut self) -> &mut Scope<'h> {
        let n = self
            .scopes
            .len()
            - 1;
        &mut self.scopes[n]
    }

    fn show_verdict(&mut self, marker: Marker, path: &str, outcome: &Outcome, restored: bool) {
        let verdict = verdict_of(outcome);
        self.runner
            .driver
            .show(Event::Verdict {
                marker,
                path,
                verdict: &verdict,
                restored,
            });
    }

    fn display_step(&mut self, env: &Environment, source: &'i language::Scope<'i>, path: &str) {
        let subs = env.substitutions();
        let text = formatting::render_step(
            source,
            &subs,
            self.runner
                .driver
                .renderer(),
        );
        let constraints = render_constraints(&self.constraints);
        let depth = self
            .path
            .depth();
        self.runner
            .driver
            .show(Event::Step {
                path,
                constraints: &constraints,
                text: &text,
                depth,
            });
    }

    // A named procedure's heading: its entry line, declaration, title, and
    // description.
    fn announce(&mut self, subroutine: &'i Subroutine<'i>, path: &str, env: &Environment) {
        let echo = if subroutine
            .parameters
            .is_empty()
        {
            String::new()
        } else {
            render_argument_echo(&subroutine.parameters, env)
        };
        let renderer = self
            .runner
            .driver
            .renderer();
        let driver = &mut self
            .runner
            .driver;
        driver.show(Event::Enter { path, echo: &echo });
        if let Some(source) = subroutine.source {
            driver.show(Event::Display(&formatting::render_procedure_declaration(
                source, renderer,
            )));
        }
        if let Some(title) = subroutine.title {
            driver.show(Event::Display(&formatting::render_title(title, renderer)));
        }
        if !subroutine
            .description
            .is_empty()
        {
            driver.show(Event::Display(&formatting::render_description(
                subroutine.description,
                renderer,
            )));
        }
    }
}

fn stance<'h>(prior: Option<&'h Activation>, inputs: &[Supplied]) -> Stance<'h> {
    let Some(a) = prior else {
        return Stance::Fresh;
    };
    if a.standing == engraving::Standing::Withdrawn || a.began != inputs {
        return Stance::Again;
    }
    if a.children
        .is_empty()
        && a.standing == engraving::Standing::Closed
    {
        return Stance::Restore(a);
    }
    Stance::Continue(a)
}

fn rethrow(flow: Flow, outcome: Outcome) -> Flow {
    match (flow, &outcome) {
        (Flow::Throwing(reason), Outcome::Fail(_)) => Flow::Throwing(reason),
        _ => Flow::Completed(outcome),
    }
}

fn unwind(flow: Flow, a: &Activation) -> Flow {
    match thrown(a) {
        Some(reason) => Flow::Throwing(reason),
        None => flow,
    }
}

// A bare `Return` is a skip or a throw; closing Fail on it tells a throw.
fn thrown(a: &Activation) -> Option<String> {
    let effect = a
        .effects
        .last()?;
    match (&effect.returned, concluded(a)) {
        (Some(None), Some((State::Fail(reason), _))) => Some(reason_of(reason)),
        _ => None,
    }
}

fn done(value: Value) -> Flow {
    Flow::Completed(Outcome::Done(value))
}

fn outcome_of(flow: &Flow) -> Outcome {
    match flow {
        Flow::Completed(outcome) => outcome.clone(),
        Flow::Throwing(reason) => Outcome::Fail(reason.clone()),
    }
}

fn answered(reply: Reply, produced: Value) -> Outcome {
    match reply {
        Reply::Done(value) => Outcome::Done(value),
        Reply::Skip => Outcome::Skip(produced),
        Reply::Fail(reason) => Outcome::Fail(reason),
        Reply::Override => Outcome::Done(Value::Unitus),
    }
}

fn rank(outcome: &Outcome) -> Standing {
    match outcome {
        Outcome::Done(_) => Standing::Done,
        Outcome::Skip(_) => Standing::Skip,
        Outcome::Fail(_) => Standing::Fail,
    }
}

fn rank_of_state(state: &State) -> Standing {
    match state {
        State::Skip => Standing::Skip,
        State::Fail(_) => Standing::Fail,
        _ => Standing::Done,
    }
}

/// The outcome an activation recorded.
pub(super) fn recorded(a: &Activation) -> Outcome {
    match &a.outcome {
        Some(State::Skip) => Outcome::Skip(Value::Unitus),
        Some(State::Fail(reason)) => Outcome::Fail(reason_of(reason)),
        Some(State::Done(Some(value))) => Outcome::Done(value.clone()),
        _ => Outcome::Done(Value::Unitus),
    }
}

/// The text of a recorded `Fail [ "reason" = … ]`.
pub(super) fn reason_of(reason: &Option<Value>) -> String {
    match reason {
        Some(Value::Tabularum(pairs)) => match pairs.first() {
            Some((_, Value::Literali(text))) => text.clone(),
            Some((_, other)) => other.to_string(),
            None => String::new(),
        },
        Some(other) => other.to_string(),
        None => String::new(),
    }
}

fn state_of(outcome: &Outcome) -> State {
    match outcome {
        Outcome::Done(value) => State::Done(Some(value.clone())),
        Outcome::Skip(_) => State::Skip,
        Outcome::Fail(reason) if reason.is_empty() => State::Fail(None),
        Outcome::Fail(reason) => State::Fail(Some(engraving::fail_reason(reason))),
    }
}

pub(super) fn verdict_of(outcome: &Outcome) -> Verdict {
    match outcome {
        Outcome::Done(value) => Verdict::Done(value.clone()),
        Outcome::Skip(_) => Verdict::Skip,
        Outcome::Fail(reason) => Verdict::Fail(reason.clone()),
    }
}

// What a closed activation concluded and bound, or a reopened one did before
// its Revoke.
fn concluded(a: &Activation) -> Option<(&State, &[Supplied])> {
    match a.standing {
        engraving::Standing::Closed => a
            .outcome
            .as_ref()
            .map(|state| {
                (
                    state,
                    a.bound
                        .as_slice(),
                )
            }),
        engraving::Standing::Reopened => a
            .former_outcome
            .as_ref()
            .map(|state| {
                (
                    state,
                    a.former_bound
                        .as_slice(),
                )
            }),
        _ => None,
    }
}

// What an activation bound, or last bound before it was withdrawn.
fn kept(a: &Activation) -> &[Supplied] {
    if a.bound
        .is_empty()
    {
        &a.former_bound
    } else {
        &a.bound
    }
}

fn lookup<'a>(bound: &'a [Supplied], name: &str) -> Option<&'a Value> {
    bound
        .iter()
        .find(|item| match &item.name {
            Some(bound) => bound == name,
            None => false,
        })
        .map(|item| &item.value)
}

fn bind_supplied(env: &mut Environment, supplied: &[Supplied]) {
    for item in supplied {
        if let Some(name) = &item.name {
            env.extend(
                name.clone(),
                item.value
                    .clone(),
            );
        }
    }
}

fn is_hole(op: &Operation) -> bool {
    if let Operation::Hole(_) = op {
        true
    } else {
        false
    }
}

fn is_empty_sequence(op: &Operation) -> bool {
    if let Operation::Sequence(ops, _) = op {
        ops.is_empty()
    } else {
        false
    }
}

/// Worst-wins rollup: Fail > Done > Skip, the value last-seen, Done if empty.
struct Rollup {
    rank: Option<Standing>,
    value: Value,
    failure: Option<String>,
}

impl Rollup {
    fn new() -> Self {
        Rollup {
            rank: None,
            value: Value::Unitus,
            failure: None,
        }
    }

    fn absorb(&mut self, outcome: Outcome) {
        let rank = match outcome {
            Outcome::Done(value) => {
                self.value = value;
                Standing::Done
            }
            Outcome::Skip(value) => {
                self.value = value;
                Standing::Skip
            }
            Outcome::Fail(reason) => {
                if self
                    .failure
                    .is_none()
                {
                    self.failure = Some(reason);
                }
                Standing::Fail
            }
        };
        self.rank = Some(match self.rank {
            Some(current) => current.max(rank),
            None => rank,
        });
    }

    fn observe(&mut self, value: Value) {
        self.value = value;
    }

    fn settle(self) -> Outcome {
        match self
            .rank
            .unwrap_or(Standing::Done)
        {
            Standing::Fail => Outcome::Fail(
                self.failure
                    .unwrap_or_default(),
            ),
            Standing::Skip => Outcome::Skip(self.value),
            Standing::Done => Outcome::Done(self.value),
        }
    }
}

/// Classify a step by its final member: `Choice` if it offers responses,
/// otherwise from the last operation of its body.
fn kind_of_step(library: &super::library::Library, op: &Operation) -> Kind {
    match op {
        Operation::Step { responses, .. } if !responses.is_empty() => Kind::Choice,
        Operation::Step { body, .. } => kind_of_step(library, body),
        Operation::Sequence(ops, _) | Operation::Prologue(ops, _) => match ops.last() {
            Some(last) => kind_of_step(library, last),
            None => Kind::Prose,
        },
        Operation::Execute(executable, _) => match &executable.target {
            ExecutableRef::Resolved(id) => match library.nature(*id) {
                Nature::Pure => Kind::Computable,
                Nature::Command | Nature::Instant => Kind::System,
                Nature::Action => Kind::Action,
            },
            ExecutableRef::Unresolved(_) => Kind::Computable,
        },
        Operation::Prose(_, _) => Kind::Prose,
        _ => Kind::Computable,
    }
}

/// `Computable` if any member holds work, else `Prose`.
fn kind_of_scope(op: &Operation) -> Kind {
    match op {
        Operation::Sequence(ops, _) | Operation::Prologue(ops, _) => {
            if ops
                .iter()
                .any(|op| kind_of_scope(op) == Kind::Computable)
            {
                Kind::Computable
            } else {
                Kind::Prose
            }
        }
        Operation::Step { body, .. } | Operation::Section { body, .. } => kind_of_scope(body),
        Operation::Prose(_, _) => Kind::Prose,
        _ => Kind::Computable,
    }
}

/// The values a step reads directly, in the order first met. A name not yet
/// bound contributes nothing.
fn read_values(op: &Operation, env: &Environment) -> Vec<Supplied> {
    let mut names = Vec::new();
    names_read(op, &mut names);
    names
        .into_iter()
        .filter_map(|name| {
            env.lookup(name)
                .map(|value| Supplied {
                    value: value.clone(),
                    name: Some(name.to_string()),
                })
        })
        .collect()
}

fn names_read<'i>(op: &Operation<'i>, found: &mut Vec<&'i str>) {
    match op {
        Operation::Variable(id, _) => {
            if !found.contains(&id.value) {
                found.push(id.value);
            }
        }
        Operation::Loop { over, body, .. } => {
            if let Some(over) = over {
                names_read(over, found);
            }
            names_read(body, found);
        }
        Operation::Within { bound, body, .. } => {
            names_read(bound, found);
            names_read(body, found);
        }
        Operation::Bind { value, .. } => names_read(value, found),
        Operation::Cost(inner, _) => names_read(inner, found),
        Operation::Sequence(ops, _)
        | Operation::List(ops, _)
        | Operation::Tuple(ops, _)
        | Operation::Prologue(ops, _) => {
            for op in ops {
                names_read(op, found);
            }
        }
        Operation::Invoke(invocable, _) => {
            for argument in &invocable.arguments {
                names_read(argument, found);
            }
        }
        Operation::Execute(executable, _) => {
            for argument in &executable.arguments {
                names_read(argument, found);
            }
        }
        Operation::String(fragments, _) => {
            for fragment in fragments {
                if let Fragment::Interpolation(op) = fragment {
                    names_read(op, found);
                }
            }
        }
        Operation::Tablet(entries, _) => {
            for entry in entries {
                names_read(&entry.value, found);
            }
        }
        Operation::Step { .. }
        | Operation::Section { .. }
        | Operation::Number(_, _)
        | Operation::Response(_, _)
        | Operation::Verbatim(_, _)
        | Operation::Prose(_, _)
        | Operation::Hole(_)
        | Operation::Unit(_) => {}
    }
}

/// The names of the first `Bind` in a step body.
fn binding_names<'i>(op: &Operation<'i>) -> Option<&'i [language::Identifier<'i>]> {
    match op {
        Operation::Bind { names, .. } => Some(names),
        Operation::Sequence(ops, _) => ops
            .iter()
            .find_map(binding_names),
        _ => None,
    }
}

/// Every name a body binds directly, not descending into nested steps.
fn bindings<'i>(op: &Operation<'i>, found: &mut Vec<&'i language::Identifier<'i>>) {
    match op {
        Operation::Bind { names, .. } => found.extend(names.iter()),
        Operation::Sequence(ops, _) | Operation::Prologue(ops, _) => {
            for op in ops {
                bindings(op, found);
            }
        }
        _ => {}
    }
}

/// Whether a step body is nothing but prose and descriptive `~` bindings.
fn binds_descriptively(op: &Operation) -> bool {
    match op {
        Operation::Bind { value, .. } => is_empty_sequence(value),
        Operation::Sequence(ops, _) => {
            let mut bound = false;
            for op in ops {
                if let Operation::Prose(_, _) = op {
                    continue;
                }
                if binds_descriptively(op) {
                    bound = true;
                } else {
                    return false;
                }
            }
            bound
        }
        _ => false,
    }
}

/// The loop variables bound for this pass, as an iteration's `Begin` states them.
fn iteration_values(names: &[language::Identifier], env: &Environment) -> Vec<Supplied> {
    names
        .iter()
        .filter_map(|name| {
            env.lookup(name.value)
                .map(|value| Supplied {
                    value: value.clone(),
                    name: Some(
                        name.value
                            .to_string(),
                    ),
                })
        })
        .collect()
}

fn render_argument_echo(params: &[Option<String>], env: &Environment) -> String {
    let names: Vec<&str> = params
        .iter()
        .flatten()
        .map(String::as_str)
        .collect();
    format!("({})", render_bindings(&names, env))
}

fn render_iteration_echo(names: &[language::Identifier], env: &Environment) -> String {
    if names.is_empty() {
        return String::new();
    }
    let names: Vec<&str> = names
        .iter()
        .map(|n| n.value)
        .collect();
    format!("({})", render_bindings(&names, env))
}

fn render_bindings(names: &[&str], env: &Environment) -> String {
    names
        .iter()
        .map(|name| match env.lookup(name) {
            Some(value) => format!("{} ~ {}", value, name),
            None => format!(" ~ {}", name),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn render_constraints(constraints: &[Value]) -> String {
    constraints
        .iter()
        .map(|budget| format!("$({budget})"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// Each parameter's forma as a prompt shows it. A single list parameter
/// (`[Region]`) renders bracketed so the prompt takes a list.
pub(super) fn render_parameter_formae(signature: Option<&language::Signature>) -> Vec<String> {
    match signature.map(|s| &s.requires) {
        Some(genus @ language::Genus::List(_)) => vec![formatting::render_genus(genus, &Identity)],
        Some(genus) => genus
            .formae()
            .iter()
            .map(|f| {
                f.value
                    .to_string()
            })
            .collect(),
        None => Vec::new(),
    }
}

#[cfg(test)]
#[path = "checks/walker.rs"]
mod check;
