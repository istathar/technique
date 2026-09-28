//! Answering at the keyboard: the live prompt line and the review frame,
//! redrawn in place on each key.

use std::io::{self, Write};

use crossterm::style::{
    Attribute, Color, ResetColor, SetAttribute, SetBackgroundColor, SetForegroundColor, Stylize,
};
use crossterm::terminal::{Clear, ClearType, size};
use crossterm::{cursor, queue};

use crate::engraving::display_path;
use crate::formatting::Render;
use crate::highlighting::Terminal;
use crate::value::Value;

use super::keys::{Keys, RealKeyboard};
use super::prompt::{Asking, Field, Menu, Reason, Reviewing};
use super::trail::{announce, glyph, verdict_glyph};
use super::{Answer, Frame, Output, Policy, Prompt, Question, Review, Standing};

/// Answers every question from the keyboard.
pub struct Interactive<K: Keys = RealKeyboard> {
    pub(super) keys: K,
}

impl<K: Keys> Policy for Interactive<K> {
    fn ask<O: Output>(&mut self, out: &mut O, question: Question<'_>) -> Answer {
        ask(out.surface(), &mut self.keys, &question)
    }

    fn review<O: Output>(&mut self, out: &mut O, frame: Frame<'_>) -> Review {
        review(out.surface(), &mut self.keys, &frame)
    }
}

const PROMPT_SYMBOL: &str = "▶";

const REASON_PREFIX: &str = "Reason? ";

// Mirrors the `Terminal` renderer's `Syntax::Marker`.
const MARKER_GREY: Color = Color::Rgb {
    r: 0x55,
    g: 0x57,
    b: 0x53,
};

const FAIL_RED: Color = Color::Rgb {
    r: 0xcc,
    g: 0x00,
    b: 0x00,
};

const SKIP_YELLOW: Color = Color::Rgb {
    r: 0xc4,
    g: 0xa0,
    b: 0x00,
};

const RESPONSE: Color = Color::Rgb {
    r: 0xf5,
    g: 0x79,
    b: 0x00,
};

const RESPONSE_ACTIVE: Color = Color::Rgb {
    r: 0x8f,
    g: 0x59,
    b: 0x02,
};

const LIGHT_BROWN: Color = Color::Rgb {
    r: 0xc8,
    g: 0x96,
    b: 0x4b,
};

/// What precedes the `▶` on a prompt line.
enum Head<'a> {
    Plain {
        marker: &'static str,
        text: String,
    },
    Action {
        path: String,
        verb: &'a str,
        value: &'a Value,
    },
}

fn head<'a>(question: &Question<'a>) -> Head<'a> {
    let marker = glyph(question.marker);
    let path = display_path(question.path);
    let text = match &question.prompt {
        Prompt::Confirm { .. } | Prompt::Command { .. } | Prompt::External => path,
        // The space before `(name : forma)` stands even when `text` is empty.
        Prompt::Acquire {
            text, name, forma, ..
        } => format!(
            "{} {}({} : {})",
            path,
            text,
            name.unwrap_or("?"),
            forma.unwrap_or("?")
        ),
        Prompt::Depart { echo } => announce(&path, echo),
        Prompt::Action { verb, value, .. } => {
            return Head::Action { path, verb, value };
        }
    };
    Head::Plain { marker, text }
}

fn columns(text: &str) -> u16 {
    text.chars()
        .count() as u16
}

fn clear<W: Write>(out: &mut W) {
    let _ = queue!(out, cursor::MoveToColumn(0), Clear(ClearType::CurrentLine));
}

pub(super) fn ask<W: Write, K: Keys>(out: &mut W, keys: &mut K, question: &Question<'_>) -> Answer {
    let head = head(question);
    let mut asking = Asking::begin(question);
    let answer = {
        let _raw = match keys.hold() {
            Some(raw) => raw,
            None => {
                let _ = writeln!(out, "(could not enter raw mode)");
                return Answer::Quit;
            }
        };
        loop {
            if draw(out, &head, &asking).is_err() {
                break Answer::Quit;
            }
            match keys.next() {
                None => break Answer::Quit,
                Some(intent) => {
                    if let Some(answer) = asking.handle(intent) {
                        break answer;
                    }
                }
            }
        }
    };
    clear(out);
    let _ = queue!(out, cursor::Show);
    let _ = out.flush();
    answer
}

pub(super) fn review<W: Write, K: Keys>(out: &mut W, keys: &mut K, frame: &Frame<'_>) -> Review {
    let path = display_path(frame.path);
    let mut reviewing = Reviewing::begin(frame.offers, frame.verdict);
    let result = {
        let _raw = match keys.hold() {
            Some(raw) => raw,
            None => {
                let _ = writeln!(out, "(could not enter raw mode)");
                return Review::Quit;
            }
        };
        loop {
            if draw_review(out, frame, &path, &reviewing).is_err() {
                break Review::Quit;
            }
            match keys.next() {
                None => break Review::Quit,
                Some(intent) => {
                    if let Some(answer) = reviewing.handle(intent) {
                        break answer;
                    }
                }
            }
        }
    };
    // A motion leaves the line standing for the next frame to redraw over,
    // which would otherwise be seen as flicker.
    if let Review::Move(_) = result {
    } else {
        clear(out);
        let _ = queue!(out, cursor::Show);
        let _ = out.flush();
    }
    result
}

/// `{marker} {text} ▶ {tail}`, the `▶` coloured for what Enter would answer.
fn draw<W: Write>(out: &mut W, head: &Head<'_>, asking: &Asking) -> io::Result<()> {
    clear(out);
    let prefix = match head {
        Head::Plain { marker, text } => {
            let symbol = match asking.standing {
                Standing::Done => PROMPT_SYMBOL.blue(),
                Standing::Fail => PROMPT_SYMBOL.with(FAIL_RED),
                Standing::Skip => PROMPT_SYMBOL.with(SKIP_YELLOW),
            };
            let lead = format!("{} {}", marker, text);
            write!(
                out,
                "{} {} ",
                lead.as_str()
                    .with(MARKER_GREY),
                symbol
            )?;
            columns(&lead) + 3
        }
        Head::Action { path, verb, value } => {
            let lead = format!("» {}", path);
            write!(
                out,
                "{} ",
                lead.as_str()
                    .with(MARKER_GREY)
            )?;
            queue!(out, SetForegroundColor(LIGHT_BROWN))?;
            write!(out, "{}", verb)?;
            queue!(out, ResetColor)?;
            let label = value.label();
            let mut width = columns(&lead) + 1 + columns(verb);
            if !label.is_empty() {
                if let Value::Enumerati(_) = value {
                    queue!(out, SetForegroundColor(RESPONSE))?;
                    write!(out, " {}", label)?;
                    queue!(out, ResetColor)?;
                } else {
                    write!(out, " {}", label)?;
                }
                width += 1 + columns(&label);
            }
            write!(out, " {} ", PROMPT_SYMBOL.blue())?;
            width + 3
        }
    };
    let (at, end) = draw_tail(out, asking, prefix)?;
    place_cursor(out, at, end)
}

/// The menu, the reason, or the field; returns the cursor's column (`None`
/// hides it) and the column writing ended at.
fn draw_tail<W: Write>(
    out: &mut W,
    asking: &Asking,
    prefix: u16,
) -> io::Result<(Option<u16>, u16)> {
    if let Some(reason) = &asking.reason {
        return draw_reason(out, reason, prefix);
    }
    if let Some(menu) = &asking.menu {
        render_menu(out, menu, |item| asking.offerable(item))?;
        return Ok((None, prefix));
    }
    match &asking.field {
        Field::Edit {
            buffer,
            cursor,
            bracketed,
            ..
        } => {
            let lead = if *bracketed {
                write!(out, "[{}]", buffer)?;
                1
            } else {
                write!(out, "{}", buffer)?;
                0
            };
            let at = prefix + lead + columns(&buffer[..*cursor]);
            let end = prefix + columns(buffer) + 2 * lead;
            Ok((Some(at), end))
        }
        Field::Frozen { .. } => Ok((Some(prefix), prefix)),
        Field::Choose { choices, active } => {
            render_choices(out, choices, *active)?;
            Ok((None, prefix))
        }
    }
}

fn draw_reason<W: Write>(
    out: &mut W,
    reason: &Reason,
    prefix: u16,
) -> io::Result<(Option<u16>, u16)> {
    write!(out, "{}{}", REASON_PREFIX, reason.buffer)?;
    let lead = prefix + columns(REASON_PREFIX);
    Ok((
        Some(lead + columns(&reason.buffer[..reason.cursor])),
        lead + columns(&reason.buffer),
    ))
}

/// `{marker} {path} [~ names] {glyph}   [menu]`, all grey but the glyph; while
/// a Fail reason is being typed, `{marker} {path} ▶ Reason? {text}`.
fn draw_review<W: Write>(
    out: &mut W,
    frame: &Frame<'_>,
    path: &str,
    reviewing: &Reviewing,
) -> io::Result<()> {
    clear(out);
    let lead = format!("{} {}", glyph(frame.marker), path);
    if let Some(reason) = &reviewing.reason {
        write!(
            out,
            "{} {} ",
            lead.as_str()
                .with(MARKER_GREY),
            PROMPT_SYMBOL.blue()
        )?;
        let (at, end) = draw_reason(out, reason, columns(&lead) + 3)?;
        return place_cursor(out, at, end);
    }
    queue!(out, cursor::Hide)?;
    write!(out, "{}", format!("{} ", lead).with(MARKER_GREY))?;
    if !frame
        .bound
        .is_empty()
    {
        write!(out, "{}", format!("{} ", frame.bound).with(MARKER_GREY))?;
    }
    if let Some(verdict) = frame.verdict {
        let (mark, syntax) = verdict_glyph(verdict);
        write!(out, "{}", Terminal.style(syntax, mark))?;
    }
    write!(out, "   ")?;
    if let Some(menu) = &reviewing.menu {
        render_menu(out, menu, |_| true)?;
    }
    out.flush()
}

/// The highlighted offer in reverse video, a disabled one dimmed.
fn render_menu<W: Write>(
    out: &mut W,
    menu: &Menu,
    enabled: impl Fn(super::Offer) -> bool,
) -> io::Result<()> {
    for (i, item) in menu
        .offers
        .iter()
        .enumerate()
    {
        if i > 0 {
            write!(out, "  ")?;
        }
        let label = item.label();
        if i == menu.active {
            queue!(out, SetAttribute(Attribute::Reverse))?;
            write!(out, " {} ", label)?;
            queue!(out, SetAttribute(Attribute::Reset))?;
        } else if !enabled(*item) {
            queue!(out, SetAttribute(Attribute::Dim))?;
            write!(out, " {} ", label)?;
            queue!(out, SetAttribute(Attribute::Reset))?;
        } else {
            write!(out, " {} ", label)?;
        }
    }
    Ok(())
}

fn render_choices<W: Write>(out: &mut W, choices: &[String], active: usize) -> io::Result<()> {
    for (i, choice) in choices
        .iter()
        .enumerate()
    {
        if i > 0 {
            write!(out, "  ")?;
        }
        queue!(out, SetAttribute(Attribute::Bold))?;
        if i == active {
            queue!(
                out,
                SetBackgroundColor(Color::White),
                SetForegroundColor(RESPONSE_ACTIVE)
            )?;
        } else {
            queue!(out, SetForegroundColor(RESPONSE))?;
        }
        write!(out, " {} ", choice)?;
        queue!(out, ResetColor, SetAttribute(Attribute::Reset))?;
    }
    Ok(())
}

/// Put the cursor at `at` having written up to `end`. Past the right margin an
/// absolute column clamps to the edge, so a wrapped line is resolved against
/// the terminal's width into a move back from the end.
fn place_cursor<W: Write>(out: &mut W, at: Option<u16>, end: u16) -> io::Result<()> {
    match at {
        None => {
            queue!(out, cursor::Hide)?;
        }
        Some(target) if target >= end => {
            queue!(out, cursor::Show)?;
        }
        Some(target) => {
            let width = size()
                .map(|(cols, _)| cols)
                .unwrap_or(80)
                .max(1);
            // A column exactly filling a row leaves the cursor on that row.
            let row = if end.is_multiple_of(width) {
                end / width - 1
            } else {
                end / width
            };
            let up = row - target / width;
            queue!(out, cursor::Show)?;
            if up > 0 {
                queue!(out, cursor::MoveUp(up))?;
            }
            queue!(out, cursor::MoveToColumn(target % width))?;
        }
    }
    out.flush()
}

#[cfg(test)]
#[path = "checks/console.rs"]
mod check;
