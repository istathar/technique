//! Hold each `.moves` table against the trail it names.
//!
//! A table sits beside a `.pfftt` of the same stem and states, for every record
//! of that trail and for the live prompt, where each of the six motions lands.
//! Blank lines and lines opening with `#` are ignored; every other line is
//!
//!     <path> <verb> <key> <destination>
//!
//! with `(live)` standing in for `<path> <verb>` at the prompt. `<key>` is one
//! of Up, Down, Left, Right, PageUp, PageDown. `<destination>` is another
//! `<path> <verb>`, or `(live)`, or `(refused)` where the motion does not move.
//!
//! Origins must stand in trail order and account for every record, one block
//! each. That is what names a record, rather than a search: a procedure invoked
//! twice writes the same path and verb both times, and only its place in the
//! order tells the two apart.

use std::fs;
use std::path::Path;

use technique::engraving::{Motion, Position, Record, State, Trail, parse_records};

use crate::common::list_files;

// The verb a record is named by in a `.moves` table: the keyword its line
// carries, without the payload.
fn verb(state: &State) -> &'static str {
    match state {
        State::Start { .. } => "Start",
        State::Finish => "Finish",
        State::Stop => "Stop",
        State::Resume => "Resume",
        State::Invoke(_) => "Invoke",
        State::Execute { .. } => "Execute",
        State::Return(_) => "Return",
        State::Begin(_) => "Begin",
        State::Bind(_) => "Bind",
        State::Revoke => "Revoke",
        State::Done(_) => "Done",
        State::Skip => "Skip",
        State::Fail(_) => "Fail",
    }
}

fn name(record: &Record) -> String {
    format!("{} {}", record.path, verb(&record.state))
}

// How a position is written in a `.moves` table.
fn render(trail: &Trail, position: Option<Position>) -> String {
    match position {
        None => "(refused)".to_string(),
        Some(Position::Live) => "(live)".to_string(),
        Some(Position::At(at)) => name(&trail.records()[at]),
    }
}

fn motion(key: &str) -> Motion {
    match key {
        "Up" => Motion::Up,
        "Down" => Motion::Down,
        "Left" => Motion::Left,
        "Right" => Motion::Right,
        "PageUp" => Motion::PageUp,
        "PageDown" => Motion::PageDown,
        other => panic!("unknown key {:?}", other),
    }
}

/// Walk every table beside a trail and require that the reusltant cursor
/// conforms to it. The table is a specification.
#[test]
fn ensure_moves() {
    let dir = Path::new("tests/navigation/");
    let files = list_files(dir, "moves");

    let mut failures = Vec::new();

    for file in &files {
        let expected_path = file.with_extension("pfftt");
        let content = fs::read_to_string(&expected_path).unwrap_or_else(|e| {
            panic!(
                "missing trail {:?}: {:?} — add the .pfftt beside the table",
                expected_path, e
            )
        });
        let records = parse_records(&content)
            .unwrap_or_else(|e| panic!("trail {:?} is malformed: {:?}", expected_path, e));
        let trail = Trail::new(&records);

        let table = fs::read_to_string(file).expect("read the moves table");
        let mut at = 0;
        let mut opened = false;

        for (number, line) in table
            .lines()
            .enumerate()
        {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let fields: Vec<&str> = line
                .split_whitespace()
                .collect();
            let (origin, key, destination) = match fields.as_slice() {
                ["(live)", key, rest @ ..] => ("(live)".to_string(), *key, rest.join(" ")),
                [path, state, key, rest @ ..] => {
                    (format!("{} {}", path, state), *key, rest.join(" "))
                }
                _ => panic!("{:?} line {}: malformed row", file, number + 1),
            };

            let from = if origin == "(live)" {
                Position::Live
            } else {
                if !opened {
                    opened = true;
                } else if name(&records[at]) != origin {
                    at += 1;
                }
                match records.get(at) {
                    Some(record) if name(record) == origin => {}
                    Some(record) => panic!(
                        "{:?} line {}: {:?} where {:?} stands in {:?}",
                        file,
                        number + 1,
                        origin,
                        name(record),
                        expected_path
                    ),
                    None => panic!(
                        "{:?} line {}: {:?} runs past the end of {:?}",
                        file,
                        number + 1,
                        origin,
                        expected_path
                    ),
                }
                Position::At(at)
            };

            let reached = render(&trail, trail.step(from, motion(key)));
            if reached != destination {
                println!(
                    "{:?} line {}: {} {} reached {} not {}",
                    file,
                    number + 1,
                    origin,
                    key,
                    reached,
                    destination
                );
                failures.push(file.clone());
            }
        }

        // A table that stops short of the last record is not the exhaustive
        // account it claims to be.
        let reached = if opened { at + 1 } else { 0 };
        if reached != records.len() {
            println!(
                "{:?}: accounts for {} of {} records",
                file,
                reached,
                records.len()
            );
            failures.push(file.clone());
        }
    }

    if !failures.is_empty() {
        panic!("{} navigation tables did not hold", failures.len());
    }
}
