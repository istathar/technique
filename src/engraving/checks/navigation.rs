use crate::engraving::{InvokeTarget, Motion, Position, Record, RunId, Serial, State, Trail};

fn record(serial: u32, path: &str, state: State) -> Record {
    Record {
        recorded: "2026-05-14T12:00:00Z".to_string(),
        run_id: RunId(1),
        serial: Serial(serial),
        path: path.to_string(),
        state,
    }
}

// A step invoking a procedure, which the trail writes at a path beside the
// step rather than beneath it.
fn calling() -> Vec<Record> {
    vec![
        record(
            0,
            "/",
            State::Start {
                uri: "file://x".to_string(),
            },
        ),
        record(1, "/task:", State::Begin(Vec::new())),
        record(2, "/task:/1", State::Begin(Vec::new())),
        record(
            2,
            "/task:/1",
            State::Invoke(InvokeTarget::Procedure("check:".to_string())),
        ),
        record(3, "/task:/check:", State::Begin(Vec::new())),
        record(3, "/task:/check:", State::Done(None)),
        record(2, "/task:/1", State::Done(None)),
        record(1, "/task:", State::Done(None)),
    ]
}

/// The callee is enclosed by the step that invoked it, not by the scope its
/// path sits under, so Left out of it reaches the call site.
#[test]
fn a_callee_is_enclosed_by_its_call_site() {
    let records = calling();
    let trail = Trail::new(&records);

    assert_eq!(
        trail.step(Position::At(4), Motion::Left),
        Some(Position::At(2))
    );
    assert_eq!(
        trail.step(Position::At(3), Motion::Right),
        Some(Position::At(4))
    );
    assert_eq!(trail.step(Position::At(4), Motion::PageUp), None);
    assert_eq!(trail.step(Position::At(4), Motion::PageDown), None);
}

/// Down off the last record reaches the prompt the run is waiting at, and a
/// run that walked to its end has no prompt to reach.
#[test]
fn down_off_the_end_leaves_review() {
    let records = calling();
    let trail = Trail::new(&records);
    assert_eq!(
        trail.step(Position::At(7), Motion::Down),
        Some(Position::Live)
    );
    assert_eq!(
        trail.step(Position::Live, Motion::Up),
        Some(Position::At(7))
    );
    assert_eq!(trail.step(Position::Live, Motion::Down), None);

    let mut ended = calling();
    ended.push(record(0, "/", State::Finish));
    let trail = Trail::new(&ended);
    assert_eq!(trail.last(), Some(Position::At(7)));
    assert_eq!(trail.step(Position::At(7), Motion::Down), None);
    assert_eq!(trail.step(Position::At(0), Motion::Up), None);
}

/// `Stop` and `Resume` bracket a session, not the walk. Review opens on the
/// last thing the walk did, and stepping past where a run was interrupted
/// crosses the pair as though it were not there.
#[test]
fn a_session_boundary_is_not_a_position() {
    let mut records = calling();
    records.insert(6, record(0, "/", State::Resume));
    records.insert(6, record(0, "/", State::Stop));
    records.push(record(0, "/", State::Stop));
    records.push(record(0, "/", State::Resume));
    let trail = Trail::new(&records);

    assert_eq!(trail.last(), Some(Position::At(9)));
    assert_eq!(
        trail.step(Position::Live, Motion::Up),
        Some(Position::At(9))
    );
    // 5 and 8 are the records either side of the interruption.
    assert_eq!(
        trail.step(Position::At(8), Motion::Up),
        Some(Position::At(5))
    );
    assert_eq!(
        trail.step(Position::At(5), Motion::Down),
        Some(Position::At(8))
    );
    assert_eq!(
        trail.step(Position::At(9), Motion::Down),
        Some(Position::Live)
    );
}
