//! Layer 3: card and transfer disputes with a regulatory deadline.
//!
//! US Regulation E gives consumers 60 days after the statement is sent to
//! report an unauthorized electronic transfer. A bank that refuses a timely
//! dispute, or accepts one with the wrong deadline, is out of compliance.
//!
//! # Rules (all proved)
//! - A dispute case can only be opened with an [`OnTime`] token from checking
//!   **that statement's** 60-day deadline, so a late dispute can't be accepted
//!   by mistake and a check against a different deadline doesn't count.
//! - The deadline is exactly statement date + 60 days (no overflow, no
//!   off-by-one: a dispute on day 60 itself is on time).

use vstd::prelude::*;
use verus_types::deadline::{Deadline, Late, OnTime};

verus! {

pub const DAY: u64 = 86_400;
pub const REG_E_WINDOW: u64 = 60 * DAY;

pub struct Statement { pub account: u64, pub sent_at: u64 }

pub struct Case { pub account: u64, pub entry: u64, pub opened_at: u64 }

/// The dispute window for a statement: exactly 60 days after it was sent.
/// Written with the literal 60 days, not `REG_E_WINDOW`, so the spec states the
/// regulation independently of the code: changing the constant fails verification.
pub open spec fn window_end(s: &Statement) -> int { s.sent_at + 60 * 86_400 }

#[derive(Debug)]
pub enum DisputeError { TooLate, BadDate }

/// Check the window. Returns a token proving the check passed, at `now`.
pub fn check_window(s: &Statement, now: u64) -> (r: Result<Tracked<OnTime>, DisputeError>)
    ensures
        r matches Ok(t) ==> t@.due() == window_end(s) && t@.at() == now && now <= window_end(s),
        r matches Err(DisputeError::TooLate) ==> now > window_end(s),
{
    let d = match Deadline::after(s.sent_at, REG_E_WINDOW) { Some(d) => d, None => return Err(DisputeError::BadDate) };
    match d.check(now) {
        Ok(t) => Ok(t),
        Err(Late) => Err(DisputeError::TooLate),
    }
}

/// Open a case. Can only be called with proof that the window was checked
/// for this statement and the dispute was on time.
#[allow(unused_variables)] // `on_time` exists only for the proof
pub fn open_case(s: &Statement, entry: u64, now: u64, on_time: Tracked<OnTime>) -> (c: Case)
    requires on_time@.due() == window_end(s), on_time@.at() == now,
    ensures c.account == s.account && c.entry == entry && c.opened_at == now && now <= window_end(s),
{
    proof { on_time.borrow().was_on_time(); }   // the token itself carries the fact
    Case { account: s.account, entry, opened_at: now }
}

} // verus!
