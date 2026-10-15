//! Deadlines, and compile-time proof that an action happened on time.

use vstd::prelude::*;

verus! {

/// The deadline had already passed.
pub struct Late;

/// A point in time by which something must happen, measured in the same
/// units as the timestamps you pass in (e.g. seconds since the epoch).
///
/// # Use it for
/// Time limits from contracts or regulation: "disputes must be filed within
/// 60 days of the statement", "a rate lock expires after 45 days", "respond
/// within 10 business days". Create the deadline when the clock starts, then
/// check it at the moment of the action.
///
/// # Example
/// ```ignore
/// let window = Deadline::after(statement_date, 60 * DAY).ok_or(BadDate)?;
/// let on_time = window.check(now).map_err(|Late| DisputeTooLate)?;
/// accept_dispute(claim, on_time);   // requires proof it was checked in time
/// ```
///
/// # What it proves
/// - `after(start, len)` is exactly `start + len`, or `None` on overflow
///   (never a wrapped, earlier deadline).
/// - `check(now)` succeeds **exactly** when `now <= due`, and returns an
///   [`OnTime`] token recording which deadline and which time were checked.
/// - A function that takes `Tracked<OnTime>` with
///   `requires t@.due() == d.due_spec()` can only be called after a
///   successful check of **that** deadline. Calling it without checking, or
///   with a token from a different deadline, doesn't verify. The token costs
///   nothing at runtime.
///
/// # What it does NOT prove
/// - That `now` is the real current time. Timestamps come from outside the
///   program; read them from one trusted clock.
/// - Business-day calendars (weekends, holidays). Compute the deadline with a
///   calendar first, then use this type.
pub struct Deadline { due: u64 }

/// Proof that a deadline was checked at time `at` and had not passed.
/// Zero-sized and erased at runtime; only [`Deadline::check`] can create one.
#[allow(dead_code)] // fields exist only for specs
pub tracked struct OnTime { ghost due: u64, ghost at: u64 }

impl OnTime {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool { self.at <= self.due }

    pub closed spec fn due(self) -> u64 { self.due }
    pub closed spec fn at(self) -> u64 { self.at }

    /// Every token records a check that passed: `at() <= due()`.
    pub proof fn was_on_time(tracked &self) ensures self.at() <= self.due() {
        use_type_invariant(self);
    }
}

impl Deadline {
    pub closed spec fn due_spec(&self) -> u64 { self.due }

    pub fn at(due: u64) -> (r: Self) ensures r.due_spec() == due { Deadline { due } }

    pub fn after(start: u64, len: u64) -> (r: Option<Self>)
        ensures
            match r {
                Some(d) => d.due_spec() == start + len,
                None    => start + len > u64::MAX,
            },
    {
        match start.checked_add(len) {
            Some(due) => Some(Deadline { due }),
            None => None,
        }
    }

    pub fn due(&self) -> (r: u64) ensures r == self.due_spec() { self.due }

    pub fn check(&self, now: u64) -> (r: Result<Tracked<OnTime>, Late>)
        ensures
            r is Ok <==> now <= self.due_spec(),
            r matches Ok(t) ==> t@.due() == self.due_spec() && t@.at() == now && now <= self.due_spec(),
    {
        if now <= self.due {
            let tracked t = OnTime { due: self.due, at: now };
            Ok(Tracked(t))
        } else {
            Err(Late)
        }
    }
}

} // verus!
