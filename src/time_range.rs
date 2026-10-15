//! Time ranges, and compile-time proof that an action happened inside one.

use vstd::prelude::*;

verus! {

/// Why a moment wasn't accepted.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum OutOfRange {
    /// Before the range opens (e.g. a waiting period hasn't passed).
    TooEarly,
    /// After the range closes (e.g. a deadline has passed).
    TooLate,
}

/// An inclusive range of moments `start..=end`, measured in the same units
/// as the timestamps you pass in (e.g. seconds since the epoch).
///
/// # Use it for
/// Time rules from contracts or regulation. One type covers three shapes:
/// - **Deadlines and expiries** ("disputes within 60 days", "the offer
///   expires on the 31st"): [`TimeRange::until`], [`TimeRange::starting`].
/// - **Waiting periods** ("funds may not be disbursed until 3 days after the
///   disclosure", "cooling-off periods"): [`TimeRange::not_before`].
/// - **Windows with both ends** ("enrollment opens on the 1st and closes on
///   the 15th"): [`TimeRange::between`].
///
/// Create the range when the clock starts, then check it at the moment of the action.
///
/// # Example
/// ```ignore
/// let window = TimeRange::starting(statement_date, 60 * DAY).ok_or(BadDate)?;
/// let proof = window.check(now).map_err(|_| DisputeTooLate)?;
/// accept_dispute(claim, proof);   // requires proof that this window was checked
///
/// let wait = TimeRange::not_before(disclosed_at + 3 * DAY);
/// disburse(loan, wait.check(now)?);
/// ```
///
/// # What it proves
/// - Constructors are exact, with no wrapped (earlier) end on overflow:
///   `starting(s, len)` is exactly `s..=s+len`, or `None`.
/// - `check(now)` succeeds **exactly** when `start <= now <= end`; both ends
///   count as inside. On failure it says which side: `TooEarly` or `TooLate`.
/// - The returned [`InRange`] token records which range and which moment were
///   checked. A function that takes `Tracked<InRange>` and requires
///   `t@.end() == ...` (or `t@.start() == ...`) can only be called after a
///   passing check of **that** range. Calling it without checking, or with a
///   token from a different range, doesn't verify. The token costs nothing
///   at runtime.
///
/// # What it does NOT prove
/// - That `now` is the real current time. Timestamps come from outside the
///   program; read them from one trusted clock.
/// - Business-day calendars (weekends, holidays). Compute the dates with a
///   calendar first, then use this type.
pub struct TimeRange { start: u64, end: u64 }

/// Proof that moment `at` was checked and fell inside the range `start..=end`.
/// Zero-sized and erased at runtime; only [`TimeRange::check`] can create one.
#[allow(dead_code)] // fields exist only for specs
pub tracked struct InRange { ghost start: u64, ghost end: u64, ghost at: u64 }

impl InRange {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool { self.start <= self.at && self.at <= self.end }

    pub closed spec fn start(self) -> u64 { self.start }
    pub closed spec fn end(self) -> u64 { self.end }
    pub closed spec fn at(self) -> u64 { self.at }

    /// Every token records a check that passed: `start() <= at() <= end()`.
    pub proof fn holds(tracked &self) ensures self.start() <= self.at() && self.at() <= self.end() {
        use_type_invariant(self);
    }
}

impl TimeRange {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool { self.start <= self.end }

    pub closed spec fn start_spec(&self) -> u64 { self.start }
    pub closed spec fn end_spec(&self) -> u64 { self.end }

    /// Whether moment `t` is inside the range (both ends included).
    pub open spec fn contains(&self, t: u64) -> bool { self.start_spec() <= t && t <= self.end_spec() }

    /// Any moment up to and including `end`: a deadline.
    pub fn until(end: u64) -> (r: Self) ensures r.start_spec() == 0, r.end_spec() == end {
        TimeRange { start: 0, end }
    }

    /// Any moment from `start` on: a waiting period.
    pub fn not_before(start: u64) -> (r: Self) ensures r.start_spec() == start, r.end_spec() == u64::MAX {
        TimeRange { start, end: u64::MAX }
    }

    /// From `start` to `end`, both included. `None` if `start > end`.
    pub fn between(start: u64, end: u64) -> (r: Option<Self>)
        ensures
            r is Some <==> start <= end,
            r matches Some(x) ==> x.start_spec() == start && x.end_spec() == end,
    {
        if start <= end { Some(TimeRange { start, end }) } else { None }
    }

    /// From `start` for `len` units: `start..=start+len`. `None` on overflow.
    pub fn starting(start: u64, len: u64) -> (r: Option<Self>)
        ensures
            match r {
                Some(x) => x.start_spec() == start && x.end_spec() == start + len,
                None    => start + len > u64::MAX,
            },
    {
        match start.checked_add(len) {
            Some(end) => Some(TimeRange { start, end }),
            None => None,
        }
    }

    pub fn start(&self) -> (r: u64) ensures r == self.start_spec() { self.start }
    pub fn end(&self) -> (r: u64) ensures r == self.end_spec() { self.end }

    pub fn check(&self, now: u64) -> (r: Result<Tracked<InRange>, OutOfRange>)
        ensures
            r is Ok <==> self.contains(now),
            r matches Ok(t) ==> t@.start() == self.start_spec() && t@.end() == self.end_spec() && t@.at() == now,
            r == Err::<Tracked<InRange>, OutOfRange>(OutOfRange::TooEarly) <==> now < self.start_spec(),
            r == Err::<Tracked<InRange>, OutOfRange>(OutOfRange::TooLate) <==> now > self.end_spec(),
    {
        proof { use_type_invariant(self); }
        if now < self.start { return Err(OutOfRange::TooEarly); }
        if now > self.end { return Err(OutOfRange::TooLate); }
        let tracked t = InRange { start: self.start, end: self.end, at: now };
        Ok(Tracked(t))
    }
}

} // verus!
