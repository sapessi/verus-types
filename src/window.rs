//! Limits over time windows: "at most $10,000 per day", "at most 5 attempts per hour".

use vstd::prelude::*;

verus! {

#[derive(Debug)]
pub enum WindowError {
    /// Accepting this amount would push the window's total over the limit.
    LimitExceeded,
    /// `now` is earlier than a time already recorded.
    ClockWentBack,
}

/// A running total that resets every `len` time units and may never exceed `limit`.
///
/// # Use it for
/// Rate and volume limits: daily withdrawal limits, transfer caps per hour,
/// login attempts per minute, cash-reporting thresholds. Record every request
/// with `try_add(now, amount)` **before** acting on it.
///
/// # Example
/// ```ignore
/// let mut daily = WindowLimit::new(DAY, 10_000_00, now);   // $10,000 per day
/// daily.try_add(now, 6_000_00)?;      // Ok
/// daily.try_add(now, 5_000_00)?;      // Err(LimitExceeded): splitting doesn't help
/// daily.try_add(now + DAY, 5_000_00)?; // Ok: a new window started
/// ```
///
/// # What it proves
/// - **The total in the current window never exceeds the limit**, after any
///   sequence of calls. Splitting one large amount into many small ones
///   doesn't get around it, because the total is a sum.
/// - `try_add` succeeds **exactly** when the time isn't going backwards and the
///   new total fits, and then the total grows by exactly `amount` (or restarts
///   at `amount` in a new window).
/// - A rejected call changes nothing, so a refused transfer doesn't use up
///   any of the limit.
///
/// # What it does NOT prove
/// - Limits over a **sliding** window. Windows here are back-to-back blocks
///   that start at the first request after the previous block ended. Across a
///   block boundary, up to twice the limit can pass within one `len`. Use a
///   sliding-window type if the rule requires "any 24 hours".
/// - Calendar alignment ("per calendar day, midnight to midnight"). Start
///   windows at midnight yourself if that's the rule.
pub struct WindowLimit { len: u64, limit: u64, start: u64, total: u64, last: u64 }

impl Clone for WindowLimit {
    /// Copies the window state, e.g. to try an amount without committing it.
    fn clone(&self) -> (r: Self) ensures r == *self {
        proof { use_type_invariant(self); }
        WindowLimit { len: self.len, limit: self.limit, start: self.start, total: self.total, last: self.last }
    }
}

impl WindowLimit {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.len > 0
        &&& self.total <= self.limit
        &&& self.start <= self.last
    }

    pub closed spec fn len_spec(&self) -> nat { self.len as nat }
    pub closed spec fn limit_spec(&self) -> nat { self.limit as nat }
    pub closed spec fn start_spec(&self) -> nat { self.start as nat }
    pub closed spec fn total_spec(&self) -> nat { self.total as nat }
    pub closed spec fn last_spec(&self) -> nat { self.last as nat }

    /// Whether time `now` still falls in the current window.
    pub open spec fn in_window(&self, now: nat) -> bool {
        now < self.start_spec() + self.len_spec()
    }

    pub fn new(len: u64, limit: u64, now: u64) -> (r: Self)
        requires len > 0,
        ensures r.len_spec() == len, r.limit_spec() == limit,
                r.start_spec() == now, r.last_spec() == now, r.total_spec() == 0,
    { WindowLimit { len, limit, start: now, total: 0, last: now } }

    /// Total so far in the current window. Always within the limit.
    pub fn total(&self) -> (r: u64)
        ensures r as nat == self.total_spec(), r as nat <= self.limit_spec(),
    {
        proof { use_type_invariant(self); }
        self.total
    }

    pub fn try_add(&mut self, now: u64, amount: u64) -> (r: Result<(), WindowError>)
        ensures
            final(self).len_spec() == old(self).len_spec(),
            final(self).limit_spec() == old(self).limit_spec(),
            final(self).total_spec() <= final(self).limit_spec(),
            r is Err ==> *final(self) == *old(self),
            (now as nat) < old(self).last_spec() ==> r is Err,
            r is Ok ==> final(self).last_spec() == now,
            r is Ok && old(self).in_window(now as nat) ==>
                final(self).total_spec() == old(self).total_spec() + amount
                && final(self).start_spec() == old(self).start_spec(),
            r is Ok && !old(self).in_window(now as nat) ==>
                final(self).total_spec() == amount && final(self).start_spec() == now,
            // Exactly when it succeeds:
            (now as nat) >= old(self).last_spec() ==> (r is Ok <==>
                (if old(self).in_window(now as nat) { old(self).total_spec() + amount } else { amount as int })
                    <= old(self).limit_spec()),
    {
        proof { use_type_invariant(&*self); }
        if now < self.last { return Err(WindowError::ClockWentBack); }
        // No underflow: now >= last >= start.
        let in_window = now - self.start < self.len;
        let base = if in_window { self.total } else { 0 };
        // No underflow: base <= total <= limit.
        if amount > self.limit - base { return Err(WindowError::LimitExceeded); }
        let start = if in_window { self.start } else { now };
        *self = WindowLimit { len: self.len, limit: self.limit, start, total: base + amount, last: now };
        Ok(())
    }
}

} // verus!
