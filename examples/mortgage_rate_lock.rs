//! A mortgage rate lock with `Checked<T, I>`: a rule across several fields.
//!
//! A rate lock guarantees the borrower an interest rate until it expires.
//! Rules, which must hold for every lock at all times:
//!   - it expires after it was locked
//!   - it lasts at most 60 days, plus 15 days per extension
//!   - at most 2 extensions
//!
//! Proved: no `ValidLock` value can ever break the rules, and a failed
//! extension leaves the lock unchanged. Run: `cargo run --example mortgage_rate_lock`

use vstd::prelude::*;
use verus_types::checked::{Checked, Invariant, Violation};

verus! {

pub const DAY: u64 = 86_400;

#[derive(Copy, Clone, Debug)]
pub struct RateLock { pub rate_bps: u64, pub locked_at: u64, pub expires_at: u64, pub extensions: u64 }

/// The rule, once as a spec and once as a runtime check that Verus proves equal.
pub struct LockRules;

impl Invariant<RateLock> for LockRules {
    open spec fn holds(l: RateLock) -> bool {
        &&& l.extensions <= 2
        &&& l.locked_at < l.expires_at
        &&& l.expires_at - l.locked_at <= 60 * DAY + l.extensions * 15 * DAY
    }
    fn check(l: &RateLock) -> (r: bool) ensures r == Self::holds(*l) {
        // Order matters: each test makes the next one's arithmetic safe.
        l.extensions <= 2
            && l.locked_at < l.expires_at
            && l.expires_at - l.locked_at <= 60 * DAY + l.extensions * 15 * DAY
    }
}

pub type ValidLock = Checked<RateLock, LockRules>;

/// Extend a lock by `days`. All-or-nothing: on `Err` the lock is unchanged.
pub fn extend(lock: &mut ValidLock, days: u64) -> (r: Result<(), Violation>)
    ensures
        r is Ok ==> final(lock)@.expires_at == old(lock)@.expires_at + days * DAY
                 && final(lock)@.extensions == old(lock)@.extensions + 1,
        r is Err ==> final(lock)@ == old(lock)@,
        LockRules::holds(final(lock)@),          // the rule holds afterwards, either way
{
    let cur = *lock.get();
    // Reject inputs whose arithmetic could overflow; the rule check does the rest.
    if days > 15 || cur.expires_at > u64::MAX - days * DAY { return Err(Violation); }
    lock.update(|l: &RateLock| -> (n: RateLock)
        requires l.expires_at + days * DAY <= u64::MAX, l.extensions <= 2,
        ensures n.expires_at == l.expires_at + days * DAY, n.extensions == l.extensions + 1,
                n.rate_bps == l.rate_bps, n.locked_at == l.locked_at,
    {
        RateLock { expires_at: l.expires_at + days * DAY, extensions: l.extensions + 1, ..*l }
    })
}

} // verus!

fn main() {
    let now = 1_700_000_000;
    let lock = RateLock { rate_bps: 650, locked_at: now, expires_at: now + 45 * DAY, extensions: 0 };
    let mut lock = ValidLock::new(lock).ok().expect("valid lock");
    println!("locked at 6.50% for 45 days");
    for attempt in 1..=4 {
        let r = extend(&mut lock, 15);
        let l = lock.get();
        println!("extension {attempt}: {:?}  -> {} days, {} extensions",
                 r.map_err(|_| "rejected"), (l.expires_at - l.locked_at) / DAY, l.extensions);
    }
    // Invalid from the start: 90 days with no extensions.
    let bad = RateLock { rate_bps: 650, locked_at: now, expires_at: now + 90 * DAY, extensions: 0 };
    println!("90-day lock valid? {}", ValidLock::new(bad).is_ok());
}
