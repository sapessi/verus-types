//! Layer 2: an audit trail that is append-only and in time order.
//!
//! # Rules (all proved)
//! - **Entries are never edited or removed** (built on `AppendOnly`).
//! - **Entries are in time order:** a new entry can't be timestamped earlier
//!   than the last one. Auditors can read the trail as a timeline, and an
//!   event can't be back-dated into the middle of it.
//! - A rejected entry changes nothing.

use vstd::prelude::*;
use verus_types::history::AppendOnly;

verus! {

#[derive(Copy, Clone, Debug)]
pub enum Action {
    AccountOpened { account: u64, customer: u64 },
    Deposited { account: u64, amount: u64 },
    Transferred { from: u64, to: u64, amount: u64 },
    HoldPlaced { account: u64, amount: u64 },
    HoldCaptured { account: u64, amount: u64 },
    HoldReleased { account: u64, amount: u64 },
    AccountFrozen { account: u64 },
}

#[derive(Copy, Clone, Debug)]
pub struct AuditEvent { pub at: u64, pub action: Action }

/// Every entry is no earlier than the one before it. Defined step by step
/// (not with `forall`), so each new entry needs only one comparison.
pub open spec fn sorted(s: Seq<AuditEvent>) -> bool
    decreases s.len(),
{
    s.len() <= 1 || (sorted(s.drop_last()) && s[s.len() - 2].at <= s.last().at)
}

pub struct ClockWentBack;

pub struct AuditTrail { log: AppendOnly<AuditEvent>, last: u64 }

impl AuditTrail {
    pub closed spec fn events(&self) -> Seq<AuditEvent> { self.log@ }
    pub closed spec fn last_spec(&self) -> u64 { self.last }

    pub closed spec fn wf(&self) -> bool {
        &&& sorted(self.log@)
        &&& (self.log@.len() > 0 ==> self.log@.last().at == self.last)
    }

    pub fn new() -> (r: Self) ensures r.wf(), r.events() == Seq::<AuditEvent>::empty() {
        AuditTrail { log: AppendOnly::new(), last: 0 }
    }

    /// Time of the latest entry (0 if empty). A new entry must not be earlier.
    pub fn last(&self) -> (r: u64) ensures r == self.last_spec() { self.last }

    pub fn record(&mut self, e: AuditEvent) -> (r: Result<(), ClockWentBack>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok <==> e.at >= old(self).last_spec(),
            r is Ok ==> final(self).events() == old(self).events().push(e) && final(self).last_spec() == e.at,
            r is Err ==> final(self).events() == old(self).events() && final(self).last_spec() == old(self).last_spec(),
    {
        if e.at < self.last { return Err(ClockWentBack); }
        self.log.push(e);
        self.last = e.at;
        proof { assert(self.log@.drop_last() =~= old(self).log@); }
        Ok(())
    }
}

} // verus!
