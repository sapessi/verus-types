//! Layer 3: a bank built from the Layer 1 and 2 types.
//!
//! # Rules (all proved, for every sequence of calls)
//! - **Money is conserved:** a transfer takes exactly the amount from one
//!   account and adds it to the other; no other balance changes.
//! - **Transfers happen at most once per idempotency key:** a retry returns
//!   the original outcome and moves no money.
//! - **No spending of held funds:** card authorizations ("holds") reserve
//!   money; transfers and new holds can use only the *available* balance
//!   (balance minus holds), and holds never exceed the balance.
//! - **Daily outgoing limit** per account. Splitting a transfer doesn't get
//!   around it, and rejected transfers don't use it up.
//! - **Large transfers need four-eyes approval** for that specific transfer.
//! - **Frozen accounts can't move money.**
//! - **Accounts exist only for KYC-verified customers** (a type: `&Customer<Verified>`).
//! - **Every money movement is in the audit trail**, in time order.
//!
//! Callers write one annotation: functions that take `&mut Bank` state
//! `requires old(bank).wf(), ensures final(bank).wf()`.

use vstd::prelude::*;
use verus_types::idempotent::IdempotencyLog;
use verus_types::window::WindowLimit;
use crate::audit::{Action, AuditEvent, AuditTrail};
use crate::customer::{Customer, Verified};
use crate::four_eyes::Approval;
use crate::ledger::{AccountId, Ledger, LedgerError};
#[cfg(verus_only)] // used only in specs and proofs: erased in a plain cargo build
use crate::ledger::{delta, net, Entry};
use crate::money::{Currency, Money};

verus! {

pub const DAY: u64 = 86_400;
/// Outgoing limit per account per day: $10,000.00.
pub const DAILY_LIMIT: u64 = 1_000_000;
/// Transfers above $5,000.00 need maker-checker approval.
pub const LARGE: u64 = 500_000;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Rejection {
    NoSuchAccount, Frozen, InsufficientAvailable, DailyLimit, NeedsApproval,
    ClockWentBack, Ledger(LedgerError),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Outcome { Done, Rejected(Rejection) }

pub struct Bank<C: Currency> {
    ledger: Ledger<C>,
    holds: Vec<u64>,
    frozen: Vec<bool>,
    limits: Vec<WindowLimit>,
    owners: Vec<u64>,
    transfers: IdempotencyLog<Outcome>,
    audit: AuditTrail,
}

/// Appending one entry changes each balance by exactly that entry's `delta`.
pub proof fn lemma_net_push(s: Seq<Entry>, e: Entry, a: u64)
    ensures net(s.push(e), a) == net(s, a) + delta(e, a),
{
    assert(s.push(e).drop_last() =~= s);
}

impl<C: Currency> Bank<C> {
    // ---- What callers can talk about --------------------------------------
    pub closed spec fn ledger_spec(&self) -> Ledger<C> { self.ledger }
    pub closed spec fn held(&self, a: u64) -> nat { self.holds@[a as int] as nat }
    pub closed spec fn is_frozen(&self, a: u64) -> bool { self.frozen@[a as int] }
    pub closed spec fn owner(&self, a: u64) -> u64 { self.owners@[a as int] }
    pub closed spec fn log_spec(&self) -> IdempotencyLog<Outcome> { self.transfers }
    /// The audit trail's entries, oldest first.
    pub closed spec fn audit_events(&self) -> Seq<AuditEvent> { self.audit.events() }
    /// Account `a`'s outgoing-limit window (total sent so far in the current day).
    pub closed spec fn window(&self, a: u64) -> WindowLimit { self.limits@[a as int] }

    pub open spec fn journal(&self) -> Seq<Entry> { self.ledger_spec().journal() }
    pub open spec fn accounts(&self) -> nat { self.ledger_spec().accounts() }
    pub open spec fn balance(&self, a: u64) -> int { net(self.journal(), a) }
    pub open spec fn available(&self, a: u64) -> int { self.balance(a) - self.held(a) }
    /// The recorded outcome for an idempotency key, if that key was used before.
    pub open spec fn seen(&self, key: u64) -> Option<Outcome> { self.log_spec().get(key) }

    pub closed spec fn wf(&self) -> bool {
        &&& self.ledger.wf()
        &&& self.audit.wf()
        &&& self.holds@.len() == self.ledger.accounts()
        &&& self.frozen@.len() == self.ledger.accounts()
        &&& self.limits@.len() == self.ledger.accounts()
        &&& self.owners@.len() == self.ledger.accounts()
        &&& forall|a: u64| (a as nat) < self.ledger.accounts() ==>
                #[trigger] self.held(a) <= net(self.ledger.journal(), a)
        &&& self.limits_ok()
    }

    /// Every account's window enforces the bank's daily limit.
    pub closed spec fn limits_ok(&self) -> bool {
        forall|a: u64| (a as nat) < self.limits@.len() ==>
            #[trigger] self.limits@[a as int].limit_spec() == DAILY_LIMIT as nat
    }

    /// Unchanged windows still enforce the limit.
    proof fn lemma_limits_frame(&self, pre: &Self)
        requires pre.limits_ok(), self.limits@ == pre.limits@,
        ensures self.limits_ok(),
    {
        assert forall|a: u64| (a as nat) < self.limits@.len() implies
            #[trigger] self.limits@[a as int].limit_spec() == DAILY_LIMIT as nat by {
            assert(pre.limits@[a as int].limit_spec() == DAILY_LIMIT as nat);
        }
    }

    pub fn new() -> (r: Self) ensures r.wf(), r.accounts() == 0 {
        Bank { ledger: Ledger::new(), holds: Vec::new(), frozen: Vec::new(), limits: Vec::new(),
               owners: Vec::new(), transfers: IdempotencyLog::new(), audit: AuditTrail::new() }
    }

    // ---- Accounts ---------------------------------------------------------

    /// Open an account. Only possible for a KYC-verified customer: the type says so.
    pub fn open_account(&mut self, customer: &Customer<Verified>, now: u64) -> (r: Result<AccountId, Rejection>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(a) ==> final(self).owner(a@) == customer@.id && final(self).balance(a@) == 0
                                && !final(self).is_frozen(a@),
            r is Err ==> final(self).journal() == old(self).journal(),
    {
        if now < self.audit.last() { return Err(Rejection::ClockWentBack); }
        let ghost j = self.ledger.journal();
        let a = match self.ledger.open_account() { Some(a) => a, None => return Err(Rejection::NoSuchAccount) };
        self.holds.push(0);
        self.frozen.push(false);
        self.limits.push(WindowLimit::new(DAY, DAILY_LIMIT, now));
        self.owners.push(customer.get().id);
        let _ = self.audit.record(AuditEvent { at: now, action: Action::AccountOpened { account: a.get(), customer: customer.get().id } });
        proof {
            assert forall|x: u64| (x as nat) < self.ledger.accounts() implies
                #[trigger] self.held(x) <= net(self.ledger.journal(), x) by {
                if x != a@ { assert(old(self).held(x) <= net(j, x)); }
            }
            assert forall|x: u64| (x as nat) < self.limits@.len() implies
                #[trigger] self.limits@[x as int].limit_spec() == DAILY_LIMIT as nat by {
                if x != a@ { assert(old(self).limits@[x as int].limit_spec() == DAILY_LIMIT as nat); }
            }
        }
        Ok(a)
    }

    pub fn freeze(&mut self, a: AccountId, now: u64) -> (r: Result<(), Rejection>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).journal() == old(self).journal(),
            r is Ok ==> final(self).is_frozen(a@),
    {
        let i = a.get();
        if i >= self.frozen.len() as u64 { return Err(Rejection::NoSuchAccount); }
        if now < self.audit.last() { return Err(Rejection::ClockWentBack); }
        self.frozen.set(i as usize, true);
        let _ = self.audit.record(AuditEvent { at: now, action: Action::AccountFrozen { account: i } });
        proof { self.lemma_frame(old(self)); }
        Ok(())
    }

    pub fn balance_of(&self, a: AccountId) -> (r: Result<Money<C>, Rejection>)
        requires self.wf(),
        ensures r matches Ok(m) ==> m@ == self.balance(a@),
    {
        match self.ledger.balance_of(a) { Ok(m) => Ok(m), Err(_) => Err(Rejection::NoSuchAccount) }
    }

    pub fn held_of(&self, a: AccountId) -> (r: Result<u64, Rejection>)
        requires self.wf(),
        ensures r matches Ok(h) ==> h as nat == self.held(a@),
    {
        if a.get() >= self.holds.len() as u64 { return Err(Rejection::NoSuchAccount); }
        Ok(self.holds[a.get() as usize])
    }

    // ---- Cash in ------------------------------------------------------------

    pub fn deposit(&mut self, a: AccountId, amount: Money<C>, now: u64) -> (r: Result<(), Rejection>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).balance(a@) == old(self).balance(a@) + amount@,
            r is Ok ==> final(self).audit_events() == old(self).audit_events().push(
                AuditEvent { at: now, action: Action::Deposited { account: a@, amount: amount@ as u64 } }),
            r is Err ==> final(self).journal() == old(self).journal(),
    {
        let i = a.get();
        if i >= self.frozen.len() as u64 { return Err(Rejection::NoSuchAccount); }
        if self.frozen[i as usize] { return Err(Rejection::Frozen); }
        if now < self.audit.last() { return Err(Rejection::ClockWentBack); }
        let ghost j = self.ledger.journal();
        let amt = amount.get();
        if let Err(e) = self.ledger.deposit(a, amount) { return Err(Rejection::Ledger(e)); }
        let _ = self.audit.record(AuditEvent { at: now, action: Action::Deposited { account: i, amount: amt } });
        proof {
            self.lemma_limits_frame(old(self));
            self.lemma_holds_after(old(self), j, Entry::Deposit { to: i, amount: amt });
        }
        Ok(())
    }

    // ---- Card holds -----------------------------------------------------------

    /// Reserve `amount` for a card authorization. Uses only available funds.
    pub fn place_hold(&mut self, a: AccountId, amount: u64, now: u64) -> (r: Result<(), Rejection>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).journal() == old(self).journal(),
            r is Ok ==> old(self).available(a@) >= amount && final(self).held(a@) == old(self).held(a@) + amount,
    {
        let i = a.get();
        if i >= self.holds.len() as u64 { return Err(Rejection::NoSuchAccount); }
        if self.frozen[i as usize] { return Err(Rejection::Frozen); }
        if now < self.audit.last() { return Err(Rejection::ClockWentBack); }
        let bal = match self.ledger.balance_of(a) { Ok(m) => m.get(), Err(_) => return Err(Rejection::NoSuchAccount) };
        let h = self.holds[i as usize];
        proof { assert(self.held(i) <= net(self.ledger.journal(), i)); }
        if amount > bal - h { return Err(Rejection::InsufficientAvailable); }
        self.holds.set(i as usize, h + amount);
        let _ = self.audit.record(AuditEvent { at: now, action: Action::HoldPlaced { account: i, amount } });
        proof {
            self.lemma_limits_frame(old(self));
            assert forall|x: u64| (x as nat) < self.ledger.accounts() implies
                #[trigger] self.held(x) <= net(self.ledger.journal(), x) by {
                if x != i { assert(old(self).held(x) <= net(self.ledger.journal(), x)); }
            }
        }
        Ok(())
    }

    /// The merchant settles: the held amount leaves the account.
    pub fn capture_hold(&mut self, a: AccountId, amount: u64, now: u64) -> (r: Result<(), Rejection>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).balance(a@) == old(self).balance(a@) - amount
                        && final(self).held(a@) == old(self).held(a@) - amount
                        && final(self).audit_events() == old(self).audit_events().push(
                            AuditEvent { at: now, action: Action::HoldCaptured { account: a@, amount } }),
            r is Err ==> final(self).journal() == old(self).journal(),
    {
        let i = a.get();
        if i >= self.holds.len() as u64 { return Err(Rejection::NoSuchAccount); }
        if now < self.audit.last() { return Err(Rejection::ClockWentBack); }
        let h = self.holds[i as usize];
        if amount > h { return Err(Rejection::InsufficientAvailable); }
        let ghost j = self.ledger.journal();
        proof { assert(self.held(i) <= net(j, i)); }
        // Can't fail: balance >= held >= amount.
        if let Err(e) = self.ledger.withdraw(a, Money::new(amount)) { return Err(Rejection::Ledger(e)); }
        self.holds.set(i as usize, h - amount);
        let _ = self.audit.record(AuditEvent { at: now, action: Action::HoldCaptured { account: i, amount } });
        proof {
            self.lemma_limits_frame(old(self));
            let e = Entry::Withdrawal { from: i, amount };
            assert forall|x: u64| (x as nat) < self.ledger.accounts() implies
                #[trigger] self.held(x) <= net(self.ledger.journal(), x) by {
                lemma_net_push(j, e, x);
                assert(old(self).held(x) <= net(j, x));
            }
        }
        Ok(())
    }

    /// The authorization expired or was cancelled: the funds become available again.
    pub fn release_hold(&mut self, a: AccountId, amount: u64, now: u64) -> (r: Result<(), Rejection>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).journal() == old(self).journal(),
            r is Ok ==> final(self).held(a@) == old(self).held(a@) - amount,
    {
        let i = a.get();
        if i >= self.holds.len() as u64 { return Err(Rejection::NoSuchAccount); }
        if now < self.audit.last() { return Err(Rejection::ClockWentBack); }
        let h = self.holds[i as usize];
        if amount > h { return Err(Rejection::InsufficientAvailable); }
        self.holds.set(i as usize, h - amount);
        let _ = self.audit.record(AuditEvent { at: now, action: Action::HoldReleased { account: i, amount } });
        proof {
            self.lemma_limits_frame(old(self));
            assert forall|x: u64| (x as nat) < self.ledger.accounts() implies
                #[trigger] self.held(x) <= net(self.ledger.journal(), x) by {
                assert(old(self).held(x) <= net(self.ledger.journal(), x));
            }
        }
        Ok(())
    }

    // ---- Transfers ------------------------------------------------------------

    /// Transfer up to `LARGE`. Larger amounts are refused (not recorded), so the
    /// client can retry with the same key through `transfer_approved`.
    pub fn transfer(&mut self, key: u64, from: AccountId, to: AccountId, amount: Money<C>, now: u64) -> (r: Outcome)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            Self::transfer_spec(*old(self), *final(self), key, from@, to@, amount@, r),
            amount@ > LARGE && old(self).seen(key) is None ==>
                r == Outcome::Rejected(Rejection::NeedsApproval) && final(self).journal() == old(self).journal()
                && final(self).seen(key) is None,
    {
        if amount.get() > LARGE {
            if let Some(prev) = self.transfers.lookup(key) { return prev; }
            return Outcome::Rejected(Rejection::NeedsApproval);
        }
        self.execute(key, from, to, amount, now)
    }

    /// Transfer of any size, with a four-eyes approval for **this** request.
    /// The approval is consumed: one approval, one transfer.
    #[allow(unused_variables)] // `approval` exists only for the proof
    pub fn transfer_approved(&mut self, key: u64, from: AccountId, to: AccountId, amount: Money<C>, now: u64,
                             approval: Tracked<Approval>) -> (r: Outcome)
        requires old(self).wf(), approval@.request() == key,
        ensures final(self).wf(), Self::transfer_spec(*old(self), *final(self), key, from@, to@, amount@, r),
    {
        self.execute(key, from, to, amount, now)
    }

    /// What every transfer guarantees.
    pub open spec fn transfer_spec(pre: Self, post: Self, key: u64, from: u64, to: u64, amount: nat, r: Outcome) -> bool {
        // A retry returns the original outcome and changes nothing.
        &&& pre.seen(key) matches Some(p) ==> r == p && post.journal() == pre.journal()
        // A new key gets its outcome recorded.
        &&& (pre.seen(key) is None && r != Outcome::Rejected(Rejection::NeedsApproval)) ==> post.seen(key) == Some(r)
        // Rejected: no money moves.
        &&& r is Rejected ==> post.journal() == pre.journal()
        // Done (first time): exactly `amount` moves from `from` to `to`, nothing else changes.
        &&& (r is Done && pre.seen(key) is None) ==> {
                &&& post.journal() == pre.journal().push(Entry::Transfer { from, to, amount: amount as u64 })
                &&& post.balance(from) == pre.balance(from) - amount
                &&& post.balance(to) == pre.balance(to) + amount
                &&& pre.available(from) >= amount
                &&& !pre.is_frozen(from) && !pre.is_frozen(to)
                // The amount counts toward today's limit, which still holds.
                &&& post.window(from).total_spec() >= amount
                &&& post.window(from).total_spec() <= DAILY_LIMIT
                // It's in the audit trail.
                &&& post.audit_events().len() == pre.audit_events().len() + 1
                &&& post.audit_events().last().action == (Action::Transferred { from, to, amount: amount as u64 })
            }
    }

    fn execute(&mut self, key: u64, from: AccountId, to: AccountId, amount: Money<C>, now: u64) -> (r: Outcome)
        requires old(self).wf(),
        ensures final(self).wf(), Self::transfer_spec(*old(self), *final(self), key, from@, to@, amount@, r),
    {
        if let Some(prev) = self.transfers.lookup(key) { return prev; }
        let _amt = amount.get();   // tells the verifier the amount fits in a u64
        let r = match self.move_money(from, to, amount, now) {
            Ok(()) => Outcome::Done,
            Err(e) => Outcome::Rejected(e),
        };
        let ghost mid = *self;
        self.transfers.record(key, r);
        proof {
            self.lemma_frame(&mid);   // only the idempotency log changed
            if r is Done {
                let e = Entry::Transfer { from: from@, to: to@, amount: amount@ as u64 };
                lemma_net_push(old(self).journal(), e, from@);
                lemma_net_push(old(self).journal(), e, to@);
            }
        }
        r
    }

    fn move_money(&mut self, from: AccountId, to: AccountId, amount: Money<C>, now: u64) -> (r: Result<(), Rejection>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).log_spec() == old(self).log_spec(),
            r is Err ==> final(self).journal() == old(self).journal() && r != Err::<(), Rejection>(Rejection::NeedsApproval),
            r is Ok ==> final(self).journal() == old(self).journal().push(
                Entry::Transfer { from: from@, to: to@, amount: amount@ as u64 })
                && old(self).available(from@) >= amount@ && from@ != to@
                && !old(self).is_frozen(from@) && !old(self).is_frozen(to@)
                && final(self).window(from@).total_spec() >= amount@
                && final(self).window(from@).total_spec() <= DAILY_LIMIT
                && final(self).audit_events().len() == old(self).audit_events().len() + 1
                && final(self).audit_events().last().action
                    == (Action::Transferred { from: from@, to: to@, amount: amount@ as u64 }),
    {
        let (f, t, amt) = (from.get(), to.get(), amount.get());
        let n = self.holds.len() as u64;
        if f >= n || t >= n { return Err(Rejection::NoSuchAccount); }
        if self.frozen[f as usize] || self.frozen[t as usize] { return Err(Rejection::Frozen); }
        if now < self.audit.last() { return Err(Rejection::ClockWentBack); }
        let bal = match self.ledger.balance_of(from) { Ok(m) => m.get(), Err(_) => return Err(Rejection::NoSuchAccount) };
        let h = self.holds[f as usize];
        proof { assert(self.held(f) <= net(self.ledger.journal(), f)); }
        if amt > bal - h { return Err(Rejection::InsufficientAvailable); }
        // Try the limit on a copy; keep it only if the transfer succeeds.
        let mut lim = self.limits[f as usize].clone();
        if lim.try_add(now, amt).is_err() { return Err(Rejection::DailyLimit); }
        let ghost j = self.ledger.journal();
        if let Err(e) = self.ledger.transfer(from, to, amount) { return Err(Rejection::Ledger(e)); }
        self.limits.set(f as usize, lim);
        proof {
            assert(old(self).limits@[f as int].limit_spec() == DAILY_LIMIT as nat);
            assert forall|a: u64| (a as nat) < self.limits@.len() implies
                #[trigger] self.limits@[a as int].limit_spec() == DAILY_LIMIT as nat by {
                if a != f { assert(old(self).limits@[a as int].limit_spec() == DAILY_LIMIT as nat); }
            }
        }
        let _ = self.audit.record(AuditEvent { at: now, action: Action::Transferred { from: f, to: t, amount: amt } });
        proof { self.lemma_holds_after(old(self), j, Entry::Transfer { from: f, to: t, amount: amt }); }
        Ok(())
    }

    /// If the ledger and the holds didn't change, the bank is still well-formed.
    proof fn lemma_frame(&self, pre: &Self)
        requires
            pre.wf(),
            self.ledger == pre.ledger,
            self.audit.wf(),
            self.holds@ == pre.holds@,
            self.frozen@.len() == pre.frozen@.len(),
            self.limits@ == pre.limits@,
            self.owners@.len() == pre.owners@.len(),
        ensures self.wf(),
    {
        self.lemma_limits_frame(pre);
        assert forall|x: u64| (x as nat) < self.ledger.accounts() implies
            #[trigger] self.held(x) <= net(self.ledger.journal(), x) by {
            assert(pre.held(x) <= net(pre.ledger.journal(), x));
            assert(self.held(x) == pre.held(x));
        }
    }

    /// After one ledger entry `e`, holds still fit within balances, provided
    /// `e` doesn't take more than the available funds of any account.
    proof fn lemma_holds_after(&self, pre: &Self, j: Seq<Entry>, e: Entry)
        requires
            pre.wf(),
            j == pre.ledger.journal(),
            self.ledger.wf(), self.audit.wf(),
            self.ledger.journal() == j.push(e),
            self.ledger.accounts() == pre.ledger.accounts(),
            self.holds@ == pre.holds@,
            self.frozen@.len() == pre.frozen@.len(),
            self.limits@.len() == pre.limits@.len(),
            self.limits_ok(),
            self.owners@ == pre.owners@,
            forall|x: u64| (x as nat) < self.ledger.accounts() ==>
                #[trigger] delta(e, x) >= 0 || pre.held(x) as int <= net(j, x) + delta(e, x),
        ensures self.wf(),
    {
        assert forall|x: u64| (x as nat) < self.ledger.accounts() implies
            #[trigger] self.held(x) <= net(self.ledger.journal(), x) by {
            lemma_net_push(j, e, x);
            assert(pre.held(x) <= net(j, x));
            assert(self.held(x) == pre.held(x));
        }
    }
}

} // verus!
