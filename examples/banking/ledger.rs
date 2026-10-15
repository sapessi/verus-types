//! Layer 2: a ledger whose balances are always the sum of an append-only journal.
//!
//! This is the general-business version: nothing here is specific to banks.
//! The same type tracks inventory, loyalty points or prepaid credit.
//!
//! # Rules (all proved)
//! - **Every balance equals the sum of its journal entries.** The cached
//!   balances can never drift from the journal, which is the audit record.
//! - **Balances never go negative.**
//! - **Transfers conserve value:** the source loses exactly the amount, the
//!   destination gains exactly the amount, every other account is untouched.
//! - **The journal is append-only:** entries are never edited or removed.
//! - **A rejected operation changes nothing.**
//!
//! # The one annotation users write
//! A `Ledger` carries a well-formedness predicate, `wf()`. Every method keeps
//! it, so the only time you mention it is in the signature of your own
//! functions that take `&mut Ledger`:
//! `requires old(l).wf(), ensures final(l).wf()`.
//! (A Verus type invariant would hide even this, but Verus doesn't yet allow
//! growing a `Vec` field of a struct with a type invariant.)

use vstd::prelude::*;
use core::marker::PhantomData;
use verus_types::history::AppendOnly;
use verus_types::id::Id;
use crate::money::{Currency, Money};

verus! {

pub struct AccountTag;
pub type AccountId = Id<AccountTag>;

/// One journal entry. Accounts are referred to by their id number.
#[derive(Copy, Clone, Debug)]
pub enum Entry {
    Deposit { to: u64, amount: u64 },
    Withdrawal { from: u64, amount: u64 },
    Transfer { from: u64, to: u64, amount: u64 },
}

/// How much an entry changes account `a`'s balance.
pub open spec fn delta(e: Entry, a: u64) -> int {
    match e {
        Entry::Deposit { to, amount } => if to == a { amount as int } else { 0 },
        Entry::Withdrawal { from, amount } => if from == a { -(amount as int) } else { 0 },
        Entry::Transfer { from, to, amount } =>
            (if to == a { amount as int } else { 0 }) - (if from == a { amount as int } else { 0 }),
    }
}

/// Account `a`'s balance according to the journal: the sum of all its entries.
pub open spec fn net(s: Seq<Entry>, a: u64) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { net(s.drop_last(), a) + delta(s.last(), a) }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LedgerError { NoSuchAccount, SameAccount, InsufficientFunds, Overflow }

pub struct Ledger<C: Currency> {
    journal: AppendOnly<Entry>,
    balances: Vec<u64>,
    _c: PhantomData<C>,
}

impl<C: Currency> Ledger<C> {
    pub closed spec fn journal(&self) -> Seq<Entry> { self.journal@ }
    pub closed spec fn accounts(&self) -> nat { self.balances@.len() }
    closed spec fn cached(&self, a: u64) -> int { self.balances@[a as int] as int }

    /// An account's balance, by definition the sum of its journal entries.
    pub open spec fn balance(&self, a: AccountId) -> int { net(self.journal(), a@) }

    pub open spec fn exists(&self, a: AccountId) -> bool { (a@ as nat) < self.accounts() }

    pub closed spec fn wf(&self) -> bool {
        &&& self.accounts() <= u64::MAX
        &&& forall|a: u64| (a as nat) < self.accounts() ==>
                #[trigger] self.cached(a) == net(self.journal(), a) && net(self.journal(), a) >= 0
        &&& forall|a: u64| (a as nat) >= self.accounts() ==> #[trigger] net(self.journal(), a) == 0
    }

    pub fn new() -> (r: Self)
        ensures r.wf(), r.accounts() == 0, r.journal() == Seq::<Entry>::empty(),
    {
        Ledger { journal: AppendOnly::new(), balances: Vec::new(), _c: PhantomData }
    }

    /// Open a new account with balance zero.
    pub fn open_account(&mut self) -> (r: Option<AccountId>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).journal() == old(self).journal(),
            match r {
                Some(a) => a@ == old(self).accounts() && final(self).accounts() == old(self).accounts() + 1
                           && final(self).balance(a) == 0,
                None => *final(self) == *old(self),
            },
    {
        if self.balances.len() as u64 == u64::MAX { return None; }
        let id = self.balances.len() as u64;
        self.balances.push(0);
        proof {
            let j = old(self).journal();
            assert(self.journal() == j);
            assert(self.accounts() == old(self).accounts() + 1);
            // Existing accounts keep their balance; the new one starts at 0
            // (no journal entry ever mentioned it).
            assert forall|a: u64| (a as nat) < self.accounts() implies
                #[trigger] self.cached(a) == net(self.journal(), a) && net(self.journal(), a) >= 0 by {
                if a == id { assert(net(j, a) == 0); }
                else { assert(old(self).cached(a) == net(j, a)); assert(old(self).cached(a) == self.cached(a)); }
            }
            assert forall|a: u64| (a as nat) >= self.accounts() implies #[trigger] net(self.journal(), a) == 0 by {
                assert(net(j, a) == 0);
            }
            assert(self.wf());
        }
        Some(AccountId::new(id))
    }

    /// The current balance (O(1): read from the cache the proof keeps in sync).
    pub fn balance_of(&self, a: AccountId) -> (r: Result<Money<C>, LedgerError>)
        requires self.wf(),
        ensures
            r is Ok <==> self.exists(a),
            r matches Ok(m) ==> m@ == self.balance(a),
    {
        if a.get() >= self.balances.len() as u64 { return Err(LedgerError::NoSuchAccount); }
        let b = self.balances[a.get() as usize];
        proof { assert(self.cached(a@) == net(self.journal(), a@)); }   // name the account for the solver
        Ok(Money::new(b))
    }

    pub fn deposit(&mut self, to: AccountId, amount: Money<C>) -> (r: Result<(), LedgerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).accounts() == old(self).accounts(),
            r is Err ==> *final(self) == *old(self),
            r is Ok ==> final(self).journal() == old(self).journal().push(Entry::Deposit { to: to@, amount: amount@ as u64 }),
            r is Ok ==> final(self).balance(to) == old(self).balance(to) + amount@,
            r is Ok ==> forall|a: AccountId| a@ != to@ ==> #[trigger] final(self).balance(a) == old(self).balance(a),
            r is Ok <==> old(self).exists(to) && old(self).balance(to) + amount@ <= u64::MAX,
    {
        let (t, amt) = (to.get(), amount.get());
        if t >= self.balances.len() as u64 { return Err(LedgerError::NoSuchAccount); }
        let tb = self.balances[t as usize];
        proof { assert(self.cached(t) == net(self.journal(), t)); }
        if tb > u64::MAX - amt { return Err(LedgerError::Overflow); }
        self.balances.set(t as usize, tb + amt);
        self.journal.push(Entry::Deposit { to: t, amount: amt });
        proof { self.prove_step(old(self), Entry::Deposit { to: t, amount: amt }); }
        Ok(())
    }

    pub fn withdraw(&mut self, from: AccountId, amount: Money<C>) -> (r: Result<(), LedgerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).accounts() == old(self).accounts(),
            r is Err ==> *final(self) == *old(self),
            r is Ok ==> final(self).journal() == old(self).journal().push(Entry::Withdrawal { from: from@, amount: amount@ as u64 }),
            r is Ok ==> final(self).balance(from) == old(self).balance(from) - amount@,
            r is Ok ==> forall|a: AccountId| a@ != from@ ==> #[trigger] final(self).balance(a) == old(self).balance(a),
            r is Ok <==> old(self).exists(from) && old(self).balance(from) >= amount@,
    {
        let (f, amt) = (from.get(), amount.get());
        if f >= self.balances.len() as u64 { return Err(LedgerError::NoSuchAccount); }
        let fb = self.balances[f as usize];
        proof { assert(self.cached(f) == net(self.journal(), f)); }
        if fb < amt { return Err(LedgerError::InsufficientFunds); }
        self.balances.set(f as usize, fb - amt);
        self.journal.push(Entry::Withdrawal { from: f, amount: amt });
        proof { self.prove_step(old(self), Entry::Withdrawal { from: f, amount: amt }); }
        Ok(())
    }

    /// Move `amount` from one account to another. **Conserves value.**
    pub fn transfer(&mut self, from: AccountId, to: AccountId, amount: Money<C>) -> (r: Result<(), LedgerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).accounts() == old(self).accounts(),
            r is Err ==> *final(self) == *old(self),
            r is Ok ==> final(self).journal() == old(self).journal().push(
                Entry::Transfer { from: from@, to: to@, amount: amount@ as u64 }),
            // Conservation: exactly `amount` moves, and nothing else changes.
            r is Ok ==> final(self).balance(from) == old(self).balance(from) - amount@,
            r is Ok ==> final(self).balance(to) == old(self).balance(to) + amount@,
            r is Ok ==> forall|a: AccountId| a@ != from@ && a@ != to@ ==>
                #[trigger] final(self).balance(a) == old(self).balance(a),
            r is Ok <==> old(self).exists(from) && old(self).exists(to) && from@ != to@
                         && old(self).balance(from) >= amount@
                         && old(self).balance(to) + amount@ <= u64::MAX,
    {
        let (f, t, amt) = (from.get(), to.get(), amount.get());
        if f >= self.balances.len() as u64 || t >= self.balances.len() as u64 {
            return Err(LedgerError::NoSuchAccount);
        }
        if f == t { return Err(LedgerError::SameAccount); }
        let fb = self.balances[f as usize];
        let tb = self.balances[t as usize];
        proof {
            assert(self.cached(f) == net(self.journal(), f));
            assert(self.cached(t) == net(self.journal(), t));
        }
        if fb < amt { return Err(LedgerError::InsufficientFunds); }
        if tb > u64::MAX - amt { return Err(LedgerError::Overflow); }
        self.balances.set(f as usize, fb - amt);
        self.balances.set(t as usize, tb + amt);
        self.journal.push(Entry::Transfer { from: f, to: t, amount: amt });
        proof { self.prove_step(old(self), Entry::Transfer { from: f, to: t, amount: amt }); }
        Ok(())
    }

    /// Shared proof step: after appending `e` and updating the touched cached
    /// balances by `delta(e, _)`, the ledger is well-formed again.
    proof fn prove_step(&self, pre: &Self, e: Entry)
        requires
            pre.wf(),
            self.journal() == pre.journal().push(e),
            self.accounts() == pre.accounts(),
            forall|a: u64| (a as nat) < self.accounts() ==>
                #[trigger] self.cached(a) == pre.cached(a) + delta(e, a) && self.cached(a) >= 0,
            forall|a: u64| (a as nat) >= self.accounts() ==> #[trigger] delta(e, a) == 0,
        ensures self.wf(),
    {
        assert(self.journal().drop_last() =~= pre.journal());
        assert forall|a: u64| (a as nat) < self.accounts() implies
            #[trigger] self.cached(a) == net(self.journal(), a) && net(self.journal(), a) >= 0 by {
            assert(net(self.journal(), a) == net(pre.journal(), a) + delta(e, a));
            assert(pre.cached(a) == net(pre.journal(), a));
        }
        assert forall|a: u64| (a as nat) >= self.accounts() implies #[trigger] net(self.journal(), a) == 0 by {
            assert(net(self.journal(), a) == net(pre.journal(), a) + delta(e, a));
        }
    }
}

} // verus!
