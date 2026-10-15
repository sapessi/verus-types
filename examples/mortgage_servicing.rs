//! Servicing a funded mortgage with `Monotonic`, `AppendOnly` and `WriteOnce`.
//!
//! Rules:
//!   - total paid only goes up, and never exceeds the principal  (Monotonic)
//!   - the payment history can't be edited                      (AppendOnly)
//!   - the payoff date is recorded once, when the loan is paid off (WriteOnce)
//!   - total paid always equals the sum of the payment history
//!
//! Proved: every method keeps all four rules, and callers can rely on them
//! without reading the method bodies. Run: `cargo run --example mortgage_servicing`

use vstd::prelude::*;
use verus_types::history::{AppendOnly, Monotonic, WriteOnce};

verus! {

#[derive(Copy, Clone, Debug)]
pub struct PaymentRec { pub day: u64, pub cents: u64 }

/// Sum of a payment history (a fold over the sequence).
pub open spec fn total(s: Seq<PaymentRec>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { total(s.drop_last()) + s.last().cents as nat }
}

struct LoanAccount {
    principal: u64,
    paid: Monotonic,
    history: AppendOnly<PaymentRec>,
    paid_off_day: WriteOnce<u64>,
}

#[derive(Debug)]
pub enum PaymentError { Zero, Overpayment, AlreadyPaidOff }

impl LoanAccount {
    /// The account's rules, true whenever an account is visible to callers.
    spec fn wf(&self) -> bool {
        &&& self.principal > 0
        &&& self.paid@ <= self.principal
        &&& self.paid@ == total(self.history@)
        &&& (self.paid_off_day@ is Some <==> self.paid@ == self.principal)
    }

    /// How an account may change between two points in time: history is never
    /// rewritten. Each field's own `evolves` rule, combined.
    spec fn evolves(pre: Self, post: Self) -> bool {
        &&& post.principal == pre.principal
        &&& Monotonic::evolves(pre.paid, post.paid)
        &&& AppendOnly::evolves(pre.history, post.history)
        &&& WriteOnce::evolves(pre.paid_off_day, post.paid_off_day)
    }

    fn open(principal: u64) -> (r: Self)
        requires principal > 0,
        ensures r.wf(), r.paid@ == 0,
    {
        LoanAccount { principal, paid: Monotonic::zero(), history: AppendOnly::new(),
                      paid_off_day: WriteOnce::new() }
    }

    fn apply_payment(&mut self, cents: u64, day: u64) -> (r: Result<(), PaymentError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            Self::evolves(*old(self), *final(self)),
            r is Ok ==> final(self).paid@ == old(self).paid@ + cents,
            r is Err ==> *final(self) == *old(self),
    {
        if cents == 0 { return Err(PaymentError::Zero); }
        if self.paid_off_day.get().is_some() { return Err(PaymentError::AlreadyPaidOff); }
        // No underflow: wf() gives paid <= principal.
        let remaining = self.principal - self.paid.get();
        if cents > remaining { return Err(PaymentError::Overpayment); }

        let ghost old_hist = self.history@;
        let _ = self.paid.add(cents);           // can't overflow: paid + cents <= principal
        self.history.push(PaymentRec { day, cents });
        // Tell Verus the history before the push is exactly the old history,
        // so `total` unfolds by one step.
        proof { assert(self.history@.drop_last() =~= old_hist); }
        if self.paid.get() == self.principal {
            let _ = self.paid_off_day.set(day); // first and only time: wasn't paid off before
        }
        Ok(())
    }

    fn paid(&self) -> (r: u64) ensures r as nat == self.paid@ { self.paid.get() }
    fn paid_off_day(&self) -> (r: Option<&u64>)
        ensures match r { Some(d) => self.paid_off_day@ == Some(*d), None => self.paid_off_day@ is None },
    { self.paid_off_day.get() }
}

/// What a caller can conclude WITHOUT looking inside `apply_payment`.
fn demo_reasoning(acct: &mut LoanAccount)
    requires old(acct).wf(),
{
    let ghost before = acct.paid@;      // ghost: exists only for the proof
    let _ = acct.apply_payment(150_000, 31);
    let _ = acct.apply_payment(150_000, 62);
    // Two calls, any mix of success and failure: total paid never went down.
    assert(acct.paid@ >= before);
    assert(acct.paid@ <= acct.principal);
}

} // verus!

fn main() {
    let mut acct = LoanAccount::open(300_000_00);          // $300,000
    demo_reasoning(&mut acct);
    println!("after two payments: paid ${}", acct.paid() / 100);
    println!("overpayment:  {:?}", acct.apply_payment(400_000_00, 93));
    println!("final payment: {:?}", acct.apply_payment(300_000_00 - acct.paid(), 93));
    println!("paid off on day {:?}", acct.paid_off_day());
    println!("after payoff: {:?}", acct.apply_payment(1, 94));
}
