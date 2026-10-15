//! History types: fields whose past can't be rewritten.
//!
//! [`WriteOnce`], [`Monotonic`] and [`AppendOnly`] turn rules about the PAST
//! ("was it ever paid?", "total refunded ever") into facts about the PRESENT
//! value, which the verifier checks with cheap, quantifier-free queries.
//!
//! # Pitfall: methods vs. overwrites
//! These wrappers guard their METHODS, not OVERWRITES. `*w = WriteOnce::new()`
//! or `mem::replace(&mut m, Monotonic::zero())` is legal Rust and resets the
//! history. A type invariant can't forbid it, because type invariants describe
//! a single point in time. The owning struct has to (a) keep the field private
//! and (b) state `WriteOnce::evolves(old(self).f, final(self).f)` in the
//! `ensures` of every `&mut self` method. At the library level this is a
//! convention; the `spec states` design (docs/design.md) enforces it.

use vstd::prelude::*;

verus! {

pub struct AlreadySet;
pub struct Overflow;

// ---- WriteOnce<T> ----------------------------------------------------------

/// A value that can be set **once** and never changed or cleared afterwards.
///
/// # Use it for
/// Recording *that* and *when* something happened: `paid_at`, `shipped_at`,
/// `approved_by`, `cancelled_at`. Wrap a timestamp (or a small record such
/// as `Payment { at, cents }`) and the field becomes a permanent fact about
/// history, stored in the present data.
///
/// This is how rules about the past become cheap checks on the present:
/// "never ship unpaid" becomes `shipped_at.is_some() ==> paid_at.is_some()`,
/// and "paid before shipped" becomes `paid_at <= shipped_at`. Neither needs
/// temporal logic or an event log.
///
/// # Example
/// ```ignore
/// let mut paid_at: WriteOnce<u64> = WriteOnce::new();
/// paid_at.set(now)?;                 // Ok: was empty
/// assert!(paid_at.set(later).is_err()); // second set is rejected, value kept
///
/// // In a proof, anywhere later in the same object's life:
/// proof { assert(paid_at@ == Some(now)); } // follows from `evolves`
/// ```
///
/// # What it proves
/// - `set` succeeds **exactly** when the value was empty, and stores the argument.
/// - A failed `set` leaves the value unchanged (no partial updates).
/// - `WriteOnce::evolves(pre, post)`: once `Some(v)`, it stays `Some(v)`. Cite
///   it in your own `ensures` to tell callers this field's history is preserved.
///
/// # What it does NOT prove
/// - **That nobody overwrote the whole field.** `*f = WriteOnce::new()` and
///   `mem::replace` are legal Rust. Keep the field private, and state
///   `WriteOnce::evolves(old(self).f, final(self).f)` in every `&mut self` method of
///   the owning struct (see the PITFALL note below the impls).
/// - That the value is *correct* (e.g. that `now` is the real time). It records
///   whatever you give it.
///
/// # Verus notes
/// The view is the raw `Option<T>`. Specs use `self@ is None` /
/// `self@ == Some(x)`, which SMT handles with no quantifiers.
pub struct WriteOnce<T> { v: Option<T> }

impl<T> View for WriteOnce<T> {
    type V = Option<T>;
    closed spec fn view(&self) -> Option<T> { self.v }
}

impl<T> WriteOnce<T> {
    // The two-state rule, as a predicate clients can cite in their own specs:
    // "once set, never changes".
    pub open spec fn evolves(pre: Self, post: Self) -> bool {
        pre@ is Some ==> post@ == pre@
    }

    pub fn new() -> (r: Self)
        ensures r@ is None,
    { WriteOnce { v: None } }

    pub fn set(&mut self, x: T) -> (r: Result<(), AlreadySet>)
        ensures
            old(self)@ is None ==> (r is Ok && final(self)@ == Some(x)),
            old(self)@ is Some ==> (r is Err && final(self)@ == old(self)@),
            Self::evolves(*old(self), *final(self)),
    {
        if self.v.is_some() { Err(AlreadySet) } else { self.v = Some(x); Ok(()) }
    }

    pub fn get(&self) -> (r: Option<&T>)
        ensures
            match r { Some(x) => self@ == Some(*x), None => self@ is None },
    { self.v.as_ref() }
}

// ---- Monotonic --------------------------------------------------------------

/// An unsigned counter that can only **increase**.
///
/// # Use it for
/// Running totals and counters whose history matters: `refunded_cents`,
/// `login_failures`, `api_calls_this_period`, sequence numbers, optimistic-lock
/// versions. Because the value never goes down, **the current value IS the
/// all-time total**. "Total refunded ever ≤ charged" is then just
/// `refunded@ <= charged`, with no event log to sum.
///
/// Also the building block for "at most N times" rules: increment on each
/// occurrence and check `count@ <= N`.
///
/// # Example
/// ```ignore
/// let mut refunded = Monotonic::zero();
/// refunded.add(amount)?;            // Err(Overflow) leaves it unchanged
///
/// // A "reset" bug can't be written through the API: there is no `set` or `sub`.
/// // refunded.v = 0;                // private field: doesn't compile
/// ```
///
/// # What it proves
/// - `add(d)` succeeds **exactly** when `old + d` fits in a `u64`, and then
///   the new value is `old + d`.
/// - On overflow the value is unchanged.
/// - `Monotonic::evolves(pre, post)`: `post@ >= pre@`.
///
/// # What it does NOT prove
/// - Protection against whole-field overwrite (same caveat as `WriteOnce`).
/// - Upper bounds. Pair it with an invariant (`Checked`) or a `Bounded` check
///   if the counter must stay below a limit.
///
/// # Verus notes
/// The view is `nat` (a mathematical integer), so specs never mention wrapping.
/// Overflow appears only in the `add` spec, as the explicit condition
/// `old(self)@ + d <= u64::MAX`.
pub struct Monotonic { v: u64 }

impl View for Monotonic {
    type V = nat;
    closed spec fn view(&self) -> nat { self.v as nat }
}

impl Monotonic {
    pub open spec fn evolves(pre: Self, post: Self) -> bool { post@ >= pre@ }

    pub fn zero() -> (r: Self) ensures r@ == 0 { Monotonic { v: 0 } }

    pub fn get(&self) -> (r: u64)
        ensures r as nat == self@,
    { self.v }

    pub fn add(&mut self, d: u64) -> (r: Result<(), Overflow>)
        ensures
            r is Ok  <==> old(self)@ + d <= u64::MAX,
            r is Ok  ==> final(self)@ == old(self)@ + d,
            r is Err ==> final(self)@ == old(self)@,
            Self::evolves(*old(self), *final(self)),
    {
        // Relies on vstd's built-in spec for u64::checked_add.
        match self.v.checked_add(d) {
            Some(n) => { self.v = n; Ok(()) }
            None => Err(Overflow),
        }
    }
}

// ---- AppendOnly<T> ----------------------------------------------------------

/// A sequence that can only grow at the end: no removal, no reordering, no
/// rewriting of existing entries.
///
/// # Use it for
/// Audit logs, ledgers, event histories, approval trails: anything where
/// "what happened" must never be edited after the fact. Combine with a
/// `Monotonic` total to state ledger consistency: "the cached total equals
/// the sum of ledger entries".
///
/// # Example
/// ```ignore
/// let mut ledger: AppendOnly<Refund> = AppendOnly::new();
/// ledger.push(Refund { order: 7, cents: 500 });
/// let first = ledger.get(0);        // requires 0 < len: checked by the verifier
///
/// // A function that only appends can promise this to its callers:
/// fn record(l: &mut AppendOnly<Refund>, r: Refund)
///     ensures AppendOnly::evolves(*old(l), *final(l))   // old history untouched
/// { l.push(r) }
/// ```
///
/// # What it proves
/// - `push(x)`: the new view is exactly `old.push(x)`.
/// - `AppendOnly::evolves(pre, post)`: `pre` is a **prefix** of `post`.
///   Anything you proved about earlier entries stays true forever.
/// - `get(i)` is in bounds (it's a precondition) and returns exactly entry `i`.
///
/// # What it does NOT prove
/// - Durability. An in-memory `AppendOnly` vanishes on restart. For a
///   persistent ledger, the storage layer needs the same prefix guarantee
///   (often an `assume trusted` about the database).
/// - Whole-field overwrite protection (same caveat as `WriteOnce`).
///
/// # Verus notes
/// The view is `Seq<T>`. The prefix property is phrased with `subrange`, so
/// it needs no quantifiers. Facts about *all* entries (e.g. "every refund
/// > 0") should be written as recursive spec functions over the `Seq`
/// (folds, rule L1), not as `forall` invariants.
pub struct AppendOnly<T> { v: Vec<T> }

impl<T> View for AppendOnly<T> {
    type V = Seq<T>;
    closed spec fn view(&self) -> Seq<T> { self.v@ }
}

impl<T> AppendOnly<T> {
    // "Old history is a prefix of new history": nothing rewritten, nothing removed.
    pub open spec fn evolves(pre: Self, post: Self) -> bool {
        pre@.len() <= post@.len() && post@.subrange(0, pre@.len() as int) =~= pre@
    }

    pub fn new() -> (r: Self) ensures r@ == Seq::<T>::empty() { AppendOnly { v: Vec::new() } }

    pub fn push(&mut self, x: T)
        ensures
            final(self)@ == old(self)@.push(x),
            Self::evolves(*old(self), *final(self)),
    {
        self.v.push(x);
        // `==` on Seq needs extensional equality spelled out: "same length
        // and same element at every index". `=~=` asks Verus to prove exactly that.
        proof { assert(self@.subrange(0, old(self)@.len() as int) =~= old(self)@); }
    }

    pub fn len(&self) -> (r: usize) ensures r == self@.len() { self.v.len() }

    pub fn get(&self, i: usize) -> (r: &T)
        requires i < self@.len(),
        ensures *r == self@[i as int],
    { &self.v[i] }
}

} // verus!
