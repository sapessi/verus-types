//! Integer quantities tagged with a unit, so different kinds can't be mixed.
//!
//! [`Quantity<U>`] rules out silent overflow, mixing units, and scaling that
//! exceeds the original amount. Its only multiplication
//! ([`Quantity::apply_bps`]) carries its own isolated nonlinear proof, so
//! callers reason with linear arithmetic only.

use vstd::prelude::*;
use core::marker::PhantomData;

verus! {

/// Marker trait for units. Each unit is a separate zero-sized type, so
/// quantities of different units have different Rust types and can't be
/// combined by accident.
///
/// Declare a unit with a unit struct:
/// ```ignore
/// pub struct Usd;    impl Unit for Usd {}      // cents
/// pub struct Shares; impl Unit for Shares {}   // whole shares
/// pub struct Kwh;    impl Unit for Kwh {}      // watt-hours
/// ```
/// The library attaches no meaning to the unit. What one count represents
/// (a cent, a share, a watt-hour) is the unit's documentation. Conversion
/// between units should be an explicit, separately verified function.
pub trait Unit {}

/// A non-negative integer amount of unit `U`.
///
/// # Use it for
/// Any countable amount where mixing kinds would be a bug: money (in minor
/// units such as cents), share counts, energy, storage bytes, loyalty points.
/// Never use `f64` for these. Never use a bare `u64` either, because nothing
/// then stops you from adding cents to share counts.
///
/// # Example
/// ```ignore
/// pub struct Usd; impl Unit for Usd {}
/// pub type Money<C> = Quantity<C>;
///
/// let price: Money<Usd> = Quantity::new(19_99);     // $19.99 in cents
/// let fee = price.apply_bps(250);                  // 2.5%, rounded down
/// let total = price.checked_add(fee).ok_or(Overflow)?;
/// let change = paid.checked_sub(total).ok_or(Insufficient)?;
///
/// // let bad = price.checked_add(Quantity::<Shares>::new(5)); // type error
/// // let bad = price * price;                                 // no such operator
/// ```
///
/// # What it proves
/// - **No silent overflow or underflow:** `checked_add`/`checked_sub` return
///   `None` *exactly* when the mathematical result doesn't fit, and otherwise
///   return the exact mathematical sum or difference.
/// - **No unit mixing:** enforced by the type checker, not the verifier.
/// - **Scaling never exceeds the base amount:** `apply_bps` returns
///   `r@ == self@ * bps / 10_000` and `r@ <= self@`.
/// - **Callers stay in linear arithmetic:** the only multiplication happens
///   inside `apply_bps`, whose nonlinear proof is isolated. Callers see only
///   linear facts, which keeps their SMT queries fast and stable.
///
/// # What it does NOT prove
/// - That the **rounding policy** (here: round down) is the one you want.
///   Banker's rounding or round-half-up needs its own verified function.
/// - Negative amounts. Debts and adjustments need a signed type, or a separate
///   debit/credit pair.
/// - Anything about what one count *means* (decimal places of a currency,
///   for example). That belongs to the unit.
///
/// # Verus notes
/// The view is `nat`, so specs read like school arithmetic
/// (`m@ == self@ + o@`). Overflow shows up only as the explicit `> u64::MAX`
/// condition in `checked_add`'s `None` case.
pub struct Quantity<U: Unit> { v: u64, _u: PhantomData<U> }

impl<U: Unit> View for Quantity<U> {
    type V = nat;
    closed spec fn view(&self) -> nat { self.v as nat }
}

impl<U: Unit> Quantity<U> {
    pub fn new(v: u64) -> (r: Self) ensures r@ == v { Quantity { v, _u: PhantomData } }

    pub fn get(&self) -> (r: u64) ensures r == self@ { self.v }

    pub fn checked_add(self, o: Self) -> (r: Option<Self>)
        ensures
            match r {
                Some(m) => m@ == self@ + o@,
                None    => self@ + o@ > u64::MAX,
            },
    {
        match self.v.checked_add(o.v) {
            Some(n) => Some(Quantity { v: n, _u: PhantomData }),
            None => None,
        }
    }

    pub fn checked_sub(self, o: Self) -> (r: Option<Self>)
        ensures
            match r {
                Some(m) => o@ <= self@ && m@ == self@ - o@,
                None    => o@ > self@,
            },
    {
        if o.v <= self.v { Some(Quantity { v: self.v - o.v, _u: PhantomData }) }
        else { None }
    }

    // The ONE place a quantity meets multiplication: basis points (1/100 of a
    // percent), rounded down. Nonlinear arithmetic is confined here; every
    // caller sees only the LINEAR facts in the ensures.
    pub fn apply_bps(self, bps: u16) -> (r: Self)
        requires bps <= 10_000,
        ensures
            r@ == (self@ * bps as nat) / 10_000,
            r@ <= self@,
    {
        let a = self.v;
        proof {
            // Proved once, in isolation, with nonlinear reasoning on.
            assert((a as nat) * (bps as nat) / 10_000 <= a as nat) by (nonlinear_arith)
                requires bps <= 10_000;
            assert((a as nat) * (bps as nat) <= (u64::MAX as nat) * 10_000) by (nonlinear_arith)
                requires bps <= 10_000, a <= u64::MAX;
        }
        let p: u128 = (a as u128) * (bps as u128); // fits: < 2^64 · 2^14
        Quantity { v: (p / 10_000) as u64, _u: PhantomData }
    }
}

} // verus!
