//! Integers whose legal range is part of the type.
//!
//! The range is a type invariant, so every [`Bounded::get`] hands the caller
//! `MIN <= r <= MAX` for free: no re-checks and no annotations at the call site.

use vstd::prelude::*;

verus! {

/// An integer guaranteed to lie in `MIN..=MAX`.
///
/// # Use it for
/// Values with a known legal range: percentages (`Bounded<0, 100>`), basis
/// points (`Bounded<0, 10_000>`), retry counts, page sizes, quantities per
/// order, port numbers. Validate once, at the edge (parsing, deserialization),
/// and every function that receives the value can rely on the range.
///
/// # Example
/// ```ignore
/// type Percent = Bounded<0, 100>;
/// let discount = Percent::new(input).ok_or(BadInput)?;   // the only check
///
/// fn discounted(price: Quantity<Usd>, d: &Percent) -> Quantity<Usd> {
///     // No `requires d <= 100` needed: `get()` provides it.
///     price.apply_bps((d.get() * 100) as u16)   // verifier knows ≤ 10_000
/// }
/// ```
///
/// # What it proves
/// - `new(v)` succeeds **exactly** when `MIN <= v <= MAX`.
/// - **Every** `get()` returns a value with `MIN <= r <= MAX`. The fact comes
///   from the type invariant, so call sites need no `requires` and no
///   re-checks. This removes a whole class of preconditions from your
///   functions.
///
/// # What it does NOT prove
/// - Ranges of *arithmetic results*. `Bounded<0,100> + Bounded<0,100>` can't
///   produce a `Bounded<0,200>` type on stable Rust, so do the arithmetic on
///   `get()` values; the verifier still knows each operand's range.
/// - Anything if values are created without `new` (e.g. a derived
///   `Deserialize`). See "Deserialization" in the crate docs.
///
/// # Verus notes
/// Uses `#[verifier::type_invariant]`. `get` calls `use_type_invariant(self)`
/// to turn the invariant into a fact, then exports it in its `ensures`, so
/// callers never call `use_type_invariant` themselves.
pub struct Bounded<const MIN: u64, const MAX: u64> { v: u64 }

impl<const MIN: u64, const MAX: u64> Bounded<MIN, MAX> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool { MIN <= self.v && self.v <= MAX }

    pub closed spec fn spec_get(self) -> u64 { self.v }

    pub fn new(v: u64) -> (r: Option<Self>)
        ensures
            (MIN <= v && v <= MAX) <==> r is Some,
            r matches Some(b) ==> b.spec_get() == v,
    {
        if MIN <= v && v <= MAX { Some(Bounded { v }) } else { None }
    }

    pub fn get(&self) -> (r: u64)
        ensures r == self.spec_get(), MIN <= r, r <= MAX,
    {
        proof { use_type_invariant(self); }
        self.v
    }
}
// Stable Rust can't compute Bounded<A+C, B+D> as a type (generic_const_exprs
// is unstable), so `Bounded + Bounded` returns a plain checked u64. The value
// is that each OPERAND arrives with its range already proved.
// Const-generic parameters work inside type invariants (verified).

} // verus!
