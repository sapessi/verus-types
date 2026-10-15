//! Cross-field invariants as a library type.
//!
//! Implement [`Invariant`] for a rule (a spec `holds` plus an exec `check`
//! proved equal to it), then wrap values in [`Checked`]. The rule holds for
//! every value of the wrapped type, and updates are all-or-nothing.

use vstd::prelude::*;
use core::marker::PhantomData;

verus! {

/// A rule over a value of type `T`, given both as a spec (`holds`) and as an
/// executable check (`check`) that is proved equal to the spec.
///
/// # Implementing one
/// - `holds`: the rule, as a quantifier-free boolean over `T`'s fields.
/// - `check`: the same rule in exec code, with `ensures r == Self::holds(*t)`.
///   Usually you write the same expression twice. Verus proves they agree, so
///   the runtime check and the proof always mean the same thing.
/// - Name the type after the rule (`RefundsBounded`, `DatesOrdered`), so a
///   type like `Checked<OrderData, RefundsBounded>` reads as documentation.
pub trait Invariant<T> {
    spec fn holds(t: T) -> bool;
    // The runtime check must be PROVED equal to the spec, so `contracts`-level
    // checking and `full` verification can't drift apart.
    fn check(t: &T) -> (r: bool) ensures r == Self::holds(*t);
}

pub struct Violation;

/// A value of type `T` that always satisfies the rule `I`.
///
/// # Use it for
/// Rules that relate **several fields** and so can't be expressed by one
/// field's type: `refunded <= charged`, `start <= end`, `sum(lines) == total`,
/// `min_replicas <= desired <= max_replicas`. Wrap the struct once, and the
/// rule holds everywhere the wrapped value travels.
///
/// # Example
/// ```ignore
/// type SafeOrder = Checked<OrderData, RefundsBounded>;   // RefundsBounded: an Invariant impl
/// let o: SafeOrder = Checked::new(data).map_err(|_| BadData)?;
///
/// // Multi-field update: the rule may be broken INSIDE `f`, but the result
/// // is committed only if the rule holds again.
/// o.update(|d| OrderData { refunded: d.refunded + amount, ..*d })
///     .map_err(|Violation| ExceedsCharge)?;
///
/// let d = o.get();   // the verifier now knows RefundsBounded::holds(*d)
/// ```
///
/// # What it proves
/// - `new` succeeds **exactly** when the rule holds.
/// - Every `get()` returns a value satisfying the rule (from the type
///   invariant), so readers of a `Checked` never need preconditions about it.
/// - `update` is **all-or-nothing**: on `Ok` the new value is what `f`
///   produced and satisfies the rule; on `Err` the old value is untouched.
///   There's no observable half-updated state.
///
/// # What it does NOT prove
/// - That `f` did what you intended. You get `f.ensures(..)`, so give
///   `f` a spec if callers need to know the exact new value.
/// - Two-state rules ("refunded never decreases"). `I` describes a single
///   value; use `Monotonic`/`WriteOnce` fields for history.
///
/// # Verus notes
/// `update` takes a function `&T -> T`, not `FnOnce(&mut T)`, because Verus
/// reasons about closures over owned values more reliably than about `&mut`
/// closure arguments. The new value is installed by constructing a whole
/// `Checked { .. }`, which is where the type invariant is checked.
///
/// # Cost
/// At runtime, `update` builds a new `T` and calls `I::check` once. For large
/// `T`, wrap only the fields the rule needs instead of the whole struct.
pub struct Checked<T, I: Invariant<T>> { t: T, _i: PhantomData<I> }

impl<T, I: Invariant<T>> View for Checked<T, I> {
    type V = T;
    closed spec fn view(&self) -> T { self.t }
}

impl<T, I: Invariant<T>> Checked<T, I> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool { I::holds(self.t) }

    pub fn new(t: T) -> (r: Result<Self, T>)
        ensures
            match r { Ok(c) => c@ == t && I::holds(t), Err(x) => x == t && !I::holds(t) },
    {
        if I::check(&t) { Ok(Checked { t, _i: PhantomData }) } else { Err(t) }
    }

    pub fn get(&self) -> (r: &T)
        ensures *r == self@, I::holds(*r),
    {
        proof { use_type_invariant(self); }
        &self.t
    }

    // Functional update (f: &T -> T), not `FnOnce(&mut T)`: Verus handles
    // closures over owned values much better than closures taking `&mut`.
    // Commits only if the invariant still holds, so "may break inside, must
    // hold at the end" is guaranteed by construction.
    pub fn update<F: Fn(&T) -> T>(&mut self, f: F) -> (r: Result<(), Violation>)
        requires
            f.requires((&old(self)@,)),          // closure args are passed as a tuple
        ensures
            match r {
                Ok(())  => f.ensures((&old(self)@,), final(self)@) && I::holds(final(self)@),
                Err(_)  => final(self)@ == old(self)@,
            },
    {
        let n = f(&self.t);
        if I::check(&n) {
            *self = Checked { t: n, _i: PhantomData }; // whole-value construction re-checks inv
            Ok(())
        } else {
            Err(Violation)
        }
    }
}

} // verus!
