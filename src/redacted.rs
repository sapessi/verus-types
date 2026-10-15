//! Sensitive values that don't leak through logs or debug output.

use vstd::prelude::*;

verus! {

/// A sensitive value that never prints as itself. How it *does* print is
/// decided by its type, through the [`Mask`] trait.
///
/// # Use it for
/// Personal or secret data that must not appear in logs, error messages or
/// debug output: tax ids, account numbers, card numbers, dates of birth. Give
/// each kind of data its own type and decide **once** how it's shown:
///
/// ```ignore
/// pub struct TaxId(pub u64);
/// impl Mask for TaxId {
///     fn fmt_masked(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
///         write!(f, "***-**-{:04}", self.0 % 10_000)        // shows only the last 4 digits
///     }
/// }
///
/// let ssn: Redacted<TaxId> = Redacted::new(TaxId(form.ssn));
/// log::info!("applicant {:?}", ssn);                 // logs "***-**-6789"
/// credit_bureau.pull(ssn.expose());                  // the one place the raw value is used
///
/// // Just hide it, with no type of its own: wrap it in `Hidden`.
/// let note: Redacted<Hidden<u64>> = Redacted::new(Hidden(42));   // prints "[redacted]"
/// ```
///
/// # What it proves
/// - **Nothing leaks by accident through formatting:** `Debug` prints only
///   what the type's mask writes, and there's no `Display`, so `{}` doesn't
///   compile.
/// - **One policy per kind of data:** the mask belongs to the data's type, so
///   every `Redacted<TaxId>` in the program prints the same way. Two fields
///   holding tax ids can't disagree.
/// - **No unnamed sensitive data:** there's no mask for raw primitives, so
///   `Redacted<u64>` can't be printed. You have to say what the value is
///   (`TaxId`), or explicitly choose `Hidden<u64>`.
/// - `expose()` returns exactly the wrapped value, so specs can still reason
///   about it (e.g. "the SSN sent to the bureau is the one on the application").
///
/// # What it does NOT prove
/// - Real information-flow security. Once `expose()` hands out the value, the
///   type can't follow where it goes. This is hygiene that makes leaks rare
///   and reviewable, not a proof that they're impossible.
/// - That a mask hides enough. A mask can see the value, so it *can* print it;
///   review `Mask` impls like any other code that handles the raw data.
pub struct Redacted<T> { v: T }

impl<T> View for Redacted<T> {
    type V = T;
    closed spec fn view(&self) -> T { self.v }
}

impl<T: Copy> Clone for Redacted<T> {
    fn clone(&self) -> (r: Self) ensures r@ == self@ { Redacted { v: self.v } }
}
impl<T: Copy> Copy for Redacted<T> {}

impl<T> Redacted<T> {
    pub fn new(v: T) -> (r: Self) ensures r@ == v { Redacted { v } }

    /// Access the sensitive value. Every call site is a place to review.
    pub fn expose(&self) -> (r: &T) ensures *r == self@ { &self.v }
}

/// "Just hide it": a ready-made mask for values that don't have a type of
/// their own. `Redacted<Hidden<u64>>` prints `[redacted]`.
pub struct Hidden<T>(pub T);

impl<T: Copy> Clone for Hidden<T> {
    fn clone(&self) -> (r: Self) ensures r.0 == self.0 { Hidden(self.0) }
}
impl<T: Copy> Copy for Hidden<T> {}

} // verus!

/// How a kind of sensitive data is shown in logs and debug output.
///
/// Implement it on the data's own type (e.g. `TaxId`), so the policy is
/// decided once for every place that data appears. Write a fixed string, or a
/// safe *part* of the value such as the last four digits.
pub trait Mask {
    fn fmt_masked(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result;
}

impl<T> Mask for Hidden<T> {
    fn fmt_masked(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("[redacted]")
    }
}

impl<T: Mask> core::fmt::Debug for Redacted<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.v.fmt_masked(f)
    }
}
