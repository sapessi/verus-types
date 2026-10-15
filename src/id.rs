//! Typed identifiers: an `Id<Account>` can't be used where an `Id<Customer>` is expected.

use vstd::prelude::*;
use core::marker::PhantomData;

verus! {

/// An identifier for things of kind `K`.
///
/// # Use it for
/// Every identifier that travels through your code: account ids, customer
/// ids, order ids, request ids. Declare one empty marker type per kind:
/// ```ignore
/// pub struct Account;  pub type AccountId  = Id<Account>;
/// pub struct Customer; pub type CustomerId = Id<Customer>;
///
/// fn close(a: AccountId) { .. }
/// close(customer_id);   // type error: Id<Customer> is not Id<Account>
/// ```
///
/// # What it proves
/// - **No mix-ups between kinds:** passing a customer id where an account id is
///   expected is a compile error. With bare `u64`s it would compile and
///   silently act on the wrong record.
/// - `same(a, b)` returns exactly whether the two ids are equal, so specs can
///   reason about "the same account" (e.g. "a transfer's source and
///   destination differ").
///
/// # What it does NOT prove
/// - That the id **exists** (refers to a real record). Look it up and handle
///   "not found".
/// - Anything about ids from outside the program: parse them at the edge with
///   `Id::new`.
///
/// # Verus notes
/// The view is the raw `u64`, so specs compare ids with `a@ == b@`. `Id` is
/// `Copy`, so ids can be passed around freely, like integers.
pub struct Id<K> { v: u64, _k: PhantomData<K> }

impl<K> View for Id<K> {
    type V = u64;
    closed spec fn view(&self) -> u64 { self.v }
}

impl<K> Clone for Id<K> {
    fn clone(&self) -> (r: Self) ensures r@ == self@ { Id { v: self.v, _k: PhantomData } }
}
impl<K> Copy for Id<K> {}

impl<K> Id<K> {
    pub fn new(v: u64) -> (r: Self) ensures r@ == v { Id { v, _k: PhantomData } }

    pub fn get(&self) -> (r: u64) ensures r == self@ { self.v }

    /// Equality of two ids of the same kind.
    pub fn same(&self, other: &Self) -> (r: bool) ensures r == (self@ == other@) {
        self.v == other.v
    }
}

} // verus!
