//! Layer 3: customer onboarding (KYC) as a workflow.
//!
//!   Applied --verify--> Verified
//!
//! A bank may only open accounts for customers whose identity was verified
//! ("know your customer") and who were screened against sanctions lists. Here
//! that's a type: `Bank::open_account` takes a `&Customer<Verified>`, so an
//! account for an unverified customer can't even be written.
//!
//! The tax id has its own type, [`TaxId`], whose mask shows only the last four
//! digits (`***-**-6789`). Every place a tax id appears prints the same way.

use vstd::prelude::*;
use verus_types::redacted::{Mask, Redacted};
use verus_types::workflow::{CanMoveTo, InState, State};

verus! {

/// A taxpayer identification number. Sensitive: always held as `Redacted<TaxId>`.
#[derive(Copy, Clone)]
pub struct TaxId(pub u64);

#[derive(Copy, Clone)]
pub struct CustomerData {
    pub id: u64,
    pub tax_id: Redacted<TaxId>,
    /// When identity documents were verified.
    pub kyc_verified_at: Option<u64>,
    /// Whether the customer was screened against sanctions lists.
    pub sanctions_screened: bool,
}

pub struct Applied;
pub struct Verified;

impl State<CustomerData> for Applied {
    open spec fn holds(d: CustomerData) -> bool { d.kyc_verified_at is None }
    fn check(d: &CustomerData) -> (r: bool) ensures r == Self::holds(*d) { d.kyc_verified_at.is_none() }
}

impl State<CustomerData> for Verified {
    open spec fn holds(d: CustomerData) -> bool { d.kyc_verified_at is Some && d.sanctions_screened }
    fn check(d: &CustomerData) -> (r: bool) ensures r == Self::holds(*d) {
        d.kyc_verified_at.is_some() && d.sanctions_screened
    }
}

impl CanMoveTo<Verified> for Applied {}

pub type Customer<S> = InState<CustomerData, S>;

pub fn apply(id: u64, tax_id: u64) -> (r: Customer<Applied>)
    ensures r@.id == id && r@.tax_id@.0 == tax_id,
{
    let d = CustomerData { id, tax_id: Redacted::new(TaxId(tax_id)), kyc_verified_at: None, sanctions_screened: false };
    match Customer::<Applied>::new(d) {
        Ok(c) => c,
        Err(_) => vstd::pervasive::unreached(),
    }
}

/// Record a successful identity check. Fails (customer handed back) if the
/// sanctions screening didn't pass.
pub fn verify(c: Customer<Applied>, now: u64, screened_ok: bool) -> (r: Result<Customer<Verified>, Customer<Applied>>)
    ensures
        match r {
            Ok(v) => v@ == CustomerData { kyc_verified_at: Some(now), sanctions_screened: true, ..c@ },
            Err(back) => back@ == c@ && !screened_ok,
        },
{
    let d = *c.get();
    match c.advance::<Verified>(CustomerData { kyc_verified_at: Some(now), sanctions_screened: screened_ok, ..d }) {
        Ok(v) => Ok(v),
        Err((back, _)) => Err(back),
    }
}

} // verus!

/// Tax ids show only their last four digits: `***-**-6789`.
impl Mask for TaxId {
    fn fmt_masked(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "***-**-{:04}", self.0 % 10_000)
    }
}
