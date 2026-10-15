//! Layer 3: interest accrual with day-count conventions.
//!
//! Interest for `days` days on a balance at an annual rate is
//! `balance × rate × days / days_in_year`. Banks disagree on `days_in_year`:
//! that's the **day-count convention**, fixed by the account's contract.
//! Using the wrong one is a classic, hard-to-spot bug: on a $1M balance at 5%,
//! ACT/360 vs ACT/365 differs by about $9.50 a month.
//!
//! # Rules (all proved)
//! - The convention is a type parameter of the rate, so a rate quoted ACT/360
//!   can't be used with an ACT/365 accrual.
//! - Interest is the exact value **rounded down** (in the customer's favor
//!   for interest *charged*, the bank's for interest *paid*: pick the mode the
//!   contract requires), and never off by a full cent.
//! - No overflow: results that don't fit return `None`.

use vstd::prelude::*;
use core::marker::PhantomData;
use verus_types::bounded::Bounded;
use verus_types::ratio::{Ratio, Rounding};
#[cfg(verus_only)] // spec-only: erased in a plain cargo build
use verus_types::ratio::rounds;
use crate::money::{Currency, Money};

verus! {

/// A day-count convention: how many days a year has, for interest.
pub trait DayCount {
    spec fn year() -> nat;
    fn days_in_year() -> (r: u64) ensures r as nat == Self::year(), 0 < r <= 366;
}

/// Actual days / 360. Common for commercial loans and money markets.
pub struct Act360;
impl DayCount for Act360 {
    fn days_in_year() -> (r: u64) ensures r as nat == Self::year(), 0 < r <= 366 { 360 }
    open spec fn year() -> nat { 360 }
}

/// Actual days / 365. Common for consumer deposits and UK products.
pub struct Act365;
impl DayCount for Act365 {
    fn days_in_year() -> (r: u64) ensures r as nat == Self::year(), 0 < r <= 366 { 365 }
    open spec fn year() -> nat { 365 }
}

/// Annual rate in basis points (0% to 100%).
pub type RateBps = Bounded<0, 10_000>;
/// Days in one accrual period (at most a leap year).
pub type Days = Bounded<0, 366>;

/// An annual interest rate quoted under day-count convention `D`.
pub struct AnnualRate<D: DayCount> { pub bps: RateBps, pub convention: PhantomData<D> }

impl<D: DayCount> AnnualRate<D> {
    pub fn new(bps: RateBps) -> (r: Self) ensures r.bps == bps { AnnualRate { bps, convention: PhantomData } }
}

/// Interest on `balance` for `days` days at `rate`, rounded with `mode`.
pub fn accrue<C: Currency, D: DayCount>(balance: &Money<C>, rate: &AnnualRate<D>, days: &Days, mode: Rounding)
    -> (r: Option<Money<C>>)
    ensures
        r matches Some(i) ==> rounds(
            (balance@ as int) * (rate.bps.spec_get() as int) * (days.spec_get() as int),
            10_000 * (D::year() as int),
            i@ as int, mode),
{
    let bps = rate.bps.get();     // <= 10_000: from the type
    let d = days.get();           // <= 366: from the type
    let year = D::days_in_year();
    proof {
        assert(bps * d <= 10_000 * 366) by (nonlinear_arith) requires bps <= 10_000, d <= 366;
    }
    let ratio = match Ratio::new(bps * d, 10_000 * year) {   // can't fail: year > 0
        Some(q) => q,
        None => return None,
    };
    match ratio.apply(balance.get(), mode) {
        Some(v) => {
            proof {
                assert((balance@ as int) * (bps as int) * (d as int) == (balance@ as int) * ((bps * d) as int))
                    by (nonlinear_arith);
            }
            Some(Money::new(v))
        }
        None => None,
    }
}

} // verus!
