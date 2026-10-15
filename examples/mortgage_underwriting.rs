//! Mortgage underwriting with `Quantity` (used as money) and `Bounded`.
//!
//! Policy, checked in order (the decline reason must be the FIRST failing rule,
//! because declined applicants are legally owed an accurate reason):
//!   1. credit score >= 620
//!   2. loan-to-value <= 80%
//!   3. debt-to-income (existing debts + new payment) <= 43%
//!
//! Proved: `underwrite` returns exactly what the spec table `decide` says, for
//! every input, with no overflow. Run: `cargo run --example mortgage_underwriting`

use vstd::prelude::*;
use verus_types::bounded::Bounded;
use verus_types::quantity::{Quantity, Unit};

verus! {

// The library only knows units, not money. A currency is just a unit whose
// count is the currency's minor unit (cents for USD).
pub struct Usd;
impl Unit for Usd {}
pub struct Eur;
impl Unit for Eur {}
pub type Money<C> = Quantity<C>;

pub type CreditScore = Bounded<300, 850>;   // out-of-range scores are rejected at the edge

pub struct Application {
    pub loan: Money<Usd>,
    pub property_value: Money<Usd>,
    pub monthly_income: Money<Usd>,
    pub monthly_debts: Money<Usd>,         // existing debts + the new mortgage payment
    pub score: CreditScore,
}

#[derive(Copy, Clone, Debug)]
pub enum Decision { Approve, DeclineCreditScore, DeclineLoanToValue, DeclineDebtToIncome }

// The policy as a spec table: this is what you review with credit-risk people.
// Ratios are written without division (loan/value <= 80%  <=>  loan*100 <= value*80),
// so every check is linear arithmetic.
pub open spec fn decide(a: &Application) -> Decision {
    if a.score.spec_get() < 620 { Decision::DeclineCreditScore }
    else if a.loan@ * 100 > a.property_value@ * 80 { Decision::DeclineLoanToValue }
    else if a.monthly_debts@ * 100 > a.monthly_income@ * 43 { Decision::DeclineDebtToIncome }
    else { Decision::Approve }
}

pub fn underwrite(a: &Application) -> (r: Decision)
    ensures r == decide(a),
{
    // `get()` hands us 300 <= score <= 850 for free (type invariant of Bounded).
    if a.score.get() < 620 { return Decision::DeclineCreditScore; }
    // u128 so `* 100` can't overflow for any u64 amount; Verus checks this.
    if (a.loan.get() as u128) * 100 > (a.property_value.get() as u128) * 80 {
        return Decision::DeclineLoanToValue;
    }
    if (a.monthly_debts.get() as u128) * 100 > (a.monthly_income.get() as u128) * 43 {
        return Decision::DeclineDebtToIncome;
    }
    Decision::Approve
}

} // verus!

fn usd(dollars: u64) -> Money<Usd> { Quantity::new(dollars * 100) }   // dollars -> cents

fn main() {
    let score = |s| CreditScore::new(s).expect("score in 300..=850");
    let cases = [
        ("good borrower",   400_000, 500_000, 12_000, 3_000, 740),
        ("low score",       400_000, 500_000, 12_000, 3_000, 600),
        ("too little down", 480_000, 500_000, 12_000, 3_000, 740),
        ("too much debt",   400_000, 500_000,  8_000, 4_000, 740),
    ];
    for (name, loan, value, income, debts, s) in cases {
        let app = Application {
            loan: usd(loan), property_value: usd(value),
            monthly_income: usd(income), monthly_debts: usd(debts), score: score(s),
        };
        println!("{name:16} -> {:?}", underwrite(&app));
    }
    // Rejected before underwriting ever sees it:
    println!("score 900        -> valid? {}", CreditScore::new(900).is_some());
    // Doesn't compile: Money<Usd> and Money<Eur> are different types.
    // usd(1).checked_add(Money::<Eur>::new(1));
}
