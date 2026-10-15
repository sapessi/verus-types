//! # Banking: Layers 2 and 3, built from the `verus-types` library (Layer 1)
//!
//! This crate shows how an application gets proved properties **without its
//! authors writing proofs**: each layer only composes the layer below and
//! declares its rules; the proofs live inside the types.
//!
//! ```text
//! Layer 3  banking      bank · customer (KYC) · interest · disputes
//!              │ adds one banking law each
//! Layer 2  business     money · ledger · audit · four_eyes
//!              │ instantiates with units, rules, states
//! Layer 1  library      Quantity · Id · history · Checked · workflow ·
//!                       IdempotencyLog · WindowLimit · Ratio · TimeRange · Redacted
//! ```
//!
//! | Module | Layer | Built from | What's proved |
//! |---|---|---|---|
//! | [`money`] | 2 | `Quantity`, `Unit` | currencies can't be mixed; amounts carry their decimal places |
//! | [`ledger`] | 2 | `AppendOnly`, `Id`, `Money` | balance = sum of the journal; never negative; transfers conserve value |
//! | [`audit`] | 2 | `AppendOnly` | the trail is append-only and in time order |
//! | [`four_eyes`] | 2 | tracked token | an approval names one request and needs two different people |
//! | [`customer`] | 3 | `workflow`, `Redacted` | only verified, sanctions-screened customers reach `Verified`; tax ids print as `***-**-6789` |
//! | [`bank`] | 3 | all of the above, `IdempotencyLog`, `WindowLimit` | conservation, at-most-once transfers, holds, daily limits, approvals, freezes |
//! | [`interest`] | 3 | `Ratio`, `Rounding`, `Bounded` | correct rounding under the account's day-count convention |
//! | [`disputes`] | 3 | `TimeRange` | a dispute case can only be opened inside the Reg E window |
//!
//! Verify: `cargo verus verify --example banking`.
//! Run the scenarios: `cargo test --example banking`.

pub mod audit;
pub mod bank;
pub mod customer;
pub mod disputes;
pub mod four_eyes;
pub mod interest;
pub mod ledger;
pub mod money;

#[cfg(test)]
mod scenarios {
    //! End-to-end scenarios. They run the same code the proofs cover, so they
    //! show the guarantees in action; they're illustrations, not the evidence.

    use crate::bank::{Bank, Outcome, Rejection, DAY};
    use crate::customer::{apply, verify};
    use crate::disputes::{check_window, open_case, DisputeError, Statement};
    use crate::four_eyes::approve;
    use crate::interest::{accrue, Act360, Act365, AnnualRate, Days, RateBps};
    use crate::money::{format, Jpy, Money, Usd};
    use verus_types::ratio::Rounding;

    fn usd(cents: u64) -> Money<Usd> { Money::new(cents) }

    /// A bank with two funded accounts: Alice $8,000.00, Bob $0.
    fn setup() -> (Bank<Usd>, crate::ledger::AccountId, crate::ledger::AccountId) {
        let mut bank = Bank::<Usd>::new();
        let alice = verify(apply(1, 123_45_6789), 10, true).ok().unwrap();
        let bob = verify(apply(2, 987_65_4321), 10, true).ok().unwrap();
        let a = bank.open_account(&alice, 20).unwrap();
        let b = bank.open_account(&bob, 20).unwrap();
        bank.deposit(a, usd(800_000), 30).unwrap();
        (bank, a, b)
    }

    #[test]
    fn kyc_gate_and_redaction() {
        let applied = apply(3, 111_22_3333);
        // Sanctions screening failed: the customer stays `Applied`, and
        // `open_account` only accepts `&Customer<Verified>`, so no account.
        let still_applied = verify(applied, 10, false).err().unwrap();
        assert_eq!(format!("{:?}", still_applied.get().tax_id), "***-**-3333");   // custom mask
    }

    #[test]
    fn transfer_conserves_money() {
        let (mut bank, a, b) = setup();
        assert_eq!(bank.transfer(1, a, b, usd(250_000), 40), Outcome::Done);
        let (ba, bb) = (bank.balance_of(a).unwrap().get(), bank.balance_of(b).unwrap().get());
        assert_eq!((ba, bb), (550_000, 250_000));
        assert_eq!(ba + bb, 800_000);   // conserved
    }

    #[test]
    fn retry_is_idempotent() {
        let (mut bank, a, b) = setup();
        assert_eq!(bank.transfer(7, a, b, usd(100_000), 40), Outcome::Done);
        // Network timeout, client retries with the same key: no second transfer.
        assert_eq!(bank.transfer(7, a, b, usd(100_000), 41), Outcome::Done);
        assert_eq!(bank.balance_of(b).unwrap().get(), 100_000);
    }

    #[test]
    fn holds_reserve_funds() {
        let (mut bank, a, b) = setup();
        bank.place_hold(a, 700_000, 40).unwrap();             // card authorization: $7,000
        assert_eq!(bank.transfer(2, a, b, usd(200_000), 41),  // only $1,000 available
                   Outcome::Rejected(Rejection::InsufficientAvailable));
        bank.capture_hold(a, 700_000, 42).unwrap();           // merchant settles
        assert_eq!(bank.balance_of(a).unwrap().get(), 100_000);
        assert_eq!(bank.held_of(a).unwrap(), 0);
    }

    #[test]
    fn daily_limit_cannot_be_split_around() {
        let (mut bank, a, b) = setup();
        bank.deposit(a, usd(1_000_000), 31).unwrap();         // now $18,000
        for k in 0..2 { assert_eq!(bank.transfer(10 + k, a, b, usd(450_000), 40), Outcome::Done); }
        // $9,000 sent today; another $4,500 would exceed the $10,000 daily limit.
        assert_eq!(bank.transfer(12, a, b, usd(450_000), 41), Outcome::Rejected(Rejection::DailyLimit));
        // Next day: a new window.
        assert_eq!(bank.transfer(13, a, b, usd(450_000), 40 + DAY), Outcome::Done);
    }

    #[test]
    fn large_transfers_need_four_eyes() {
        let (mut bank, a, b) = setup();
        assert_eq!(bank.transfer(20, a, b, usd(600_000), 40), Outcome::Rejected(Rejection::NeedsApproval));
        assert!(approve(20, 501, 501).is_err());              // can't approve your own request
        let ok = approve(20, 501, 502).unwrap();
        assert_eq!(bank.transfer_approved(20, a, b, usd(600_000), 41, ok), Outcome::Done);
    }

    #[test]
    fn frozen_accounts_cannot_move_money() {
        let (mut bank, a, b) = setup();
        bank.freeze(a, 40).unwrap();
        assert_eq!(bank.transfer(30, a, b, usd(1), 41), Outcome::Rejected(Rejection::Frozen));
    }

    #[test]
    fn interest_and_day_count() {
        let balance = usd(100_000_000);                        // $1,000,000.00
        let rate = || RateBps::new(500).unwrap();              // 5%
        let days = Days::new(30).unwrap();
        let a360 = accrue(&balance, &AnnualRate::<Act360>::new(rate()), &days, Rounding::Down).unwrap();
        let a365 = accrue(&balance, &AnnualRate::<Act365>::new(rate()), &days, Rounding::Down).unwrap();
        assert_eq!(format(&a360), "USD 4166.66");
        assert_eq!(format(&a365), "USD 4109.58");
        assert_eq!(format(&Money::<Jpy>::new(1500)), "JPY 1500");
    }

    #[test]
    fn reg_e_dispute_window() {
        let stmt = Statement { account: 0, sent_at: 1_000 };
        let on_time = check_window(&stmt, 1_000 + 60 * DAY).unwrap();   // day 60: still on time
        let case = open_case(&stmt, 5, 1_000 + 60 * DAY, on_time);
        assert_eq!(case.entry, 5);
        assert!(matches!(check_window(&stmt, 1_001 + 60 * DAY), Err(DisputeError::TooLate)));
    }
}
