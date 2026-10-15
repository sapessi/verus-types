//! Layer 2: money as a currency-tagged `Quantity`.
//!
//! The library knows only units. A currency is a unit that also knows how many
//! decimal places its minor unit has (USD 2 = cents, JPY 0, KWD 3). That's
//! needed to display and parse amounts; the arithmetic doesn't change.

use vstd::prelude::*;
use verus_types::quantity::{Quantity, Unit};

verus! {

/// A currency: a [`Unit`] whose count is the currency's minor unit.
pub trait Currency: Unit {
    /// Decimal places of the minor unit (ISO 4217): USD 2, JPY 0, KWD 3.
    fn minor_digits() -> u32;
    /// ISO 4217 code, for display.
    fn code() -> &'static str;
}

pub struct Usd;
impl Unit for Usd {}
impl Currency for Usd {
    fn minor_digits() -> u32 { 2 }
    fn code() -> &'static str { "USD" }
}

pub struct Jpy;
impl Unit for Jpy {}
impl Currency for Jpy {
    fn minor_digits() -> u32 { 0 }
    fn code() -> &'static str { "JPY" }
}

/// An amount of currency `C`, in minor units. `Money<Usd>` and `Money<Jpy>`
/// can't be mixed.
pub type Money<C> = Quantity<C>;

} // verus!

/// Format an amount for people, e.g. `USD 1234.05`. Not verified (display only).
pub fn format<C: Currency>(m: &Money<C>) -> String {
    let d = C::minor_digits();
    let v = m.get();
    if d == 0 { return format!("{} {}", C::code(), v); }
    let p = 10u64.pow(d);
    format!("{} {}.{:0width$}", C::code(), v / p, v % p, width = d as usize)
}
