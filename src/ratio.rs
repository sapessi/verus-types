//! Exact fractions and explicit rounding: interest, fees, pro-rating, currency conversion.

use vstd::prelude::*;

verus! {

/// How to round a result that isn't a whole number of units.
#[derive(Copy, Clone, Debug)]
pub enum Rounding {
    /// Toward zero (truncate). Typical for interest paid **to** customers.
    Down,
    /// Away from zero. Typical for fees, so the institution never under-collects.
    Up,
    /// To the nearest unit; exact halves go up. Typical for displayed amounts.
    HalfUp,
}

/// `r` is `exact_num / den` rounded to a whole number according to `mode`.
///
/// Written without division so it's easy to check by hand:
/// - Down:   `r·den ≤ x < (r+1)·den`
/// - Up:     `(r−1)·den < x ≤ r·den`
/// - HalfUp: `(2r−1)·den ≤ 2x < (2r+1)·den`   (r is within half a unit)
pub open spec fn rounds(x: int, den: int, r: int, mode: Rounding) -> bool {
    match mode {
        Rounding::Down   => r * den <= x && x < (r + 1) * den,
        Rounding::Up     => (r - 1) * den < x && x <= r * den,
        Rounding::HalfUp => (2 * r - 1) * den <= 2 * x && 2 * x < (2 * r + 1) * den,
    }
}

/// A non-negative fraction `num / den`, with `den > 0`.
///
/// # Use it for
/// Anything computed as "amount × fraction": interest
/// (`rate × days / days_in_year`), fees in basis points, pro-rated charges,
/// currency conversion, splitting a bill. Keep the fraction exact and round
/// **once**, at the end, with a rounding mode you chose on purpose.
///
/// # Example
/// ```ignore
/// // 5.25% a year for 31 days on an ACT/365 basis:  525 × 31 / (10_000 × 365)
/// let r = Ratio::new(525 * 31, 10_000 * 365).ok_or(BadRate)?;
/// let interest = r.apply(balance_cents, Rounding::Down).ok_or(Overflow)?;
/// ```
///
/// # What it proves
/// - **Correct rounding:** the result of `apply` satisfies the spec fn `rounds`: it's
///   the exact value rounded down, up or to nearest, never off by more than
///   the mode allows. This holds for every input, including the edge cases
///   (exact halves, remainders of `den − 1`) that hand-written integer
///   rounding usually gets wrong.
/// - **No overflow:** the product is computed in `u128`; if the rounded result
///   doesn't fit in a `u64`, `apply` returns `None` instead of a wrapped number.
/// - `den` is never zero (type invariant), so there's no division by zero.
///
/// # What it does NOT prove
/// - That you picked the rounding mode your contract or regulator requires.
/// - Banker's rounding (half-to-even). Add it as another mode with its own proof.
///
/// # Verus notes
/// All nonlinear arithmetic (products of variables, division) is confined to
/// `apply`, proved with `nonlinear_arith`. Callers get the linear `rounds`
/// facts and never reason about multiplication themselves.
pub struct Ratio { num: u64, den: u64 }

impl Ratio {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool { self.den > 0 }

    pub closed spec fn num_spec(&self) -> nat { self.num as nat }
    pub closed spec fn den_spec(&self) -> nat { self.den as nat }

    pub fn new(num: u64, den: u64) -> (r: Option<Self>)
        ensures
            r is Some <==> den > 0,
            r matches Some(q) ==> q.num_spec() == num && q.den_spec() == den,
    {
        if den > 0 { Some(Ratio { num, den }) } else { None }
    }

    pub fn den(&self) -> (r: u64) ensures r == self.den_spec(), r > 0 {
        proof { use_type_invariant(self); }
        self.den
    }

    /// `q × num / den`, rounded with `mode`.
    pub fn apply(&self, q: u64, mode: Rounding) -> (r: Option<u64>)
        ensures
            match r {
                Some(v) => rounds((q as int) * (self.num_spec() as int), self.den_spec() as int, v as int, mode),
                None    => (q as int) * (self.num_spec() as int) >= (u64::MAX as int) * (self.den_spec() as int),
            },
    {
        proof { use_type_invariant(self); }
        let d = self.den as u128;
        proof {
            // The product of two u64s fits in a u128.
            assert((q as int) * (self.num as int) <= (u64::MAX as int) * (u64::MAX as int)) by (nonlinear_arith)
                requires q <= u64::MAX, self.num <= u64::MAX;
        }
        let p: u128 = (q as u128) * (self.num as u128);
        // Add the rounding offset before dividing. Each sum fits in u128
        // because p <= (2^64 - 1)^2 and the offset is below 2^64.
        let offset: u128 = match mode {
            Rounding::Down => 0,
            Rounding::Up => d - 1,
            Rounding::HalfUp => d / 2,
        };
        let v = (p + offset) / d;
        proof {
            let (x, dd, o, vv) = (p as int, d as int, offset as int, v as int);
            assert(x + o == dd * vv + (x + o) % dd && 0 <= (x + o) % dd < dd) by (nonlinear_arith)
                requires dd > 0, vv == (x + o) / dd, x + o >= 0;
            match mode {
                Rounding::Down => {
                    assert(vv * dd <= x && x < (vv + 1) * dd) by (nonlinear_arith)
                        requires o == 0, x + o == dd * vv + (x + o) % dd, 0 <= (x + o) % dd < dd;
                }
                Rounding::Up => {
                    assert((vv - 1) * dd < x && x <= vv * dd) by (nonlinear_arith)
                        requires o == dd - 1, x + o == dd * vv + (x + o) % dd, 0 <= (x + o) % dd < dd;
                }
                Rounding::HalfUp => {
                    // d/2 is exact for even d; for odd d an exact half can't occur.
                    assert(2 * o == dd || 2 * o == dd - 1) by (nonlinear_arith)
                        requires o == dd / 2, dd > 0;
                    assert((2 * vv - 1) * dd <= 2 * x && 2 * x < (2 * vv + 1) * dd) by (nonlinear_arith)
                        requires 2 * o == dd || 2 * o == dd - 1,
                                 x + o == dd * vv + (x + o) % dd, 0 <= (x + o) % dd < dd;
                }
            }
        }
        if v > u64::MAX as u128 {
            proof {
                let (x, dd, o, vv) = (p as int, d as int, offset as int, v as int);
                assert(x >= (u64::MAX as int) * dd) by (nonlinear_arith)
                    requires vv >= u64::MAX as int + 1, x + o == dd * vv + (x + o) % dd,
                             0 <= (x + o) % dd, o <= dd - 1, dd > 0;
            }
            None
        } else {
            Some(v as u64)
        }
    }
}

} // verus!
