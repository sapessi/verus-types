//! # verus-types
//!
//! Library types that hand facts to the verifier. Each type's API makes a
//! class of business-logic bug impossible to write, and its Verus spec
//! exports what callers may rely on, so code that uses these types needs
//! fewer proofs of its own.
//!
//! ## Choosing a type
//!
//! | Situation                              | Type                                   |
//! |----------------------------------------|----------------------------------------|
//! | "this happened, and when"              | [`history::WriteOnce`]                 |
//! | running total or counter, never down   | [`history::Monotonic`]                 |
//! | audit log or ledger                    | [`history::AppendOnly`]                |
//! | an amount of something (money, shares)  | [`quantity::Quantity`]                 |
//! | a number in a known range              | [`bounded::Bounded`]                   |
//! | a rule across several fields           | [`checked::Checked`]                   |
//! | a fixed workflow                       | [`workflow`] (`InState`, `CanMoveTo`)  |
//! | "step B requires step A happened"      | [`patterns::approval`] (tracked token) |
//! | must commit or roll back               | [`patterns::transaction`]              |
//!
//! ## How the docs are organized
//!
//! Every type's doc comment has the same sections:
//! - **Use it for**: the business situations it fits.
//! - **Example**: typical use (marked `ignore`; examples aren't compiled).
//! - **What it proves**: facts callers get without writing proofs.
//! - **What it does NOT prove**: where you still need specs of your own.
//! - **Verus notes**: how the spec is phrased and why.
//!
//! ## Conventions
//!
//! - Every type has a CLOSED `View` (`x@`). Callers reason only through `@`
//!   and the method `ensures`, never through private fields. (Verus doesn't
//!   let public *open* spec fns read private fields; closed views avoid that.)
//! - Every `&mut self` method states what it does to `self@`, including on
//!   the error path ("unchanged"). Callers never have to guess what changed.
//! - This crate uses Verus's new `&mut` semantics: in `ensures`, `old(x)` is
//!   the value on entry and `final(x)` is the value on return.
//! - Outside verification, the `verus!` macro erases all spec and proof code,
//!   so the crate builds as an ordinary Rust library.
//!
//! ## Deserialization
//!
//! `#[derive(Deserialize)]` would build `Bounded`, `Checked` or `InState<D, S>`
//! WITHOUT running their checks. Route every guarded type through its verified
//! constructor:
//!
//! ```ignore
//! #[derive(Deserialize)]
//! #[serde(try_from = "u64")]
//! pub struct Bounded<..> { .. }
//! impl TryFrom<u64> for Bounded<..> { fn try_from(v) -> .. { Bounded::new(v).ok_or(..) } }
//! ```
//!
//! For workflow data, deserialize the plain data type, then type it with a
//! `classify` function (see `examples/order_workflow.rs`).
//! serde itself is outside Verus; its effect enters the proof only through
//! these verified constructors.

pub mod bounded;
pub mod checked;
pub mod history;
pub mod patterns;
pub mod quantity;
pub mod workflow;
