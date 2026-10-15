//! Workflows: data that is proven to be in a named state, with a fixed table
//! of allowed moves between states.
//!
//! Two ideas, both built on [`Checked`]:
//!
//! 1. **A state is an invariant.** A state marker (`Paid`, `Shipped`) implements
//!    [`State<D>`]: a spec `holds` describing what the data looks like in that
//!    state, plus a runtime `check` proved equal to it. [`InState<D, S>`] is
//!    "data `D`, proven to be in state `S`", which is exactly `Checked<D, S>`.
//! 2. **Allowed moves are trait impls.** `impl CanMoveTo<Shipped> for Paid {}`
//!    declares one edge of the workflow. [`InState::advance`] only compiles
//!    for declared edges, so the set of impls IS the workflow table, and any
//!    other move is a compile error (closed world).
//!
//! # Example
//! ```ignore
//! pub struct Created; pub struct Paid; pub struct Shipped;
//! impl State<OrderData> for Paid { /* holds + check */ }   // one per state
//!
//! impl CanMoveTo<Paid>    for Created {}
//! impl CanMoveTo<Shipped> for Paid    {}
//!
//! pub type Order<S> = InState<OrderData, S>;
//!
//! let paid: Order<Paid> = created.advance::<Paid>(new_data).map_err(..)?;
//! // paid.advance::<Created>(..)   // doesn't compile: no CanMoveTo<Created> for Paid
//! ```
//! See `examples/order_workflow.rs` for a complete, runnable version.
//!
//! # What it proves
//! - **Data matches state, always:** every `InState<D, S>` satisfies
//!   `S::holds`. It can only be created by [`Checked::new`] or
//!   [`InState::advance`], and both check the target state.
//! - **Only declared moves exist:** enforced by the type checker through
//!   `CanMoveTo`.
//! - **Rejected moves lose nothing:** `advance` returns the original value,
//!   unchanged, together with the rejected data.
//!
//! # What it does NOT prove
//! - That states are **disjoint** (no data in two states at once). That's a
//!   fact about your descriptions; prove it once per workflow if you rely on it.
//! - That the new data passed to `advance` was computed correctly from the old.
//!   Wrap `advance` in domain functions whose `ensures` say exactly what changed.

use vstd::prelude::*;
use crate::checked::Checked;

/// A workflow state over data `D`: what the data must look like in that state.
///
/// It's the same trait as [`crate::checked::Invariant`], under a name that
/// reads better here. Implement `holds` (the spec) and `check` (the runtime
/// version, proved equal to it).
pub use crate::checked::Invariant as State;

verus! {

/// Data `D` proven to be in state `S`.
///
/// Create one from untrusted data with `InState::<D, S>::new(d)` (it checks
/// `S`), or move an existing one with [`InState::advance`].
pub type InState<D, S> = Checked<D, S>;

/// Declares that the workflow may move from `Self` to `To`.
///
/// Each impl is one edge of the workflow, so the list of impls reads like the
/// workflow table:
/// ```ignore
/// impl CanMoveTo<Paid>    for Created {}
/// impl CanMoveTo<Shipped> for Paid    {}
/// ```
/// There's deliberately no blanket impl: every allowed move is written down.
pub trait CanMoveTo<To> {}

impl<D, S: State<D>> Checked<D, S> {
    /// Moves to state `T`, with `next` as the new data.
    ///
    /// Compiles only if `S: CanMoveTo<T>`, i.e. the move is in the workflow
    /// table. At runtime, succeeds exactly when `next` satisfies `T`'s
    /// description. On failure the original value is handed back unchanged,
    /// together with the rejected data.
    pub fn advance<T: State<D>>(self, next: D) -> (r: Result<InState<D, T>, (Self, D)>)
        where S: CanMoveTo<T>,
        ensures
            match r {
                Ok(n)       => n@ == next && T::holds(next),
                Err((o, d)) => o@ == self@ && d == next && !T::holds(next),
            },
    {
        match Checked::<D, T>::new(next) {
            Ok(n) => Ok(n),
            Err(d) => Err((self, d)),
        }
    }
}

} // verus!
