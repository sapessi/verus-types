//! Worked patterns that combine the library types with domain code.
//!
//! These modules are verified together with the library, so they double as
//! regression tests for the types. Copy and adapt them; they aren't meant to
//! be depended on directly.
//!
//! - [`approval`]: an unforgeable, zero-cost token for "deploy only after an
//!   independent approval".
//! - [`transaction`]: commit-or-rollback with no way to leak the transaction.

pub mod approval;
pub mod transaction;
