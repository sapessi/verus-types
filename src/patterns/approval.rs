//! Pattern: unforgeable witness tokens ("step B requires step A").
//!
//! Plain Rust uses branded lifetimes (`for<'id>`) to tie a witness to one
//! value. Verus has a more direct tool: TRACKED ghost values. They're
//! zero-sized, erased at runtime, and can only be created where their private
//! fields are visible, i.e. inside this module. A ghost field ties each token
//! to a specific change id, so no branding is needed.

use vstd::prelude::*;

verus! {

pub struct Change { pub id: u64, pub author: u64 }

/// A proof, checked at compile time, that change `change()` was approved by
/// `approver()`, who is not its author. **Zero bytes and zero cost at
/// runtime**: tracked values are erased.
///
/// # Use it for
/// "Step B may happen only after step A" rules across functions or modules:
/// deploy-after-approval, refund-after-payment, delete-after-backup,
/// pay-after-fraud-check. The function performing step A (`approve`)
/// is the **only** place that can create the token, and the function
/// performing step B (`deploy`) requires one.
///
/// # Example
/// ```ignore
/// let approval = approve(&change, reviewer)?;   // Err if reviewer == author
/// deploy(&change, Tracked(approval.borrow()));   // verifies
///
/// deploy(&other_change, Tracked(approval.borrow())); // FAILS to verify:
///                                                    // token is for a different change
/// ```
///
/// # What it proves
/// - **Unforgeable:** the fields are private, so code outside this module
///   can't create an `Approved`, even in proof code.
/// - **Bound to one value:** `deploy` requires `approval@.change() == c.id`,
///   so a token for one change can't authorize another.
/// - **Carries facts:** the separation-of-duties rule (`approver != author`)
///   is in `approve`'s `ensures`. Holding the token *is* holding that fact.
///
/// # What it does NOT prove
/// - That the approval is still **current**. Tokens record facts that never
///   become false ("was approved"). If an approval can be revoked or expire,
///   re-check the live state at the point of use, and keep the token only for
///   what can't change.
/// - Anything across a process boundary. Tokens exist only inside one verified
///   program. Between services, persist the fact (e.g. a `WriteOnce`
///   `approved_at` column) and re-establish it on load.
///
/// # Verus notes
/// Ghost fields hold spec values and tracked types are linear-ish proof
/// objects. Neither exists at runtime. This replaces the plain-Rust
/// "branded lifetime" (`for<'id>`) trick with something more direct.
// The fields exist only for specs; in a plain `cargo build` nothing reads them.
#[allow(dead_code)]
pub tracked struct Approved { ghost change: u64, ghost approver: u64 }

impl Approved {
    pub closed spec fn change(self) -> u64 { self.change }
    pub closed spec fn approver(self) -> u64 { self.approver }
}

pub struct SelfApproval;

pub fn approve(c: &Change, approver: u64) -> (r: Result<Tracked<Approved>, SelfApproval>)
    ensures
        match r {
            Ok(t)  => t@.change() == c.id && t@.approver() == approver && approver != c.author,
            Err(_) => approver == c.author,
        },
{
    if approver == c.author { return Err(SelfApproval); }
    // Mint the token. Only code that can see Approved's private fields (this
    // module) can do this.
    let tracked tok = Approved { change: c.id, approver };
    Ok(Tracked(tok))
}

// The precondition ties the token to THIS change. Calling deploy without an
// approval, or with another change's approval, doesn't verify.
// Stub body: the parameters are used only by the spec (`requires`).
#[allow(unused_variables)]
pub fn deploy(c: &Change, approval: Tracked<&Approved>)
    requires approval@.change() == c.id,
{
    // ... actual deployment ...
}

} // verus!
