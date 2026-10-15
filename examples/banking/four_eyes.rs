//! Layer 2: maker-checker ("four eyes") approval.
//!
//! High-risk actions (large transfers, limit changes, account closures) need
//! one person to request them and a **different** person to approve them.
//!
//! # Rules (all proved)
//! - An [`Approval`] can only be created by [`approve`], and only when the
//!   checker is not the maker.
//! - An approval names the request it's for, so it can't be reused for
//!   another one. Functions that need approval take `Tracked<Approval>`
//!   (consuming it: one approval, one action) and require
//!   `approval@.request() == <their request id>`.
//! - It costs nothing at runtime (tracked values are erased).

use vstd::prelude::*;

verus! {

#[allow(dead_code)] // fields exist only for specs
pub tracked struct Approval { ghost request: u64, ghost maker: u64, ghost checker: u64 }

impl Approval {
    pub closed spec fn request(self) -> u64 { self.request }
    pub closed spec fn maker(self) -> u64 { self.maker }
    pub closed spec fn checker(self) -> u64 { self.checker }
}

#[derive(Debug)]
pub struct SamePerson;

/// `checker` approves request `request`, made by `maker`.
#[allow(unused_variables)] // `request` is used only by the spec
pub fn approve(request: u64, maker: u64, checker: u64) -> (r: Result<Tracked<Approval>, SamePerson>)
    ensures
        match r {
            Ok(t) => t@.request() == request && t@.maker() == maker && t@.checker() == checker
                     && maker != checker,
            Err(_) => maker == checker,
        },
{
    if maker == checker { return Err(SamePerson); }
    let tracked a = Approval { request, maker, checker };
    Ok(Tracked(a))
}

} // verus!
