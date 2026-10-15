//! Optimistic concurrency: updates succeed only against the version you read.

use vstd::prelude::*;

verus! {

/// Returned when an update was based on an out-of-date version.
pub struct Stale;

/// A value with a version number that increases by one on every update.
///
/// # Use it for
/// Records that several users or processes may edit at the same time: an
/// account profile, a loan application, a configuration entry. Each writer
/// reads the value **and its version**, then updates with
/// `update(expected_version, new_value)`.
///
/// # Example
/// ```ignore
/// let (profile, ver) = (rec.get().clone(), rec.version());
/// let edited = Profile { email: new_email, ..profile };
/// match rec.update(ver, edited) {
///     Ok(())      => { /* saved */ }
///     Err(Stale)  => { /* someone else saved first: re-read and retry */ }
/// }
/// ```
///
/// # What it proves
/// - **No lost updates:** `update` succeeds **only** if the caller's expected
///   version equals the current one. Two writers that read the same version
///   can't both succeed; the second gets `Err(Stale)` instead of silently
///   overwriting the first one's change.
/// - On success the new value is stored and the version is exactly one higher.
/// - On failure nothing changes.
/// - The version never decreases (see `evolves`).
///
/// # What it does NOT prove
/// - Atomicity across processes. Inside one program `&mut` already prevents
///   races. For a database row, the same check must run inside the database
///   (`UPDATE ... WHERE version = ?`), which belongs in an `assume trusted`.
///
/// # Verus notes
/// The version view is `nat`. Updates fail rather than wrap once the version
/// reaches `u64::MAX`, which in practice never happens.
pub struct Versioned<T> { value: T, version: u64 }

impl<T> Versioned<T> {
    pub closed spec fn value(&self) -> T { self.value }
    pub closed spec fn version_spec(&self) -> nat { self.version as nat }

    /// The version only goes up.
    pub open spec fn evolves(pre: Self, post: Self) -> bool {
        post.version_spec() >= pre.version_spec()
    }

    pub fn new(value: T) -> (r: Self)
        ensures r.value() == value, r.version_spec() == 0,
    { Versioned { value, version: 0 } }

    pub fn get(&self) -> (r: &T) ensures *r == self.value() { &self.value }

    pub fn version(&self) -> (r: u64) ensures r as nat == self.version_spec() { self.version }

    pub fn update(&mut self, expected: u64, new_value: T) -> (r: Result<(), Stale>)
        ensures
            r is Ok <==> (expected as nat == old(self).version_spec()
                          && old(self).version_spec() < u64::MAX),
            r is Ok ==> final(self).value() == new_value
                        && final(self).version_spec() == old(self).version_spec() + 1,
            r is Err ==> *final(self) == *old(self),
            Self::evolves(*old(self), *final(self)),
    {
        if expected != self.version || self.version == u64::MAX { return Err(Stale); }
        self.value = new_value;
        self.version = self.version + 1;
        Ok(())
    }
}

} // verus!
