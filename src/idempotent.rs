//! Idempotency: a request retried with the same key has no second effect.

use vstd::prelude::*;

verus! {

/// The recorded result for `key`: the **latest** entry with that key.
pub open spec fn lookup_spec<R>(s: Seq<(u64, R)>, key: u64) -> Option<R>
    decreases s.len(),
{
    if s.len() == 0 { None }
    else if s.last().0 == key { Some(s.last().1) }
    else { lookup_spec(s.drop_last(), key) }
}

/// Results of requests already processed, keyed by idempotency key.
///
/// # Use it for
/// Any operation that clients may retry: payments, transfers, order
/// placement, account opening. Networks time out after the server acted but
/// before the client heard back, so the client retries. Without idempotency,
/// the retry moves the money twice.
///
/// The pattern: the client sends a unique key with the request. The server
///  1. looks the key up; if found, returns the stored result **without acting**;
///  2. otherwise acts, then records the result under the key.
///
/// # Example
/// ```ignore
/// if let Some(prev) = log.lookup(req.key) { return prev; }   // retry: no second effect
/// let result = do_transfer(&req)?;
/// log.record(req.key, result);
/// result
/// ```
///
/// # What it proves
/// - `lookup` returns exactly the result recorded for the key, or `None` if
///   the key is new.
/// - `record` can only be called for a **new** key (it's a precondition), so
///   a key can never be recorded twice with different results: the first
///   result is the result, forever.
/// - Recording a key doesn't change the result of any other key.
/// - The log is append-only: nothing is ever forgotten or rewritten.
///
/// # What it does NOT prove
/// - That you actually check the log before acting. Wrap the pattern above
///   in one function per operation, so it can't be skipped.
/// - Expiry. Real systems forget keys after a retention period; this log
///   keeps them all. Keys must be unique per client request.
/// - Concurrency across processes: two servers checking the same key at the
///   same moment need a database constraint (`UNIQUE(key)`).
///
/// # Verus notes
/// Lookup is a linear scan from the newest entry (the spec `lookup_spec` is
/// defined the same way), which is fine for examples. Replace the storage
/// with a hash map behind the same spec for production.
pub struct IdempotencyLog<R> { entries: Vec<(u64, R)> }

impl<R> View for IdempotencyLog<R> {
    type V = Seq<(u64, R)>;
    closed spec fn view(&self) -> Seq<(u64, R)> { self.entries@ }
}

impl<R: Copy> IdempotencyLog<R> {
    /// The stored result for `key`, if any.
    pub open spec fn get(&self, key: u64) -> Option<R> { lookup_spec(self@, key) }

    /// Append-only: the old log is a prefix of the new one.
    pub open spec fn evolves(pre: Self, post: Self) -> bool {
        pre@.len() <= post@.len() && post@.subrange(0, pre@.len() as int) =~= pre@
    }

    pub fn new() -> (r: Self) ensures forall|k: u64| r.get(k) is None {
        IdempotencyLog { entries: Vec::new() }
    }

    pub fn lookup(&self, key: u64) -> (r: Option<R>)
        ensures r == self.get(key),
    {
        let mut i = self.entries.len();
        assert(self.entries@.take(i as int) =~= self.entries@);   // start: "the first len entries" = all
        while i > 0
            invariant
                i <= self.entries@.len(),
                lookup_spec(self.entries@.take(i as int), key) == lookup_spec(self.entries@, key),
            decreases i,
        {
            // Unfold one step: the last of the first i entries is entry i-1.
            assert(self.entries@.take(i as int).drop_last() =~= self.entries@.take(i - 1));
            if self.entries[i - 1].0 == key { return Some(self.entries[i - 1].1); }
            i = i - 1;
        }
        assert(self.entries@.take(0) =~= Seq::<(u64, R)>::empty());
        None
    }

    pub fn record(&mut self, key: u64, result: R)
        requires old(self).get(key) is None,
        ensures
            final(self).get(key) == Some(result),
            forall|k: u64| k != key ==> #[trigger] final(self).get(k) == old(self).get(k),
            Self::evolves(*old(self), *final(self)),
    {
        self.entries.push((key, result));
        proof {
            assert(self.entries@.drop_last() =~= old(self).entries@);
            assert(self.entries@.subrange(0, old(self).entries@.len() as int) =~= old(self).entries@);
        }
    }
}

} // verus!
