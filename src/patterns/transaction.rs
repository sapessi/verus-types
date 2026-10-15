//! Pattern: scoped transactions, approximating linear types.
//!
//! The transaction is passed BY VALUE into the closure and must be handed back
//! to commit. If the closure drops it, there's nothing to commit, so
//! [`Db::transaction`] rolls back. Leaking it past the scope is impossible.
//! This "ownership-passing" style also avoids `&mut` closure arguments, which
//! Verus handles less well.

use vstd::prelude::*;

verus! {

pub struct Db { rows: Vec<u64> }
pub struct Tx { pending: Vec<u64> }

impl View for Db { type V = Seq<u64>; closed spec fn view(&self) -> Seq<u64> { self.rows@ } }
impl View for Tx { type V = Seq<u64>; closed spec fn view(&self) -> Seq<u64> { self.pending@ } }

impl Db {
    /// Runs `f` inside a transaction: **commit on `Ok`, roll back on `Err`**.
    ///
    /// # Use it for
    /// Any group of writes that must happen together or not at all: updating
    /// an order plus inserting its shipment record, moving money between two
    /// accounts, writing a row plus its audit-log entry.
    ///
    /// # Example
    /// ```ignore
    /// db.transaction(|mut tx| {
    ///     tx.write(order_row);
    ///     tx.write(shipment_row);
    ///     if !valid { return (tx, Err(Invalid)); }   // rolled back
    ///     (tx, Ok(()))                                // both writes committed
    /// })?;
    /// ```
    ///
    /// # What it proves
    /// - **Atomicity:** on `Err`, the database view is exactly what it was
    ///   before. On `Ok`, it's exactly the transaction's final pending view,
    ///   so no partial commits.
    /// - **No leaked transactions:** the `Tx` is created and consumed inside
    ///   this call and can't escape the closure's scope. It's the stable-Rust
    ///   substitute for a "must be consumed exactly once" (linear) type.
    ///
    /// # What it does NOT prove
    /// - Isolation from other concurrent transactions. That's a property of
    ///   the real database and belongs in an `assume trusted` block
    ///   (e.g. "SERIALIZABLE isolation").
    /// - That the closure's writes are *correct*. Give the closure a spec;
    ///   its `ensures` flow into `r is Ok ==> …` above.
    ///
    /// # Verus notes
    /// The closure takes the `Tx` by value and hands it back
    /// ("ownership passing"), which avoids `&mut` closure arguments. The
    /// `exists` in the `Ok` postcondition is how Verus says "whatever the
    /// closure's spec allowed". Callers usually instantiate it immediately
    /// with their closure's own `ensures`.
    pub fn transaction<R, E, F>(&mut self, f: F) -> (r: Result<R, E>)
        where F: FnOnce(Tx) -> (Tx, Result<R, E>)
        requires
            forall|tx: Tx| tx@ == old(self)@ ==> #[trigger] f.requires((tx,)),
        ensures
            // Err: nothing published. Ok: the closure's final pending view is published.
            r is Err ==> final(self)@ == old(self)@,
            r is Ok  ==> exists|tx_in: Tx, tx_out: Tx|
                tx_in@ == old(self)@ && f.ensures((tx_in,), (tx_out, r)) && final(self)@ == tx_out@,
            // An `exists` in the postcondition is unavoidable for "whatever the
            // closure did"; callers instantiate it with their closure's ensures.
    {
        let tx = Tx { pending: self.rows.clone() };
        let (tx, res) = f(tx);
        match res {
            Ok(v)  => { self.rows = tx.pending; Ok(v) }
            Err(e) => Err(e), // tx dropped: rollback
        }
    }
}

} // verus!
