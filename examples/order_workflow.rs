//! An order workflow with `workflow::{State, InState, CanMoveTo}`.
//!
//!   Created --pay--> Paid --ship--> Shipped
//!
//! Each state describes what the order's DATA looks like; the `CanMoveTo` impls
//! are the workflow table. Notice the transitions contain no `if` guards: a move
//! succeeds exactly when the new data fits the target state's description.
//!
//! Proved: every `Order<S>` matches state S's description, transitions change
//! exactly the fields they say, and `classify` gives untrusted data a type only
//! if it matches a state. Run: `cargo run --example order_workflow`

use vstd::prelude::*;
use verus_types::workflow::{CanMoveTo, InState, State};

verus! {

#[derive(Copy, Clone, Debug)]
pub struct Payment { pub at: u64, pub cents: u64 }

#[derive(Copy, Clone, Debug)]
pub struct OrderData {
    pub id: u64,
    pub payment: Option<Payment>,
    pub shipped_at: Option<u64>,
}

// ---- The states: what the data looks like in each one ----------------------

pub struct Created;
pub struct Paid;
pub struct Shipped;

impl State<OrderData> for Created {
    open spec fn holds(d: OrderData) -> bool { d.payment is None && d.shipped_at is None }
    fn check(d: &OrderData) -> (r: bool) ensures r == Self::holds(*d) {
        d.payment.is_none() && d.shipped_at.is_none()
    }
}

impl State<OrderData> for Paid {
    open spec fn holds(d: OrderData) -> bool {
        d.payment matches Some(p) && p.cents > 0 && d.shipped_at is None
    }
    fn check(d: &OrderData) -> (r: bool) ensures r == Self::holds(*d) {
        match d.payment { Some(p) => p.cents > 0 && d.shipped_at.is_none(), None => false }
    }
}

impl State<OrderData> for Shipped {
    // Shipping can't be timestamped before payment (clock skew between services).
    open spec fn holds(d: OrderData) -> bool {
        match (d.payment, d.shipped_at) {
            (Some(p), Some(t)) => p.cents > 0 && p.at <= t,
            _ => false,
        }
    }
    fn check(d: &OrderData) -> (r: bool) ensures r == Self::holds(*d) {
        match (d.payment, d.shipped_at) { (Some(p), Some(t)) => p.cents > 0 && p.at <= t, _ => false }
    }
}

// ---- The workflow table: the only allowed moves ----------------------------

impl CanMoveTo<Paid> for Created {}
impl CanMoveTo<Shipped> for Paid {}

pub type Order<S> = InState<OrderData, S>;

// ---- Transitions: say what changes; the state check does the rest ----------

pub fn new_order(id: u64) -> (r: Order<Created>)
    ensures r@ == (OrderData { id, payment: None, shipped_at: None }),
{
    match Order::<Created>::new(OrderData { id, payment: None, shipped_at: None }) {
        Ok(o) => o,
        Err(_) => vstd::pervasive::unreached(), // proved impossible: the data is Created
    }
}

/// Rejected (order handed back) if `cents == 0`, because that isn't a valid Paid order.
pub fn pay(o: Order<Created>, cents: u64, now: u64) -> (r: Result<Order<Paid>, Order<Created>>)
    ensures
        match r {
            Ok(p)     => p@ == OrderData { payment: Some(Payment { at: now, cents }), ..o@ },
            Err(back) => back@ == o@ && cents == 0,
        },
{
    let d = *o.get();
    match o.advance::<Paid>(OrderData { payment: Some(Payment { at: now, cents }), ..d }) {
        Ok(p) => Ok(p),
        Err((back, _)) => Err(back),
    }
}

/// Rejected (order handed back) if `now` is before the payment time.
pub fn ship(o: Order<Paid>, now: u64) -> (r: Result<Order<Shipped>, Order<Paid>>)
    ensures
        match r {
            Ok(s)     => s@ == OrderData { shipped_at: Some(now), ..o@ },
            Err(back) => back@ == o@ && now < o@.payment.unwrap().at,
        },
{
    let d = *o.get();
    match o.advance::<Shipped>(OrderData { shipped_at: Some(now), ..d }) {
        Ok(s) => Ok(s),
        Err((back, _)) => Err(back),
    }
}

// ---- Loading untrusted data (from a DB, a message) -------------------------

pub enum AnyOrder { Created(Order<Created>), Paid(Order<Paid>), Shipped(Order<Shipped>) }

/// Per-workflow proof: no data is in two states at once.
proof fn states_disjoint(d: OrderData)
    ensures
        !(Created::holds(d) && Paid::holds(d)),
        !(Created::holds(d) && Shipped::holds(d)),
        !(Paid::holds(d) && Shipped::holds(d)),
{}

/// The only way to type untrusted data. Corrupt data matches no state and is rejected.
pub fn classify(d: OrderData) -> (r: Option<AnyOrder>)
    ensures
        r matches Some(AnyOrder::Created(o)) ==> o@ == d && Created::holds(d),
        r matches Some(AnyOrder::Paid(o))    ==> o@ == d && Paid::holds(d),
        r matches Some(AnyOrder::Shipped(o)) ==> o@ == d && Shipped::holds(d),
        r is None ==> !Created::holds(d) && !Paid::holds(d) && !Shipped::holds(d),
{
    if let Ok(o) = Order::<Created>::new(d) { return Some(AnyOrder::Created(o)); }
    if let Ok(o) = Order::<Paid>::new(d)    { return Some(AnyOrder::Paid(o)); }
    if let Ok(o) = Order::<Shipped>::new(d) { return Some(AnyOrder::Shipped(o)); }
    None
}

} // verus!

fn main() {
    let o = new_order(7);
    let o = pay(o, 0, 10).err().expect("zero payment is rejected");
    println!("pay $0:          rejected, order still Created");
    let o = pay(o, 25_00, 10).ok().expect("valid payment");
    println!("pay $25 at t=10: {:?}", o.get().payment);
    let o = ship(o, 9).err().expect("ship before payment time is rejected");
    println!("ship at t=9:     rejected (clock skew), order still Paid");
    let o = ship(o, 12).ok().expect("valid shipment");
    println!("ship at t=12:    shipped_at = {:?}", o.get().shipped_at);
    // Doesn't compile: there's no `impl CanMoveTo<Created> for Shipped`.
    // let back = o.advance::<Created>(*o.get());

    let corrupt = OrderData { id: 8, payment: None, shipped_at: Some(5) }; // shipped, never paid
    println!("classify corrupt row: {}", if classify(corrupt).is_some() { "typed" } else { "rejected" });
}
