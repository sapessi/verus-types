# verus-types

Experimental repo inspired by Niko's excellent blog post: [What agents mean for Rust (and vice versa)](https://smallcultfollowing.com/babysteps/blog/2026/10/14/agentic-dev-and-rust/). [Verus](https://github.com/verus-lang/verus) Types is a Rust library types that make common business-logic bugs impossible to write using Verus specs that tell callers exactly what they can rely on. Code that uses these types needs fewer proofs of its own.

| Module and types | Use it for | Rules out, and why it matters | Example |
|---|---|---|---|
| `history`<br>`WriteOnce<T>` | Recording *that* and *when* something happened: `paid_at`, `approved_by`, `paid_off_day` | **Re-setting or clearing a recorded fact.** Rules like "never ship unpaid" or "paid before shipped" become simple comparisons on the stored values, but only if those values can't be quietly rewritten later. | [mortgage_servicing](examples/mortgage_servicing.rs) (payoff date) |
| `history`<br>`Monotonic` | Running totals and counters: amount repaid, refunds issued, login failures, sequence numbers | **Decreasing a total, and overflow.** A total that can be reset (the "reopen bug") lets a customer be refunded or credited twice. If it only grows, the current value *is* the all-time total, so "total ever ≤ limit" is a single check. | [mortgage_servicing](examples/mortgage_servicing.rs) (total paid) |
| `history`<br>`AppendOnly<T>` | Audit logs, ledgers, payment histories, approval trails | **Editing, deleting or reordering past entries.** Auditors and regulators rely on history being complete and unaltered; anything you proved about an old entry stays true forever. | [mortgage_servicing](examples/mortgage_servicing.rs) (payment history) |
| `quantity`<br>`Quantity<U: Unit>` | Any countable amount: money in cents, shares, kWh, bytes, points | **Mixing units, silent overflow, and scaling beyond the amount.** Adding cents to share counts, or dollars to euros, is a type error. Arithmetic that doesn't fit fails explicitly instead of wrapping, and a percentage of an amount can never exceed the amount. | [mortgage_underwriting](examples/mortgage_underwriting.rs) (loan, income, debts) |
| `bounded`<br>`Bounded<MIN, MAX>` | Values with a legal range: credit scores, percentages, basis points, retry counts, page sizes | **Out-of-range values reaching code that assumes the range.** Validate once, at the edge, and every function downstream gets the range for free, with no repeated checks and no forgotten ones. | [mortgage_underwriting](examples/mortgage_underwriting.rs) (credit score) |
| `checked`<br>`Checked<T, I>` | Rules that span several fields: `start <= end`, `refunded <= charged`, lock duration vs. extensions | **Any value that breaks the rule, even briefly.** Updates are all-or-nothing, so there's no half-updated state for other code to see, and the runtime check is proved equal to the rule, so the two can't drift apart. | [mortgage_rate_lock](examples/mortgage_rate_lock.rs) (rate lock rules) |
| `workflow`<br>`State`, `InState<D, S>`, `CanMoveTo` | Entities with a fixed lifecycle: orders, loan applications, claims, deployments, tickets | **Data that doesn't match its state, and moves outside the workflow table.** A "shipped" order without a payment can't exist, and moving a shipped order back to created doesn't compile. Corrupt rows loaded from storage are rejected instead of silently typed. | [order_workflow](examples/order_workflow.rs) |
| `patterns::approval`<br>`Approved` (tracked token) | "Step B only after step A" rules: deploy after review, fund after disclosure, delete after backup | **Skipping the required step, or reusing another item's approval.** The token can only be created by the approval step and is tied to one specific change. It's checked entirely at compile time and costs nothing at runtime. | [approval.rs](src/patterns/approval.rs) |
| `id`<br>`Id<Kind>` | Every identifier that travels through the code: account, customer, order and request ids | **Passing one kind of id where another is expected.** `close(customer_id)` on a function that takes an `Id<Account>` doesn't compile; with bare `u64`s it would silently act on the wrong record. | [banking](examples/banking/ledger.rs) (account ids) |
| `idempotent`<br>`IdempotencyLog<R>` | Anything clients retry after a timeout: payments, transfers, order placement | **Doing the same request twice.** A retry with the same key returns the original result without acting again, and a key's result can never be overwritten. | [banking](examples/banking/bank.rs) (transfers) |
| `versioned`<br>`Versioned<T>` | Records several users or processes edit: profiles, applications, settings | **Lost updates.** Two writers that read the same version can't both succeed; the second gets `Stale` instead of silently overwriting the first. | [versioned.rs](src/versioned.rs) |
| `ratio`<br>`Ratio`, `Rounding` | Interest, fees, pro-rating, currency conversion | **Wrong or accidental rounding, and overflow.** Results are proved correctly rounded (down, up, or half-up) for every input, including exact halves; you choose the mode on purpose. | [banking](examples/banking/interest.rs) (interest) |
| `time_range`<br>`TimeRange`, `InRange` | Time rules from contracts and regulation: deadlines and expiries (dispute windows, offers), waiting periods ("not before 3 days after disclosure"), and windows with both ends | **Acting outside the allowed time, or checking the wrong range.** An action that requires an `InRange` token can only run after a passing check of that specific range; a failed check says whether it was too early or too late. | [banking](examples/banking/disputes.rs) (Reg E) |
| `window`<br>`WindowLimit` | Daily and hourly limits: withdrawals, transfer caps, login attempts | **Exceeding a limit, including by splitting.** The window's total never exceeds the limit, and rejected requests don't use any of it up. | [banking](examples/banking/bank.rs) (daily limit) |
| `redacted`<br>`Redacted<T>`, `Mask`, `Hidden` | Personal or secret data: tax ids, account numbers, dates of birth | **Leaking through logs or debug output.** It prints only what the data type's mask writes, decided once per kind of data (e.g. every `TaxId` shows `***-**-6789`). Raw `Redacted<u64>` can't be printed: say what the value is, or choose `Hidden<u64>` (`[redacted]`). Every real use is an explicit, greppable `expose()`. Hygiene, not a full information-flow proof. | [banking](examples/banking/customer.rs) (`TaxId`) |
| `patterns::transaction`<br>`Db::transaction` | Groups of writes that must happen together: an order plus its shipment record, a transfer between two accounts | **Partial commits and leaked transactions.** On failure nothing is published; on success everything is. The transaction can't outlive its scope, so it can't be left open holding locks. | [transaction.rs](src/patterns/transaction.rs) |

Each type's rustdoc explains when to use it, what it proves, and what it does
**not** prove: `cargo doc --open`.

## Why this approach

Most verification approaches put the proof burden on application developers:
- **Annotating app code with Verus or Dafny** means writing invariants and
  loop specs for every function.
- **Lean or TLA+** means a separate language, or a model that can drift from
  the shipped code.
- **Tests and runtime checks** cover only the inputs someone thought of.

This crate instead uses Rust's type system to *deliver* proofs that are
written and checked once, inside the library types, so application code
inherits them by construction:

| Rust feature | What it guarantees here |
|---|---|
| Phantom type parameters | units, id kinds, workflow states and day-count conventions can't be mixed up |
| Ownership and moves | transitions consume the old state; approval and time-range tokens are unforgeable and tied to one request; transactions can't escape their scope |
| Trait impls | declarative tables domain experts can review: `CanMoveTo` edges, `Invariant` rules, `Mask` policies |
| Module privacy | the closed world: governed data changes only through verified methods |

Most proof obligations become ordinary type errors that Rust developers
already understand; the rest are strong `ensures` clauses the solver uses
automatically in calling code. Proofs are erased at compile time, so
guarantees like conservation of money, at-most-once transfers and correctly
rounded interest cost nothing at runtime. The code stays ordinary Rust, with
its ecosystem and toolchain, and the mutation suite (section 6) checks that
each guarantee actually rejects the bug it claims to.

## 1. Set up

You need Verus, its Rust toolchain, and the Z3 solver that ships with it.

1. Install Verus from the [releases page](https://github.com/verus-lang/verus/releases)
   and put its directory on `PATH` (it contains `verus`, `cargo-verus` and `z3`). This crate uses Verus's newer `&mut` semantics: in `ensures`, `old(x)` is the value on entry and `final(x)` is the value on return.
2. Point Verus at **its own** Z3:

   ```sh
   export VERUS_Z3_PATH="$HOME/verus/z3"     # adjust to your install
   ```

   Without this, Verus may pick up another `z3` on `PATH` (e.g. a pyenv shim)
   and crash with `Got too many empty lines!`.
3. Check the install:

   ```sh
   verus --version
   ```

Last verified with Verus `0.2026.10.04.426d8b0`, Z3 4.16.0, Rust 1.98.1.

## 2. Build

| Command | What it does | Needs Verus? |
|---|---|---|
| `cargo build` | Plain Rust build. The `verus!` macro erases all spec and proof code, so this is an ordinary library. | no |
| `cargo verus build` | Verify, then build. Fails if any proof fails. | yes |
| `cargo doc --open` | API docs, including what each type proves. | no |

## 3. Verify the library

```sh
cargo verus verify
```

Expected last line: `verification results:: 67 verified, 0 errors`. Each
"verified" item is one function whose body Verus proved meets its spec
(`requires`/`ensures`, type invariants, no overflow).

## 4. Run and verify the examples

The mortgage and order examples are single files in `examples/` with a `main`
you can run. `banking` is a multi-module library; see below.

| Example | Uses | What's proved | Expected |
|---|---|---|---|
| `mortgage_underwriting` | `Quantity` (as money), `Bounded` | the approve/decline decision matches the policy table exactly, including the decline reason | 2 verified |
| `mortgage_servicing` | `Monotonic`, `AppendOnly`, `WriteOnce` | total paid never decreases or exceeds principal, equals the payment history, and the payoff date is set once | 7 verified |
| `mortgage_rate_lock` | `Checked` | no rate lock can break its duration and extension rules; failed extensions change nothing | 4 verified |
| `order_workflow` | `workflow` | every order matches its state; only declared moves compile; transitions change exactly what they say; corrupt rows are rejected | 10 verified |
| `banking` (library) | all Layer 1 types | money is conserved; transfers happen at most once per key; holds, daily limits, four-eyes approval and freezes are enforced; accounts only for KYC-verified customers; interest is correctly rounded per day-count convention; disputes only inside the Reg E window | 59 verified |

**Verify an example** (proves it; doesn't run it):

```sh
cargo verus verify --example mortgage_underwriting
```

**Run an example** (plain Rust; no Verus needed):

```sh
cargo run --example mortgage_underwriting
```

### The banking example: an application built in layers

`examples/banking/` builds a small bank from the library types, to show how an
application gets proved properties without its authors writing proofs:

```text
Layer 3  banking    bank · customer (KYC) · interest · disputes
Layer 2  business   money · ledger · audit trail · four-eyes approval
Layer 1  library    the types in src/ (Quantity, Id, IdempotencyLog, WindowLimit, Ratio, ...)
```

Each layer only composes the one below and states its rules; the proofs live
inside the types. Its module docs (`examples/banking/lib.rs`) list what each
module proves.

```sh
cargo verus verify --example banking    # prove it (expected: 59 verified, 0 errors)
cargo test --example banking            # run the 9 end-to-end scenarios
```

The scenarios show the guarantees in action: a retried transfer moves money
once, held funds can't be spent, a $10,000 daily limit can't be split around,
large transfers need two different people, and interest differs correctly
between ACT/360 and ACT/365.

**The one annotation callers write.** `Ledger` and `Bank` carry a
well-formedness predicate, `wf()`, that every method keeps. Your own functions
that take `&mut Bank` state it in their signature:

```rust
fn payroll(bank: &mut Bank<Usd>, ...)
    requires old(bank).wf(),
    ensures final(bank).wf(),
```

That's the only proof-related line application code needs. (A Verus type
invariant would hide it entirely, but Verus doesn't yet allow growing a `Vec`
field of a struct that has one.)

### See a proof fail

The quickest way to see what the proofs do is to break one. In
`examples/mortgage_underwriting.rs`, change the loan-to-value limit in
`underwrite` from `* 80` to `* 85`, so the code no longer matches the policy
table, then verify:

```
$ cargo verus verify --example mortgage_underwriting
error: postcondition not satisfied
  --> examples/mortgage_underwriting.rs:50:13
   |
50 |     ensures r == decide(a),
   |             ^^^^^^^^^^^^^^ failed this postcondition
...
59 |         return Decision::DeclineDebtToIncome;
   |         ------------------------------------ at this exit
```

Verus points at the promise that broke (`r == decide(a)`) and at the return
statement where it can be broken. That's the case of a loan between 80% and
85% LTV, which the code now sends on to the DTI check instead of declining.
`cargo run` would still happily run the broken version, which is the point:
tests only check the inputs you thought of. Undo the change afterwards.

Things that **won't compile at all** (type errors, not proof errors) are
marked with comments in the examples, e.g. moving a shipped order back to
`Created`, or adding `Money<Usd>` to `Money<Eur>`.

## 5. Use the types in your own crate

1. Create a Verus project (`cargo verus new --lib my-crate`) or add this to an
   existing `Cargo.toml`:

   ```toml
   [dependencies]
   vstd = "=0.0.0-2026-10-04-0306"   # must match the vstd version used here
   verus-types = { path = "../verus-types" }

   [package.metadata.verus]
   verify = true
   ```

2. Write code that uses the types inside `verus! { ... }`, so Verus checks it:

   ```rust
   use vstd::prelude::*;
   use verus_types::quantity::{Quantity, Unit};

   verus! {
   pub struct Usd; impl Unit for Usd {}

   fn total(a: Quantity<Usd>, b: Quantity<Usd>) -> (r: Option<Quantity<Usd>>)
       ensures r matches Some(t) ==> t@ == a@ + b@,
   {
       a.checked_add(b)   // its spec is enough: nothing else to prove
   }
   } // verus!
   ```

3. Run `cargo verus verify` in your crate. The examples are the best starting
   points: copy the one closest to your problem.

## 6. Check that the proofs aren't vacuous

```sh
scripts/mutation-test.sh
```

It injects 30 known bugs, one at a time, into a temporary copy of the crate
(15 in the library, 15 in the examples), and requires Verus to reject each one.
A spec that still verifies after its guard is deleted isn't checking
anything. Expected last line: `30 caught, 0 missed or skipped` (about two minutes). Add a mutant
whenever you add a type, a guard or an example.

## Troubleshooting

| Symptom | Fix |
|---|---|
| `Got too many empty lines!` / solver reader thread panics | `VERUS_Z3_PATH` isn't set to Verus's bundled Z3 (see Set up) |
| `can't find crate for vstd` when running `verus file.rs` | Use `cargo verus verify` inside the project; bare `verus` doesn't know the crate's dependencies |
| `to dereference a mutable reference parameter in a postcondition, disambiguate by wrapping it in either old or final` | Newer Verus: in `ensures`, write `old(x)` for the value on entry and `final(x)` for the value on return |
| vstd version errors | The `vstd` version in `Cargo.toml` must match your Verus release (`cargo verus new` writes the right one) |