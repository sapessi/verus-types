# verus-types

Inspired by Niko's excellent blog post: [What agents mean for Rust (and vice versa)](https://smallcultfollowing.com/babysteps/blog/2026/10/14/agentic-dev-and-rust/), [Verus](https://github.com/verus-lang/verus) Types is a Rust library types that make common business-logic bugs impossible to write using Verus specs that tell callers exactly what they can rely on. Code that uses these types needs fewer proofs of its own.

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
| `patterns::transaction`<br>`Db::transaction` | Groups of writes that must happen together: an order plus its shipment record, a transfer between two accounts | **Partial commits and leaked transactions.** On failure nothing is published; on success everything is. The transaction can't outlive its scope, so it can't be left open holding locks. | [transaction.rs](src/patterns/transaction.rs) |

Each type's rustdoc explains when to use it, what it proves, and what it does
**not** prove: `cargo doc --open`.

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

Expected last line: `verification results:: 26 verified, 0 errors`. Each
"verified" item is one function whose body Verus proved meets its spec
(`requires`/`ensures`, type invariants, no overflow).

## 4. Run and verify the examples

Each example is a single file in `examples/` with a `main` you can run.

| Example | Uses | What's proved | Expected |
|---|---|---|---|
| `mortgage_underwriting` | `Quantity` (as money), `Bounded` | the approve/decline decision matches the policy table exactly, including the decline reason | 2 verified |
| `mortgage_servicing` | `Monotonic`, `AppendOnly`, `WriteOnce` | total paid never decreases or exceeds principal, equals the payment history, and the payoff date is set once | 7 verified |
| `mortgage_rate_lock` | `Checked` | no rate lock can break its duration and extension rules; failed extensions change nothing | 4 verified |
| `order_workflow` | `workflow` | every order matches its state; only declared moves compile; transitions change exactly what they say; corrupt rows are rejected | 10 verified |

**Verify an example** (proves it; doesn't run it):

```sh
cargo verus verify --example mortgage_underwriting
```

**Run an example** (plain Rust; no Verus needed):

```sh
cargo run --example mortgage_underwriting
```

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

It injects 13 known bugs, one at a time, into a temporary copy of the crate
(7 in the library, 6 in the examples), and requires Verus to reject each one.
A spec that still verifies after its guard is deleted isn't checking
anything. Expected last line: `13 caught, 0 missed or skipped`. Add a mutant
whenever you add a type, a guard or an example.

## Troubleshooting

| Symptom | Fix |
|---|---|
| `Got too many empty lines!` / solver reader thread panics | `VERUS_Z3_PATH` isn't set to Verus's bundled Z3 (see Set up) |
| `can't find crate for vstd` when running `verus file.rs` | Use `cargo verus verify` inside the project; bare `verus` doesn't know the crate's dependencies |
| `to dereference a mutable reference parameter in a postcondition, disambiguate by wrapping it in either old or final` | Newer Verus: in `ensures`, write `old(x)` for the value on entry and `final(x)` for the value on return |
| vstd version errors | The `vstd` version in `Cargo.toml` must match your Verus release (`cargo verus new` writes the right one) |