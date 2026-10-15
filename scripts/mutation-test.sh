#!/usr/bin/env bash
# Mutation test: inject one known bug at a time and require that Verus REJECTS it.
#
# A proof that still passes after a bug is injected is vacuous: it isn't
# checking what we think it checks. Each mutant below removes or weakens one
# guard that a type's guarantees depend on.
#
# Mutants are applied to a temporary copy of the crate, so the working tree is
# never modified. Usage:  scripts/mutation-test.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
# Reuse one target dir across mutants so dependencies (vstd) build only once.
export CARGO_TARGET_DIR="$ROOT/target/mutants"

# name | file | perl substitution (must change the file) | example to verify (empty = the library)
# Don't use '|' inside the substitution: it's the field separator. Use s#..#..# instead.
MUTANTS=(
  "Bounded::new drops range check|src/bounded.rs|s/if MIN <= v && v <= MAX \{ Some\(Bounded \{ v \}\) \} else \{ None \}/Some(Bounded { v })/"
  "WriteOnce::set overwrites|src/history.rs|s/if self\.v\.is_some\(\) \{ Err\(AlreadySet\) \} else \{ self\.v = Some\(x\); Ok\(\(\)\) \}/self.v = Some(x); Ok(())/"
  "Monotonic::add wraps on overflow|src/history.rs|s/match self\.v\.checked_add\(d\) \{/match Some(self.v.wrapping_add(d)) {/"
  "Quantity::apply_bps off by one|src/quantity.rs|s#\(p / 10_000\) as u64#(p / 10_000 + 1) as u64#"
  "Checked::update skips check|src/checked.rs|s/if I::check\(&n\) \{/if true {/"
  "approve allows self-approval|src/patterns/approval.rs|s/if approver == c\.author \{ return Err\(SelfApproval\); \}//"
  "transaction commits on Err|src/patterns/transaction.rs|s#Err\(e\) => Err\(e\), // tx dropped: rollback#Err(e) => { self.rows = tx.pending; Err(e) }#"
  "Shipped::check skips payment-time rule|examples/order_workflow.rs|s/\(Some\(p\), Some\(t\)\) => p\.cents > 0 && p\.at <= t, _ => false/(Some(p), Some(t)) => p.cents > 0, _ => false/|order_workflow"
  "ship records the wrong time|examples/order_workflow.rs|s/OrderData \{ shipped_at: Some\(now\), \.\.d \}/OrderData { shipped_at: Some(now + 1), ..d }/|order_workflow"
  "classify forgets the Shipped state|examples/order_workflow.rs|s/    if let Ok\(o\) = Order::<Shipped>::new\(d\) \{ return Some\(AnyOrder::Shipped\(o\)\); \}\n//|order_workflow"
  "underwrite uses 85% LTV|examples/mortgage_underwriting.rs|s/\(a\.property_value\.get\(\) as u128\) \* 80/(a.property_value.get() as u128) * 85/|mortgage_underwriting"
  "apply_payment skips the history|examples/mortgage_servicing.rs|s/        self\.history\.push\(PaymentRec \{ day, cents \}\);\n//|mortgage_servicing"
  "extend forgets to count the extension|examples/mortgage_rate_lock.rs|s/extensions: l\.extensions \+ 1, \.\.\*l/extensions: l.extensions, ..*l/|mortgage_rate_lock"
  "Id::same always says equal|src/id.rs|s/        self\.v == other\.v\n/        true\n/"
  "Versioned::update skips a version|src/versioned.rs|s/self\.version = self\.version \+ 1;/self.version = self.version + 2;/"
  "Deadline::check rejects the last moment|src/deadline.rs|s/if now <= self\.due \{/if now < self.due {/"
  "WindowLimit forgets earlier spending|src/window.rs|s/let base = if in_window \{ self\.total \} else \{ 0 \};/let base = 0;/"
  "IdempotencyLog::lookup misses entries|src/idempotent.rs|s/if self\.entries\[i - 1\]\.0 == key \{/if false {/"
  "Ratio rounds exact values up|src/ratio.rs|s/Rounding::Up => d - 1,/Rounding::Up => d,/"
  "Ratio half-up off by one|src/ratio.rs|s#Rounding::HalfUp => d / 2,#Rounding::HalfUp => d / 2 + 1,#"
  "Ledger::transfer forgets to debit|examples/banking/ledger.rs|s/        self\.balances\.set\(f as usize, fb - amt\);\n        self\.balances\.set\(t as usize/        self.balances.set(t as usize/|banking"
  "Bank spends held funds|examples/banking/bank.rs|s/if amt > bal - h \{/if amt > bal {/|banking"
  "Bank skips the idempotency check|examples/banking/bank.rs|s/        if let Some\(prev\) = self\.transfers\.lookup\(key\) \{ return prev; \}\n        let _amt/        let _amt/|banking"
  "Bank skips the daily limit|examples/banking/bank.rs|s/        if lim\.try_add\(now, amt\)\.is_err\(\) \{ return Err\(Rejection::DailyLimit\); \}\n//|banking"
  "KYC skips sanctions screening|examples/banking/customer.rs|s/d\.kyc_verified_at\.is_some\(\) && d\.sanctions_screened\n/d.kyc_verified_at.is_some()\n/|banking"
  "ACT/365 uses 360 days|examples/banking/interest.rs|s/0 < r <= 366 \{ 365 \}/0 < r <= 366 { 360 }/|banking"
  "Audit accepts back-dated entries|examples/banking/audit.rs|s/        if e\.at < self\.last \{ return Err\(ClockWentBack\); \}\n//|banking"
  "Four-eyes allows self-approval|examples/banking/four_eyes.rs|s/    if maker == checker \{ return Err\(SamePerson\); \}\n//|banking"
  "Reg E window is 59 days|examples/banking/disputes.rs|s/pub const REG_E_WINDOW: u64 = 60 \* DAY;/pub const REG_E_WINDOW: u64 = 59 * DAY;/|banking"
)

caught=0; failed=0
for m in "${MUTANTS[@]}"; do
  IFS='|' read -r name file subst example <<<"$m"
  rm -rf "$WORK/crate"; mkdir -p "$WORK/crate"
  cp -R "$ROOT/Cargo.toml" "$ROOT/src" "$ROOT/examples" "$WORK/crate/"
  [ -f "$ROOT/Cargo.lock" ] && cp "$ROOT/Cargo.lock" "$WORK/crate/"
  perl -0pi -e "$subst" "$WORK/crate/$file"
  if cmp -s "$ROOT/$file" "$WORK/crate/$file"; then
    echo "SKIP   $name  (substitution did not apply; update this script)"; failed=$((failed+1)); continue
  fi
  target=(); [ -n "${example:-}" ] && target=(--example "$example")
  out="$(cd "$WORK/crate" && cargo verus verify "${target[@]+"${target[@]}"}" 2>&1 || true)"
  # Require a VERIFICATION failure for this crate. A compile error would also
  # make `cargo verus verify` fail, but wouldn't show that the proof caught the bug.
  if grep -qE "verification results:: [0-9]+ verified, [1-9][0-9]* errors" <<<"$out"; then
    echo "caught $name"; caught=$((caught+1))
  elif grep -qE "verification results:: [0-9]+ verified, 0 errors" <<<"$(tail -5 <<<"$out")"; then
    echo "MISSED $name  (verification still passes: the proof is vacuous here)"; failed=$((failed+1))
  else
    echo "BROKEN $name  (mutant didn't compile; fix the substitution)"; failed=$((failed+1))
  fi
done

echo "--- $caught caught, $failed missed or skipped"
[ "$failed" -eq 0 ]
