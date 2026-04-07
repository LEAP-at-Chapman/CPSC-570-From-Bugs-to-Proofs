// Transactional Inventory Homework (single file, no repeated definitions)

function PendingSum(pending: seq<nat>): nat
  decreases |pending|
{
  if |pending| == 0 then 0 else pending[0] + PendingSum(pending[1..])
}

class InventoryAccount {
  var total: nat
  var committed: nat
  var reservedLog: seq<nat>

  // =========================
  // Part 1: Specs and Contracts
  // =========================

  // TODO (Part 1):
  // Strengthen this predicate so it captures:
  // 1) committed never exceeds total
  // 2) committed + pending never exceeds total
  predicate Valid()
    reads this
  {
    true
  }

  constructor Init(initialTotal: nat)
    // TODO (Part 1): add ensures clauses for initialized state:
    // 1) After construction, the account's total stock equals the input amount.
    // 2) Initially, nothing has been committed/sold yet.
    // 3) Initially, there are no pending reservations.
    // 4) The object starts in a state that satisfies all invariants/business rules.
  {
    total := initialTotal;
    committed := 0;
    reservedLog := [];
  }

  method Reserve(qty: nat) returns (ok: bool)
    requires Valid()
    modifies this
    // TODO (Part 1): add postconditions for:
    // 1) validity preservation
    // 2) no change to total/committed
    // 3) relation between ok and reservedLog update:
    // 3a) Success when capacity permits: if the pre-state has enough room to add qty
    //     (committed + pending + qty <= total), then the result must indicate success.
    // 3b) On success, append reservation.
    // 3c) On failure, no log change.
  {
    if committed + PendingSum(reservedLog) + qty <= total {
      reservedLog := reservedLog + [qty];
      ok := true;
    } else {
      ok := false;
    }
  }

  method RollbackAll()
    requires Valid()
    modifies this
    // TODO (Part 1): add postconditions for:
    // - validity preservation
    // - committed unchanged
    // - reservedLog cleared
  {
    reservedLog := [];
  }

  // =========================
  // Part 2: Loop Invariants and Termination
  // =========================

  // TODO (Part 2):
  // Verify this method with strong loop invariants (see below)
  method CommitAllPending()
    requires Valid()
    modifies this
    ensures Valid()
    ensures reservedLog == []
    ensures committed == old(committed) + PendingSum(old(reservedLog))
  {
    var startCommitted := committed;
    var pending := reservedLog;
    var i := 0;
    var newlyCommitted := 0;

    while i < |pending|
      // TODO: replace placeholders with useful invariants:
      // 1) The loop index is always within valid bounds: never negative, never past the end of pending.
      // 2) The accumulator newlyCommitted always equals the sum of the part of pending processed so far (the first i items).
      // 3) During the loop body, the field committed itself does not change yet; we only compute into newlyCommitted.
      // 4) The original committed amount plus the full pending total fits within capacity, so the eventual final commit is safe.
      // 5) Total inventory is constant throughout this method (and specifically unchanged from method entry).
      invariant true
      decreases |pending| - i
    {
      newlyCommitted := newlyCommitted + pending[i];
      i := i + 1;
    }

    committed := startCommitted + newlyCommitted;
    reservedLog := [];
  }
}

// =========================
// Part 3: Lemmas and Proof Reuse
// =========================

// TODO (Part 3.1):
// Prove that PendingSum distributes over concatenation.
lemma PendingSumConcat(xs: seq<nat>, ys: seq<nat>)
  ensures PendingSum(xs + ys) == PendingSum(xs) + PendingSum(ys)
  decreases |xs|
{
  if |xs| == 0 {
  } else {
    // Hint: recursive call on xs[1..], then unfold PendingSum once.
  }
}

// TODO (Part 3.2):
// Prove that a prefix sum is never larger than the full sum.
lemma PrefixBound(xs: seq<nat>, i: nat)
  requires i <= |xs|
  ensures PendingSum(xs[..i]) <= PendingSum(xs)
{
  // Hint: combine PendingSumConcat with non-negativity of nat.
}

// TODO (Part 3.3):
// Use your lemmas in this method to finish the proof.
method PrefixCommit(pending: seq<nat>, k: nat) returns (taken: nat)
  requires k <= |pending|
  ensures taken == PendingSum(pending[..k])
  ensures taken <= PendingSum(pending)
{
  var i := 0;
  taken := 0;
  while i < k
    // TODO: add loop invariants
    invariant true
    decreases k - i
  {
    taken := taken + pending[i];
    i := i + 1;
  }

  // TODO: replace this with a proof that uses PrefixBound.
  assert taken <= PendingSum(pending);
}
