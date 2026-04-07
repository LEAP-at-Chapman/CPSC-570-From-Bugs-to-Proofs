## Homework: Verified Transactional Inventory

### Scenario

You are implementing a backend inventory component with three operations:

- `Reserve(qty)`: tentatively reserve stock
- `CommitOne()`: commit the earliest pending reservation
- `RollbackAll()`: discard all pending reservations

Business rule: committed + pending stock must never exceed total stock.

### Files

- `homework-transactions.dfy` - single file, divided into:
  - Part 1: preconditions/postconditions and object validity
  - Part 2: iterative implementation with loop invariants and termination
  - Part 3: helper lemmas for recursive sequence properties

### Submission checklist

1. All methods verify with no errors.
2. You do not weaken required business rules.
3. Any additional invariants or lemmas are documented with short comments.
