---
slug: records
title: Records
section: intro
---
# Records

Records are like structs or objects - they group named fields together. In TLA+, records are simply functions whose domain is a set of strings (the field names), but because this pattern occurs so frequently, TLA+ provides dedicated syntax for them.

## Creating Records

```
[name |-> "Alice", age |-> 30]
```

## Accessing Fields

Use dot notation:

```
person.name      \* "Alice"
person.age       \* 30
```

## Record Types (Sets of Records)

```
[name: {"Alice", "Bob"}, age: 0..120]
```

This is the **set of all records** with a `name` field from the given set and an `age` field from 0..120. Useful for `TypeOK` invariants.

## Updating Records (EXCEPT)

Just like functions, use `EXCEPT`:

```
person' = [person EXCEPT !.age = @ + 1]
```

## Records Are Functions

Under the hood, a record is a function from field names (strings) to values:

```
[name |-> "Alice", age |-> 30]
```

is the same as:

```
[x \in {"name", "age"} |-> IF x = "name" THEN "Alice" ELSE 30]
```

## Try It

The spec models a simple user account system with records.

---TLA_BY_EXAMPLE_SPEC---
----------------------------- MODULE Records ---------------------------------
EXTENDS Naturals

CONSTANT Users

VARIABLE accounts

TypeOK == accounts \in [Users -> [balance: Nat, active: BOOLEAN]]

Init == accounts = [u \in Users |-> [balance |-> 100, active |-> TRUE]]

Deposit(u, amt) ==
    /\ accounts[u].active
    /\ amt \in 1..50
    /\ accounts' = [accounts EXCEPT ![u].balance = @ + amt]

Withdraw(u, amt) ==
    /\ accounts[u].active
    /\ amt \in 1..accounts[u].balance
    /\ accounts' = [accounts EXCEPT ![u].balance = @ - amt]

Deactivate(u) ==
    /\ accounts[u].active
    /\ accounts' = [accounts EXCEPT ![u].active = FALSE]

Next == \E u \in Users :
          \/ \E amt \in 1..50 : Deposit(u, amt)
          \/ \E amt \in 1..50 : Withdraw(u, amt)
          \/ Deactivate(u)

NoNegativeBalances == \A u \in Users : accounts[u].balance >= 0

=============================================================================

---TLA_BY_EXAMPLE_CFG---
CONSTANT Users = {alice, bob}
INIT Init
NEXT Next
INVARIANT TypeOK
INVARIANT NoNegativeBalances
