Require Import Arith List Infinite_sets.
From Coq Require Export String.
From LFI1 Require Language Syntax Semantics.
Arguments In {U}.
Arguments Add {U}.
Arguments Empty_set {U}.
Arguments Union {U}.
Arguments Singleton {U}.
Arguments Included {U}.

Notation " a ∈ A " := (In A a) (at level 10).
Notation " B ∪ C " := (Union B C) (at level 65, left associativity).
Notation " [ a ] " := (Singleton a) (at level 0, right associativity).
Notation " A ⊆ B " := (Included A B) (at level 70).

Record Logic : Type := mklogic
{ L : Ensemble Set;
  c : Ensemble Set -> Set -> Prop
}.
