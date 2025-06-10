From LFI1 Require Import Utils.
From Stdlib Require Import Arith Constructive_sets.

Definition Atom := nat.

Inductive Formula : Set :=
  | Lit    : Atom -> Formula
  | Neg    : Formula -> Formula
  | And    : Formula -> Formula -> Formula
  | Or     : Formula -> Formula -> Formula
  | Imp    : Formula -> Formula -> Formula
  | Consistency   : Formula -> Formula.

Notation " x → y " := 
(Imp x y) (at level 8, right associativity).

(* Notation " x ↔ y " := 
(bimplf x y) (at level 50, left associativity). *)

Notation " x ∧ y " := 
(And x y) (at level 6, left associativity).

Notation " x ∨ y " := 
(Or x y) (at level 7, left associativity).

Notation " ¬ x " := 
(Neg x) (at level 5, right associativity, format "¬ x").

Notation " ∘ x " := 
(Consistency x) (at level 5, right associativity, format "∘ x").

Notation " # x " :=
(Lit x) (at level 2, no associativity, x constr at level 1, format "# x").
