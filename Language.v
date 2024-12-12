Require Import Arith List ListSet.
From Coq Require Export String.


Definition Atom := nat.

Inductive Formula : Set :=
  | Lit    : Atom -> Formula
  | Neg    : Formula -> Formula
  | And    : Formula -> Formula -> Formula
  | Or     : Formula -> Formula -> Formula
  | Imp    : Formula -> Formula -> Formula
  | Cons   : Formula -> Formula.


Notation " x → y " := 
(Imp x y) (at level 80, right associativity).

(* Notation " x ↔ y " := 
(bimplf x y) (at level 50, left associativity). *)

Notation " x ∧ y " := 
(And x y) (at level 20, left associativity).

Notation " x ∨ y " := 
(Or x y) (at level 31, left associativity).

Notation " ¬ x " := 
(Neg x) (at level 9, right associativity, format "¬ x").

Notation " ∘ x " := 
(Cons x) (at level 9, right associativity, format "∘ x").

Notation " # x " :=
(Lit x) (at level 2, no associativity, x constr at level 1, format "# x").

Fixpoint size (f : Formula) : nat :=
 match f with
 | Lit x    => 1
 | Neg a    => 1 + size a
 | And a b  => 1 + size a + size b
 | Or a b   => 1 + size a + size b
 | Imp a b  => 1 + size a + size b
 | Cons a => 2 + size a
 end.

Fixpoint atoms (f : Formula) : set nat :=
  match f with
  | Lit x    => set_add eq_nat_dec x (empty_set nat)
  | Neg a    => atoms a
  | And a b  => set_union eq_nat_dec (atoms a) (atoms b)
  | Or a b   => set_union eq_nat_dec (atoms a) (atoms b)
  | Imp a b  => set_union eq_nat_dec (atoms a) (atoms b)
  | Cons a => atoms a
  end.