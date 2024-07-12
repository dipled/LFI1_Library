Require Import LFI1_Syntax.

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

Notation " • x " := 
(Incons x) (at level 9, right associativity, format "• x").

Notation " # x " :=
(Lit x) (at level 1, no associativity, x constr at level 1, format "# x").

