From Coq Require Export String.
Require Import Arith List ListSet.


Inductive Formula : Set :=
  | Lit    : nat -> Formula
  | Neg    : Formula -> Formula
  | And    : Formula -> Formula -> Formula
  | Or     : Formula -> Formula -> Formula
  | Imp    : Formula -> Formula -> Formula
  | Incons : Formula -> Formula.


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

Notation " ∙ x " := 
(Incons x) (at level 9, right associativity, format "∙ x").

Notation " # x " :=
(Lit x) (at level 2, no associativity, x constr at level 1, format "# x").


Fixpoint size (f : Formula) : nat :=
 match f with
 | Lit x    => 1
 | Neg a    => 1 + size a
 | And a b  => 1 + size a + size b
 | Or a b   => 1 + size a + size b
 | Imp a b  => 1 + size a + size b
 | Incons a => 1 + size a
 end.

Fixpoint literals (f : Formula) : set nat :=
  match f with
  | Lit x    => set_add eq_nat_dec x (empty_set nat)
  | Neg a    => literals a
  | And a b  => set_union eq_nat_dec (literals a) (literals b)
  | Or a b   => set_union eq_nat_dec (literals a) (literals b)
  | Imp a b  => set_union eq_nat_dec (literals a) (literals b)
  | Incons a => literals a
  end.

Fixpoint evenP (n : nat) : Prop :=
  match n with
  | S (S n) => evenP n
  | O => True
  | S O => False
  end.

Fixpoint formulaSAT (v : nat -> Prop) (f : Formula) : Prop :=
  match f with
  | #x    => v x
  | a ∧ b => (formulaSAT v a) /\ (formulaSAT v b)
  | a ∨ b => (formulaSAT v a) \/ (formulaSAT v b)
  | a → b => (formulaSAT v a) -> (formulaSAT v b)
  | ∙a    => formulaSAT v a /\ ~ (formulaSAT v a)
  | ¬a    => ~(formulaSAT v a)
  end.

Definition theory := set Formula.


Fixpoint theorySAT (v : nat -> Prop) (Γ : theory) : Prop :=
  match Γ with
  | nil => True
  | h :: t => (formulaSAT v h) /\ (theorySAT v t)
  end.

Definition entails (Γ : theory) (f : Formula) : Prop :=
forall (v : nat -> Prop), theorySAT v Γ -> formulaSAT v f.

Notation " A |= B " :=
(entails A B) (at level 110, no associativity).

Example teste : forall (Γ : theory) (A B : Formula), 
  ((∙A) :: Γ) |= A ∧ ¬A.
Proof.
  intros.
  unfold entails. intros. apply H. 
Qed. 


