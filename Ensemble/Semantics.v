Require Import Arith Infinite_sets.
From Coq Require Export String.
From LFI1 Require Import Language.
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

(* Semantic System: Matrix *)

Inductive MatrixDomain : Set :=
  | One
  | Half
  | Zero.

Definition andM (a b : MatrixDomain) : MatrixDomain :=
  match a, b with
  | Zero, _  => Zero
  | _, Zero  => Zero
  | One, One => One
  | _, _     => Half
  end.

Definition orM (a b : MatrixDomain) : MatrixDomain :=
  match a, b with
  | One, _     => One
  | _, One     => One
  | Zero, Zero => Zero
  | _, _       => Half
  end.

Definition impM (a b : MatrixDomain) : MatrixDomain :=
  match a, b with
  | Zero, _ => One
  | _, One  => One
  | _, Half => Half

  | _, Zero => Zero
  end.

Definition negM (a : MatrixDomain) : MatrixDomain :=
  match a with
  | One  => Zero
  | Half => Half
  | Zero => One
  end.

Definition consM (a : MatrixDomain) : MatrixDomain :=
  match a with
  | Half => Zero
  | _    => One
  end.

Notation " x →' y " := 
(impM x y) (at level 80, right associativity).

Notation " x ∧' y " := 
(andM x y) (at level 20, left associativity).

Notation " x ∨' y " := 
(orM x y) (at level 31, left associativity).

Notation " ¬' x " := 
(negM x) (at level 9, right associativity, format "¬' x").

Notation " ∘' x " := 
(consM x) (at level 9, right associativity, format "∘' x").

Fixpoint matrixEvaluation (v : Atom -> MatrixDomain) (φ : Formula) : MatrixDomain :=
  match φ with
  | a ∧ b => andM (matrixEvaluation v a) (matrixEvaluation v b)
  | a ∨ b => orM (matrixEvaluation v a) (matrixEvaluation v b)
  | a → b => impM (matrixEvaluation v a) (matrixEvaluation v b)
  | ¬a    => negM (matrixEvaluation v a)
  | ∘a    => consM (matrixEvaluation v a)
  | #a    => v a
  end.

Definition designatedValue (a : MatrixDomain) : Prop :=
  match a with
  | Zero => False
  | _ => True
  end.

Definition matrixFormulaSAT (v : Atom -> MatrixDomain) (φ : Formula) : Prop := 
designatedValue (matrixEvaluation v φ).

Definition matrixEntails (Γ:Ensemble Formula) p := forall v,
(forall q, q ∈ Γ -> designatedValue (matrixEvaluation v q)) -> 
designatedValue ( matrixEvaluation v p).

Notation " A ⊨ B " := (matrixEntails A B) (at level 110, no associativity).

Example teste : forall (Γ : Ensemble Formula) (α : Formula), 
 Γ ⊨ ¬ (α ∧ ¬α).
Proof.
  intros. unfold matrixEntails. intros.
  unfold matrixFormulaSAT in *. simpl in *. destruct (matrixEvaluation v α); reflexivity.
Qed.

(* Semantic System: Valuations *)