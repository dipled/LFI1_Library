Require Import Arith List Infinite_sets.
From Coq Require Export String.
From LFI1 Require Import Language.
Arguments In {U}.
Arguments Add {U}.
Arguments Empty_set {U}.
Arguments Union {U}.
Arguments Singleton {U}.

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

Definition bimpM (a b : MatrixDomain) : MatrixDomain := 
andM (impM a b) (impM b a).

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

Fixpoint matrixFormulaSetSAT (v : Atom -> MatrixDomain) (Γ : Ensemble Formula) : Prop :=
  match Γ with
  | Empty_set => True
  | Full_set => False
  | Union a b => (matrixFormulaSAT v a) /\ (matrixFormulaSetSAT v b)
  end.

Definition matrixEntails (Γ : list Formula) (φ : Formula) : Prop :=
forall (v : Atom -> MatrixDomain), matrixFormulaSetSAT v Γ -> matrixFormulaSAT v φ.

Notation " A ⊨ B " := (matrixEntails A B) (at level 110, no associativity).

Example teste : forall (Γ : list Formula) (α : Formula), 
 ¬∘α :: Γ ⊨ α ∧ ¬α.
Proof.
  intros. unfold matrixEntails. intros. simpl in H. destruct H as [H0 H1].
  unfold matrixFormulaSAT in *. simpl in *. destruct (matrixEvaluation v α).
  - destruct H0.
  - reflexivity.
  - destruct H0.
Qed.

(* Semantic System: Valuations *)