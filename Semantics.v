Require Import Arith List ListSet.
From Coq Require Export String.
From LFI1 Require Import Language.

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

Definition matrixFormulaSAT (v : Atom -> MatrixDomain) (φ : Formula) : Prop := designatedValue (matrixEvaluation v φ).

Fixpoint matrixFormulaSetSAT (v : Atom -> MatrixDomain) (Γ : set Formula) : Prop :=
  match Γ with
  | nil => True
  | h :: t => (matrixFormulaSAT v h) /\ (matrixFormulaSetSAT v t)
  end.

Definition matrixEntails (Γ : set Formula) (φ : Formula) : Prop :=
forall (v : Atom -> MatrixDomain), matrixFormulaSetSAT v Γ -> matrixFormulaSAT v φ.

Notation " A ⊨ B " := (matrixEntails A B) (at level 110, no associativity).

Example teste : forall (Γ : set Formula) (α : Formula), 
  ¬∘α::Γ ⊨ α ∧ ¬α.
Proof.
  intros. unfold matrixEntails. intros.
  destruct H. unfold matrixFormulaSAT. unfold matrixFormulaSAT in H.
  simpl. simpl in H. destruct ((matrixEvaluation v α)).
  - simpl in H. exfalso; apply H.
  - reflexivity.
  - simpl in H. exfalso; apply H.
Qed.

(* Semantic System: Valuations *)