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

Example formula_sat_app : forall (v : Atom -> MatrixDomain) (Γ : set Formula) (α : Formula), matrixFormulaSetSAT v (set_add eq_formula_dec (¬∘α) Γ) -> matrixFormulaSAT v (¬∘α) /\ matrixFormulaSetSAT v Γ.
Proof.
  intros. induction Γ.
  - simpl in H. destruct H. split.
    + apply H.
    + reflexivity.
  - simpl in H. destruct eq_formula_dec in H.
    + split.
      * simpl in H. destruct H. rewrite e. apply H.
      * apply H.
    + split.
      * simpl in H. destruct H. apply IHΓ in H0. apply H0.
      * simpl in H. destruct H. apply IHΓ in H0. split.
        -- apply H.
        -- apply H0.
Qed.


Example teste : forall (Γ : set Formula) (α : Formula), 
 set_add eq_formula_dec (¬∘α) Γ ⊨ α ∧ ¬α.
Proof.
  intros. unfold matrixEntails. intros. apply formula_sat_app in H. destruct H.
  unfold matrixFormulaSAT in H. unfold matrixFormulaSAT. simpl in *.
  destruct (matrixEvaluation v α).
  - destruct H.
  - reflexivity.
  - destruct H.
Qed.

(* Semantic System: Valuations *)