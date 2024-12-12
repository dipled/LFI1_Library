Require Import Arith List ListSet.
From Coq Require Export String.
From LFI1 Require Import Language Syntax Semantics.

(* Deduction metatheorem for Hilbert calculus *)

Lemma id : forall (Γ : set Formula) (φ : Formula), Γ ⊢ φ → φ.
Proof.
  intros. 
  pose proof AxiomInstance Γ (Ax2 φ (φ → φ) φ). simpl in H.
  pose proof AxiomInstance Γ (Ax1 φ (φ → φ)). simpl in H0.
  pose proof AxiomInstance Γ (Ax1 φ φ). simpl in H1.
  pose proof MP Γ (φ → (φ → φ) → φ) ((φ → φ → φ) → φ → φ).
  apply H2 in H.
  - pose proof MP Γ (φ → φ → φ) (φ → φ).
    apply H3 in H.
    + apply H.
    + apply H1.
  - apply H0.
Qed.

Lemma quasi_monotonicity : forall (Γ : set Formula) (α β : Formula), 
(Γ ⊢ β) -> (set_add eq_formula_dec α Γ) ⊢ β.
Proof.
  intros. induction H.
  - apply Premisse. apply set_add_intro. right. apply H.
  - apply AxiomInstance.
  - apply (MP _ φ ψ).
    + apply IHdeduction1.
    + apply IHdeduction2.
Qed.

Theorem deduction_metatheorem : forall (Γ : set Formula) (α β : Formula), 
((set_add eq_formula_dec α Γ) ⊢ β) <-> (Γ ⊢ α → β).
Proof. 
  intros. split.
  - intro. remember ((set_add eq_formula_dec α Γ)) as Δ eqn: Heq in H. induction H.
    + rewrite Heq in H. apply set_add_elim in H. destruct H.
      * rewrite H. apply id.
      * apply (MP Γ φ (α → φ)).
        -- apply (AxiomInstance Γ (Ax1 φ α)).
        -- apply Premisse. apply H.
    + apply (MP Γ (instantiate a) (α → (instantiate a))).
      * apply (AxiomInstance Γ (Ax1 (instantiate a) α)).
      * apply AxiomInstance.
    + apply IHdeduction1 in Heq as H1. apply IHdeduction2 in Heq as H2.
      pose proof (AxiomInstance Γ (Ax2 α φ ψ)). simpl in H3.
      pose proof (MP Γ (α → φ → ψ) ((α → φ) → α → ψ)). apply H4 in H3.
      * pose proof (MP Γ (α → φ) (α → ψ)). apply H5 in H3.
        -- apply H3.
        -- apply H2.
      * apply H1.
  - intro. 
    pose proof quasi_monotonicity Γ α (α → β). apply H0 in H as H1.
    assert ((set_add eq_formula_dec α Γ) ⊢ α) as H2.
    + apply Premisse. apply set_add_intro. left. reflexivity.
    + apply (MP (set_add eq_formula_dec α Γ) α β).
      * apply H1.
      * apply H2.
Qed.

Corollary proof_by_cases : forall (Γ : set Formula) (α β φ : Formula), 
((set_add eq_formula_dec α Γ) ⊢ φ) /\ ((set_add eq_formula_dec β Γ) ⊢ φ) -> 
((set_add eq_formula_dec (α ∨ β) Γ) ⊢ φ).
Proof.
  intros. destruct H. 
  pose proof deduction_metatheorem as DMT.
  apply DMT in H. apply DMT in H0.
  apply DMT. pose proof (AxiomInstance Γ (Ax8 α β φ)). simpl in H1.
  pose proof (MP Γ (α → φ) ((β → φ) → α ∨ β → φ)). apply H2 in H1.
  - pose proof (MP Γ (β → φ) (α ∨ β → φ)). apply H3 in H1.
    + apply H1.
    + apply H0.
  - apply H.
Qed.
  
Corollary proof_by_cases_neg : forall (Γ : set Formula) (α φ : Formula), 
((set_add eq_formula_dec α Γ) ⊢ φ) /\ ((set_add eq_formula_dec (¬ α) Γ) ⊢ φ) -> (Γ ⊢ φ).
Proof.
  intros. destruct H.
  pose proof deduction_metatheorem as DMT.
  apply DMT in H. apply DMT in H0.
  pose proof (AxiomInstance Γ (Ax8 α (¬ α) φ)). simpl in H1.
  pose proof (AxiomInstance Γ (Ax10 α)). simpl in H2.
  pose proof (MP Γ (α → φ) ((¬ α → φ) → α ∨ ¬ α → φ)). apply H3 in H1.
  - pose proof (MP Γ (¬ α → φ) (α ∨ ¬ α → φ)). apply H4 in H1.
    + pose proof (MP Γ (α ∨ ¬ α) φ). apply H5 in H1.
      * apply H1.
      * apply H2.
    + apply H0.
  - apply H.
Qed.

(* Soundness *)

Lemma in_set_sat : forall (Γ : set Formula) (α : Formula) (v : Atom -> MatrixDomain),
set_In α Γ /\ matrixFormulaSetSAT v Γ -> matrixFormulaSAT v α.
Proof.
  intros. destruct H. induction Γ.
  - simpl in H. destruct H.
  - simpl in H0. destruct H0. simpl in H. destruct H.
    + rewrite <- H. apply H0.
    + apply IHΓ.
      * apply H.
      * apply H1.
Qed.

Theorem soundness_mat : forall (Γ : set Formula) (α : Formula), 
(Γ ⊢ α) -> (Γ ⊨ α).
Proof.
  intros. induction H.
  - unfold matrixEntails. intros. apply (in_set_sat Γ).
    split.
    + apply H.
    + apply H0.
  - destruct a; unfold matrixEntails; intros; unfold matrixFormulaSAT; simpl;
    try (destruct (matrixEvaluation v f), (matrixEvaluation v f0); reflexivity);
    try (destruct (matrixEvaluation v f), (matrixEvaluation v f0), (matrixEvaluation v f1);
      reflexivity);
    try (destruct (matrixEvaluation v f); reflexivity).
  - unfold matrixEntails in *. intros. unfold matrixFormulaSAT in *.
    specialize (IHdeduction1 v). specialize (IHdeduction2 v). 
    apply IHdeduction1 in H1 as H2.
    apply IHdeduction2 in H1 as H3.
    simpl in H2, H3. destruct (matrixEvaluation v φ), (matrixEvaluation v ψ); 
    try reflexivity;
    try destruct H2;
    try destruct H3.
Qed.