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

Lemma quasi_monotonicity : forall (Γ : set Formula) (α β : Formula), (Γ ⊢ β) -> (α :: Γ) ⊢ β.
Proof.
  intros. induction H.
  - apply Premisse. simpl. right. apply H.
  - apply AxiomInstance.
  - apply (MP _ φ ψ).
    + apply IHdeduction1.
    + apply IHdeduction2.
Qed.

Theorem deduction_metatheorem : forall (Γ : set Formula) (α β : Formula), (α :: Γ ⊢ β) <-> (Γ ⊢ α → β).
Proof. 
  intros. split.
  - intro. remember (α :: Γ) as Δ eqn: Heq in H. induction H.
    + rewrite Heq in H. simpl in H. destruct H.
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
    assert (α :: Γ ⊢ α) as H2.
    + apply Premisse. simpl. left. reflexivity.
    + apply (MP (α :: Γ) α β).
      * apply H1.
      * apply H2.
Qed.

Corollary proof_by_cases : forall (Γ : set Formula) (α β φ : Formula), (α :: Γ ⊢ φ) /\ (β :: Γ ⊢ φ) -> (α ∨ β :: Γ ⊢ φ).
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
  
Corollary proof_by_cases_neg : forall (Γ : set Formula) (α φ : Formula), (α :: Γ ⊢ φ) /\ (¬ α :: Γ ⊢ φ) -> (Γ ⊢ φ).
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