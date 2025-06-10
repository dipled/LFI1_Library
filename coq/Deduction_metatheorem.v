From LFI1 Require Import Utils Language Deduction.
From Stdlib Require Import Arith Constructive_sets.

(* LFI1 is tarskian, i.e., it enjoys reflexivity, monotonicity
   and cut
*)
Proposition lfi1_reflexivity : 
forall (Γ : Ensemble Formula) (φ : Formula),
  φ ∈ Γ -> Γ ⊢ φ.
Proof.
  intros. apply Premisse in H. apply H.
Qed.

Proposition lfi1_monotonicity :
forall (Γ Δ : Ensemble Formula) (φ : Formula),
  Δ ⊢ φ /\ Δ ⊆ Γ -> Γ ⊢ φ.
Proof.
  intros. destruct H. unfold Included in H.
  induction H.
  - apply H0 in H. apply Premisse. apply H.
  - apply AxiomInstance.
  - pose proof H0 as H2. apply IHdeduction1 in H0.
    apply IHdeduction2 in H2. apply (MP Γ φ ψ). apply H0.
    apply H2.
Qed.

Proposition lfi1_cut :
forall (Γ Δ : Ensemble Formula) (φ : Formula),
  Δ ⊢ φ /\ (forall (δ : Formula), δ ∈ Δ -> Γ ⊢ δ) -> Γ ⊢ φ.
Proof.
  intros. destruct H. induction H.
  - apply H0. apply H.
  - apply AxiomInstance.
  - pose proof H0 as H2. apply IHdeduction1 in H0.
    apply IHdeduction2 in H2. apply (MP Γ φ ψ). apply H0.
    apply H2.
Qed.

Lemma id : forall (Γ : Ensemble Formula) (φ : Formula), Γ ⊢ φ → φ.
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

Theorem deduction_metatheorem : forall (Γ : Ensemble Formula) (α β : Formula), 
((Γ ∪ [α]) ⊢ β) <-> (Γ ⊢ α → β).
Proof. 
  intros. split.
  - intro. remember (Γ ∪ [α]) as Δ eqn: Heq in H. induction H.
    + rewrite Heq in H. simpl in H. destruct H.
      * apply (MP Γ x (α → x)).
        -- apply (AxiomInstance Γ (Ax1 x α)).
        -- apply Premisse. apply H.
      * rewrite H. apply id.
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
    pose proof lfi1_monotonicity (Γ ∪ [α]) Γ (α → β). 
    assert (Γ ⊆ Γ ∪ [α]). { unfold Included. intros. left. assumption. }
    apply (MP (Γ ∪ [α]) α β).
    + apply H0. split; assumption.
    + apply Premisse. right. reflexivity.
Qed.

Corollary proof_by_cases : forall (Γ : Ensemble Formula) (α β φ : Formula), 
(Γ ∪ [α] ⊢ φ) /\ (Γ ∪ [β] ⊢ φ) -> (Γ ∪ [α ∨ β] ⊢ φ).
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
  
Corollary proof_by_cases_neg : forall (Γ : Ensemble Formula) (α φ : Formula), 
(Γ ∪ [α] ⊢ φ) /\ (Γ ∪ [¬α] ⊢ φ) -> (Γ ⊢ φ).
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