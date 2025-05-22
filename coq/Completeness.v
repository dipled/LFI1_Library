From LFI1 Require Import Utils Language Syntax Semantics.
From LFI1 Require Import Deduction_metatheorem Soundness.
Require Import Coq.Program.Equality.
From Stdlib Require Import Arith Classical_sets Epsilon.
From LFI1 Require Import Cardinality.

(* From now on, we need to include the Classical_sets and
   Epsilon modules, which add the concepts needed to construct 
   the proof of completeness. These modules, however, include 
   the excluded middle and epsilon axioms, which result in 
   proof irrelevance.
*)

(* We then state a trivial fact about sets *)
Proposition In_lem {U : Type} : forall (A : Ensemble U) (x : U),
  x ∈ A \/ x ∉ A.
Proof. intros. apply classic. Qed.

(* Defining maximal nontrivial sets of formulae w.r.t a given formula *)
Definition maximal_nontrivial (Γ : Ensemble Formula) (φ : Formula) : Prop :=
  ~ Γ ⊢ φ /\ (forall (ψ : Formula), ~ψ ∈ Γ -> (Γ ∪ [ψ] ⊢ φ)).

(* Defining closed theories *)
Definition closed_theory (Γ : Ensemble Formula) : Prop := forall φ : Formula, 
  Γ ⊢ φ <-> φ ∈ Γ.

(* Every maximal nontrivial set of formulae w.r.t to a given formula 
   is a closed theory
*)
Lemma maximal_nontrivial_is_closed : forall (Γ : Ensemble Formula) (φ : Formula),
  maximal_nontrivial Γ φ -> closed_theory Γ.
Proof.
  intros. unfold maximal_nontrivial in H; destruct H.
  unfold closed_theory. intros γ. split.
  - intros. 
    pose proof (In_lem Γ γ).
    destruct H2. apply H2. apply H0 in H2.
    unfold Add in H2. 
    pose proof (lfi1_cut Γ (Γ ∪ [γ]) φ).
    assert ((Γ ∪ [γ]) ⊢ φ /\ (forall δ : Formula, δ ∈ (Γ ∪ [γ]) -> Γ ⊢ δ)).
    + split.
      * apply H2.
      * intros. destruct H4.
        -- apply Premisse. apply H4.
        -- inversion H4. rewrite <- H5.
           apply H1.
    + apply H3 in H4. exfalso. apply H. apply H4.
  - intros. apply Premisse. apply H1.
Qed.

(** Defining the valuation used in the completeness proof *)
Definition completeness_valuation (Γ : Ensemble Formula) : 
Formula -> BivaluationDomain :=
  fun x =>
          match (strong_lem (x ∈ Γ)) with
          | left _ => ⊤
          | right _ => ⊥
          end.

(** Proving that completeness_valuation is indeed a bivaluation *)
Lemma completeness_valuation_is_bivaluation : forall (Γ : Ensemble Formula) (φ : Formula),
  (maximal_nontrivial Γ φ) -> bivaluation (completeness_valuation Γ).
Proof.
  intros. unfold maximal_nontrivial in H. destruct H.
  unfold bivaluation. try repeat split; unfold completeness_valuation in *.
  - destruct (strong_lem(φ0 ∧ ψ ∈ Γ)); 
    try discriminate H1. destruct (strong_lem (φ0 ∈ Γ)).
    + reflexivity.
    + pose proof (Premisse Γ (φ0 ∧ ψ)).
      apply H2 in i. pose proof (AxiomInstance Γ (Ax4 φ0 ψ)); simpl in H3.
      pose proof (MP Γ (φ0 ∧ ψ) φ0). apply H4 in H3.
      * specialize (H0 φ0). apply H0 in n.
        pose proof (lfi1_cut Γ (Γ ∪ [φ0]) φ). exfalso. apply H.
        apply H5. split.
        -- apply n.
        -- intros. destruct H6.
          ++ apply Premisse. apply H6.
          ++ inversion H6. rewrite <- H7. apply H3.
      * apply i.
  - destruct (strong_lem(φ0 ∧ ψ ∈ Γ));
    try discriminate H1. destruct (strong_lem (ψ ∈ Γ)).
    + reflexivity.
    + pose proof (Premisse Γ (φ0 ∧ ψ)).
      apply H2 in i. pose proof (AxiomInstance Γ (Ax5 φ0 ψ)); simpl in H3.
      pose proof (MP Γ (φ0 ∧ ψ) ψ). apply H4 in H3.
      * specialize (H0 ψ). apply H0 in n.
        pose proof (lfi1_cut Γ (Γ ∪ [ψ]) φ). exfalso. apply H.
        apply H5. split.
        -- apply n.
        -- intros. destruct H6.
          ++ apply Premisse. apply H6.
          ++ inversion H6. rewrite <- H7. apply H3.
      * apply i.
  - intros. destruct H1.
    destruct (strong_lem (φ0 ∈ Γ)), (strong_lem (ψ ∈ Γ));
    try discriminate H1; try discriminate H2.
    destruct H1, H2. destruct (strong_lem (φ0 ∧ ψ ∈ Γ)); try reflexivity.
    apply H0 in n. pose proof (AxiomInstance Γ (Ax3 φ0 ψ)); simpl in H1.
    pose proof (MP Γ φ0 ψ → φ0 ∧ ψ). apply H2 in H1.
    + pose proof (MP Γ ψ φ0 ∧ ψ). apply H3 in H1.
      * pose proof (lfi1_cut Γ (Γ ∪ [φ0 ∧ ψ]) φ). exfalso. apply H.
        apply H4. split.
        -- apply n.
        -- intros. destruct H5.
           ++ apply Premisse. apply H5.
           ++ inversion H5. apply H1.
      * apply Premisse. apply i0.
    + apply Premisse. apply i.
  - intros. destruct (strong_lem (φ0 ∨ ψ ∈ Γ));
    try discriminate H1. destruct (strong_lem (φ0 ∈ Γ)), (strong_lem (ψ ∈ Γ));
    try (left; reflexivity); try (right; reflexivity). exfalso. apply H.
    apply H0 in n. apply H0 in n0. pose proof (proof_by_cases Γ φ0 ψ φ).
    assert (Γ ∪ [φ0] ⊢ φ /\ Γ ∪ [ψ] ⊢ φ); try (split; assumption).
    apply H2 in H3. pose proof (lfi1_cut Γ (Γ ∪ [φ0 ∨ ψ]) φ).
    apply H4. split; try assumption. intros.
    destruct H5.
    + apply Premisse. apply H5.
    + inversion H5. apply Premisse. apply i.
  - intros. destruct H1.
    + destruct (strong_lem (φ0 ∈ Γ)); try discriminate H1.
      destruct (strong_lem (φ0 ∨ ψ ∈ Γ)); try reflexivity.
      apply H0 in n. exfalso. apply H. pose proof (lfi1_cut Γ (Γ ∪ [φ0 ∨ ψ]) φ).
      apply H2. split; try assumption. intros. destruct H3.
      * apply Premisse. assumption.
      * inversion H3. pose proof (Premisse Γ φ0). apply H5 in i.
        pose proof (AxiomInstance Γ (Ax6 φ0 ψ)); simpl in H6.
        pose proof (MP Γ φ0 φ0 ∨ ψ). apply H7 in H6; assumption.
    + destruct (strong_lem (ψ ∈ Γ)); try discriminate H1.
      destruct (strong_lem (φ0 ∨ ψ ∈ Γ)); try reflexivity.
      apply H0 in n. exfalso. apply H. pose proof (lfi1_cut Γ (Γ ∪ [φ0 ∨ ψ]) φ).
      apply H2. split; try assumption. intros. destruct H3.
      * apply Premisse. assumption.
      * inversion H3. pose proof (Premisse Γ ψ). apply H5 in i.
        pose proof (AxiomInstance Γ (Ax7 φ0 ψ)); simpl in H6.
        pose proof (MP Γ ψ φ0 ∨ ψ). apply H7 in H6; assumption.
  - intros.
    destruct (strong_lem (φ0 → ψ ∈ Γ)); try discriminate H1; destruct H1.
    destruct (strong_lem (φ0 ∈ Γ)), (strong_lem (ψ ∈ Γ)); try (left; reflexivity);
    try (right; reflexivity). exfalso; apply H. apply H0 in n.
    pose proof (lfi1_cut Γ (Γ ∪ [ψ]) φ). apply H1. split; try assumption.
    intros. destruct H2.
    + apply Premisse. apply H2.
    + inversion H2. rewrite <- H3. pose proof (Premisse Γ φ0).
      pose proof (Premisse Γ φ0 → ψ). apply H5 in i. apply H4 in i0.
      pose proof (MP Γ φ0 ψ). apply H6 in i; assumption.
  - intros. destruct H1.
    + destruct (strong_lem (φ0 ∈ Γ)) in H1; try discriminate H1.
      destruct (strong_lem (φ0 → ψ ∈ Γ)); try reflexivity.
      exfalso. apply H. pose proof (AxiomInstance Γ (Ax9 φ0 ψ)); simpl in H2.
      apply H0 in n. apply H0 in n0. apply deduction_metatheorem in n.
      apply deduction_metatheorem in n0. pose proof (AxiomInstance Γ (Ax8 φ0 → ψ φ0 φ));
      simpl in H3. pose proof (MP Γ ((φ0 → ψ) → φ)) ((φ0 → φ) → (φ0 → ψ) ∨ φ0 → φ).
      apply H4 in H3.
      * pose proof (MP Γ ((φ0 → φ)) ((φ0 → ψ) ∨ φ0 → φ)).
        apply H5 in H3.
        -- pose proof (MP Γ ((φ0 → ψ) ∨ φ0) φ). apply H6 in H3.
           ++ apply H3.
           ++ apply H2.
        -- apply n.
      * apply n0.
    + destruct (strong_lem (ψ ∈ Γ)) in H1; try discriminate H1.
      destruct (strong_lem (φ0 → ψ ∈ Γ)); try reflexivity.
      exfalso. apply H. apply H0 in n. pose proof (AxiomInstance Γ (Ax1 ψ φ0)); simpl in H2.
      pose proof (MP Γ ψ φ0 → ψ). apply H3 in H2.
      * pose proof (lfi1_cut Γ (Γ ∪ [φ0 → ψ]) φ). apply H4. split; try assumption.
        intros. destruct H5.
        -- apply Premisse. apply H5.
        -- inversion H5. apply H2.
      * apply Premisse. apply i.
  - unfold vNeg. intros. destruct (strong_lem (¬φ0 ∈ Γ)); try discriminate H1.
    destruct (strong_lem (φ0 ∈ Γ)); try reflexivity. apply H0 in n.
    apply H0 in n0. pose proof (proof_by_cases_neg Γ φ0 φ).
    exfalso. apply H. apply H2. split; assumption.
  - unfold vCon. intros. destruct (strong_lem (∘φ0 ∈ Γ)); try discriminate H1.
    destruct (strong_lem (φ0 ∈ Γ)), (strong_lem (¬φ0 ∈ Γ)); try (left; reflexivity);
    try (right; reflexivity). exfalso. apply H. pose proof (AxiomInstance Γ (bc1 φ0 φ));
    simpl in H2. apply (Premisse Γ ∘φ0) in i. apply (Premisse Γ φ0) in i0.
    apply (Premisse Γ ¬φ0) in i1. apply (MP Γ ∘φ0 φ0 → ¬φ0 → φ) in H2.
    + apply (MP Γ φ0 ¬φ0 → φ) in H2.
      * apply (MP Γ ¬φ0 φ) in H2; assumption.
      * apply i0.
    + apply i.
  - destruct (strong_lem (¬∘φ0 ∈ Γ)); try discriminate H1.
    destruct (strong_lem (φ0 ∈ Γ)); try reflexivity.
    apply (Premisse Γ ¬∘φ0) in i. pose proof (AxiomInstance Γ (ci φ0)); simpl in H2.
    apply (MP Γ ¬∘φ0 (φ0 ∧ ¬φ0)) in H2; try assumption.
    pose proof (AxiomInstance Γ (Ax4 φ0 ¬φ0)); simpl in H3.
    apply (MP Γ φ0 ∧ ¬φ0 φ0) in H3; try assumption. apply H0 in n.
    pose proof (lfi1_cut Γ (Γ ∪ [φ0]) φ). exfalso; apply H; apply H4.
    split; try assumption. intros. destruct H5.
    + apply Premisse. apply H5.
    + inversion H5. rewrite <- H6. apply H3.
  - destruct (strong_lem (¬∘φ0 ∈ Γ)); try discriminate H1.
    destruct (strong_lem (¬φ0 ∈ Γ)); try reflexivity.
    apply (Premisse Γ ¬∘φ0) in i. pose proof (AxiomInstance Γ (ci φ0)); simpl in H2.
    apply (MP Γ ¬∘φ0 (φ0 ∧ ¬φ0)) in H2; try assumption.
    pose proof (AxiomInstance Γ (Ax5 φ0 ¬φ0)); simpl in H3.
    apply (MP Γ φ0 ∧ ¬φ0 ¬φ0) in H3; try assumption. apply H0 in n.
    pose proof (lfi1_cut Γ (Γ ∪ [¬φ0]) φ). exfalso; apply H; apply H4.
    split; try assumption. intros. destruct H5.
    + apply Premisse. apply H5.
    + inversion H5. apply H3.
  - intros. destruct (strong_lem (¬¬φ0 ∈ Γ)); try discriminate H1.
    destruct (strong_lem (φ0 ∈ Γ)); try reflexivity.
    exfalso; apply H. apply H0 in n. apply (Premisse Γ ¬¬φ0) in i.
    pose proof (AxiomInstance Γ (cf φ0)); simpl in H2.
    apply (MP Γ ¬¬φ0 φ0) in H2; try assumption.
    pose proof (lfi1_cut Γ (Γ ∪ [φ0]) φ). apply H3; split; try assumption.
    intros. destruct H4.
    + apply Premisse. apply H4.
    + inversion H4. rewrite <- H5. apply H2.
  - intros. destruct (strong_lem (φ0 ∈ Γ)); try discriminate H1.
    destruct (strong_lem (¬¬φ0 ∈ Γ)); try reflexivity.
    exfalso; apply H. apply H0 in n. apply (Premisse Γ φ0) in i.
    pose proof (AxiomInstance Γ (ce φ0)); simpl in H2.
    apply (MP Γ φ0 ¬¬φ0) in H2; try assumption.
    pose proof (lfi1_cut Γ (Γ ∪ [¬¬φ0]) φ). apply H3; split; try assumption.
    intros. destruct H4.
    + apply Premisse. apply H4.
    + inversion H4. apply H2.
  - intros. destruct (strong_lem (¬(φ0 ∧ ψ) ∈ Γ)); try discriminate H1.
    destruct (strong_lem (¬φ0 ∈ Γ)), (strong_lem (¬ψ ∈ Γ));
    try (left; reflexivity); try (right; reflexivity).
    apply (Premisse Γ ¬(φ0 ∧ ψ)) in i. apply H0 in n.
    apply H0 in n0. pose proof (proof_by_cases Γ ¬φ0 ¬ψ φ).
    exfalso. apply H. pose proof (AxiomInstance Γ (negland1 φ0 ψ));
    simpl in H3. apply (MP Γ ¬(φ0 ∧ ψ) ¬φ0 ∨ ¬ψ) in H3; try assumption.
    apply (lfi1_cut Γ (Γ ∪ [¬φ0 ∨ ¬ψ]) φ). split.
    + apply H2. split; assumption.
    + intros. destruct H4.
      * apply Premisse. apply H4.
      * inversion H4. apply H3.
  - intros. destruct H1.
    + destruct (strong_lem (¬φ0 ∈ Γ)); try discriminate H1.
      destruct (strong_lem (¬(φ0 ∧ ψ) ∈ Γ)); try reflexivity.
      apply H0 in n. exfalso. apply H. apply (Premisse Γ ¬φ0) in i.
      pose proof (AxiomInstance Γ (Ax6 ¬φ0 ¬ψ)); simpl in H2.
      apply (MP Γ ¬φ0 ¬φ0 ∨ ¬ψ) in H2; try assumption.
      pose proof (AxiomInstance Γ (negland2 φ0 ψ)); simpl in H3.
      apply (MP Γ ¬φ0 ∨ ¬ψ ¬(φ0 ∧ ψ)) in H3; try assumption.
      apply (lfi1_cut Γ (Γ ∪ [¬(φ0 ∧ ψ)]) φ). split; try assumption.
      intros. destruct H4.
      * apply Premisse. apply H4.
      * destruct H4. apply H3.
    + destruct (strong_lem (¬ψ ∈ Γ)); try discriminate H1.
      destruct (strong_lem (¬(φ0 ∧ ψ) ∈ Γ)); try reflexivity.
      apply H0 in n. exfalso. apply H. apply (Premisse Γ ¬ψ) in i.
      pose proof (AxiomInstance Γ (Ax7 ¬φ0 ¬ψ)); simpl in H2.
      apply (MP Γ ¬ψ ¬φ0 ∨ ¬ψ) in H2; try assumption.
      pose proof (AxiomInstance Γ (negland2 φ0 ψ)); simpl in H3.
      apply (MP Γ ¬φ0 ∨ ¬ψ ¬(φ0 ∧ ψ)) in H3; try assumption.
      apply (lfi1_cut Γ (Γ ∪ [¬(φ0 ∧ ψ)]) φ). split; try assumption.
      intros. destruct H4.
      * apply Premisse. apply H4.
      * destruct H4. apply H3.
  - destruct (strong_lem (¬(φ0 ∨ ψ) ∈ Γ)); try discriminate H1.
    destruct (strong_lem (¬φ0 ∈ Γ)); try reflexivity.
    apply H0 in n. apply (Premisse Γ ¬(φ0 ∨ ψ)) in i.
    pose proof (AxiomInstance Γ (neglor1 φ0 ψ)); simpl in H2.
    apply (MP Γ ¬(φ0 ∨ ψ) ¬φ0 ∧ ¬ψ) in H2; try assumption.
    pose proof (AxiomInstance Γ (Ax4 ¬φ0 ¬ψ)); simpl in H3.
    apply (MP Γ ¬φ0 ∧ ¬ψ ¬φ0) in H3; try assumption.
    exfalso. apply H. apply (lfi1_cut Γ (Γ ∪ [¬φ0]) φ). split; try assumption.
    intros. destruct H4.
    + apply Premisse. apply H4.
    + destruct H4. apply H3.
  - destruct (strong_lem (¬(φ0 ∨ ψ) ∈ Γ)); try discriminate H1.
    destruct (strong_lem (¬ψ ∈ Γ)); try reflexivity.
    apply H0 in n. apply (Premisse Γ ¬(φ0 ∨ ψ)) in i.
    pose proof (AxiomInstance Γ (neglor1 φ0 ψ)); simpl in H2.
    apply (MP Γ ¬(φ0 ∨ ψ) ¬φ0 ∧ ¬ψ) in H2; try assumption.
    pose proof (AxiomInstance Γ (Ax5 ¬φ0 ¬ψ)); simpl in H3.
    apply (MP Γ ¬φ0 ∧ ¬ψ ¬ψ) in H3; try assumption.
    exfalso. apply H. apply (lfi1_cut Γ (Γ ∪ [¬ψ]) φ). split; try assumption.
    intros. destruct H4.
    + apply Premisse. apply H4.
    + destruct H4. apply H3.
  - intros. destruct H1. destruct strong_lem in H1;
    destruct strong_lem in H2; try discriminate H1; try discriminate H2.
    destruct strong_lem; try reflexivity. apply Premisse in i.
    apply Premisse in i0. apply H0 in n. exfalso; apply H.
    pose proof (AxiomInstance Γ (Ax3 ¬φ0 ¬ψ)); simpl in H3.
    apply (MP Γ ¬φ0 ¬ψ → ¬φ0 ∧ ¬ψ) in H3; try assumption.
    apply (MP Γ ¬ψ ¬φ0 ∧ ¬ψ) in H3; try assumption.
    pose proof (AxiomInstance Γ (neglor2 φ0 ψ)); simpl in H4.
    apply (MP Γ ¬φ0 ∧ ¬ψ ¬(φ0 ∨ ψ)) in H4; try assumption.
    apply (lfi1_cut Γ (Γ ∪ [¬(φ0 ∨ ψ)]) φ). split; try assumption.
    intros. destruct H5.
    + apply Premisse. apply H5.
    + destruct H5. apply H4.
  - destruct strong_lem in H1; try discriminate H1.
    destruct strong_lem; try reflexivity.
    apply Premisse in i; apply H0 in n. exfalso; apply H.
    pose proof (AxiomInstance Γ (negto1 φ0 ψ)); simpl in H2.
    apply (MP Γ ¬(φ0 → ψ) φ0 ∧ ¬ψ) in H2; try assumption.
    pose proof (AxiomInstance Γ (Ax4 φ0 ¬ψ)); simpl in H3.
    apply (MP Γ φ0 ∧ ¬ψ φ0) in H3; try assumption.
    apply (lfi1_cut Γ (Γ ∪ [φ0]) φ). split; try assumption.
    intros. destruct H4.
    + apply Premisse. apply H4.
    + destruct H4. apply H3.
  - destruct strong_lem in H1; try discriminate H1.
    destruct strong_lem; try reflexivity.
    apply Premisse in i; apply H0 in n. exfalso; apply H.
    pose proof (AxiomInstance Γ (negto1 φ0 ψ)); simpl in H2.
    apply (MP Γ ¬(φ0 → ψ) φ0 ∧ ¬ψ) in H2; try assumption.
    pose proof (AxiomInstance Γ (Ax5 φ0 ¬ψ)); simpl in H3.
    apply (MP Γ φ0 ∧ ¬ψ ¬ψ) in H3; try assumption.
    apply (lfi1_cut Γ (Γ ∪ [¬ψ]) φ). split; try assumption.
    intros. destruct H4.
    + apply Premisse. apply H4.
    + destruct H4. apply H3.
  - intros. destruct H1. destruct strong_lem in H1; try discriminate H1.
    destruct strong_lem in H2; try discriminate H2.
    destruct strong_lem; try reflexivity.
    exfalso; apply H. apply H0 in n. apply Premisse in i. apply Premisse in i0.
    pose proof (AxiomInstance Γ (Ax3 φ0 ¬ψ)); simpl in H3.
    apply (MP Γ φ0 ¬ψ → φ0 ∧ ¬ψ) in H3; try assumption.
    apply (MP Γ ¬ψ φ0 ∧ ¬ψ) in H3; try assumption.
    pose proof (AxiomInstance Γ (negto2 φ0 ψ)); simpl in H4.
    apply (MP Γ φ0 ∧ ¬ψ ¬(φ0 → ψ)) in H4; try assumption.
    apply (lfi1_cut Γ (Γ ∪ [¬(φ0 → ψ)]) φ). split; try assumption.
    intros. destruct H5.
    + apply Premisse. apply H5.
    + destruct H5. apply H4.
Qed.

(** Lindenbaum's lemma
    Extend a given nontrivial set Γ w.r.t φ and build a maximal nontrivial set (Δ) w.r.t. φ
    
    Γ₀ = Γ

    Γᵢ = • Γᵢ₋₁           if (Γᵢ₋₁ ∪ [φᵢ₋₁]) ⊢ φ
         • Γᵢ₋₁ ∪ [φᵢ₋₁]  otherwise
    Δ = ⋃{ᵢ₌₀}{∞} Γᵢ
*)
Section Lindenbaum.

Variable (Γ : Ensemble Formula)
         (φ : Formula).

Hypothesis Gamma_nontrivial : ~Γ ⊢ φ.

Fixpoint Gamma_i_fun 
 (i : nat) (f: nat -> Formula) : Ensemble Formula :=
  match i with
  | O   => Γ
  | S n => match (strong_lem (((Gamma_i_fun n f) ∪ [f n]) ⊢ φ)) with
           | left _  => (Gamma_i_fun n f)
           | right _ => (Gamma_i_fun n f) ∪ [f n]
           end
  end.

Definition Gamma_i_set
 (i : nat) (f : nat -> Formula) : Ensemble Formula :=
fun (ψ : Formula) => exists m : nat, m <= i /\ ψ ∈ (Gamma_i_fun i f).

Definition Delta
 (f: nat -> Formula) : Ensemble Formula :=
fun (ψ : Formula) => exists n : nat, ψ ∈ (Gamma_i_fun n f).

(** Showing that these forms of defining Gamma_i are equivalent *)
Proposition Gamma_i_fun_Gamma_i_eq : 
forall (i : nat) (f : nat -> Formula),
  (Gamma_i_set i f) = (Gamma_i_fun i f).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. split.
    + unfold Included. intros. destruct H. destruct H. apply H0.
    + unfold Included. intros. unfold Gamma_i_set. unfold In. exists i.
      split.
      * reflexivity.
      * apply H.
Qed.

(** Γᵢ ⊆ ∆ *)
Fact Gamma_i_fun_included_Delta : 
forall (i : nat) (f : nat -> Formula),
  (Gamma_i_set i f) ⊆ (Delta f).
Proof.
  intros. unfold Included. intros.
  induction i.
  - unfold Delta. exists 0. rewrite <- Gamma_i_fun_Gamma_i_eq. apply H.
  - unfold Delta. exists (S i). unfold Gamma_i_set in H.
    destruct H. destruct H. apply H0.
Qed.

(** Γₘ ⊆ Γₙ , where m ≤ n *)
Fact Gamma_i_m_included_Gamma_i_n : 
forall (f : nat -> Formula) (m : nat) (n : nat), 
m <= n -> (Gamma_i_fun m f) ⊆ (Gamma_i_fun n f).
Proof.
  intros. generalize dependent m. induction n.
  - intros. unfold Included. intros. inversion H. rewrite H1 in H0; apply H0.
  - intros. inversion H. 
    + unfold Included. intros. apply H1.
    + unfold Included. intros. apply IHn in H1.
      simpl. destruct strong_lem.
      * apply H1. apply H2.
      * left. unfold Included in H1. apply H1. apply H2.
Qed.

(** ~(Γᵢ ⊢ φ) for all i *)
Fact Gamma_i_non_trivial :
forall (i : nat) (f : nat -> Formula),
  ~((Gamma_i_fun i f) ⊢ φ).
Proof.
  intros. intro. induction i.
  - simpl in H. contradiction.
  - simpl in H. destruct strong_lem in H.
    + contradiction.
    + contradiction.
Qed.

(** Δ ⊢ φ0 -> ∃n : nat, Γₙ ⊢ φ0 *)
Fact Delta_f_i_Gamma_i_con :
  forall (f : nat -> Formula) (φ0 : Formula), 
(Delta f) ⊢ φ0 -> (exists n : nat, (Gamma_i_set n f) ⊢ φ0).
Proof.
  intros. dependent induction H.
  - destruct H. exists x.
    apply Premisse. rewrite Gamma_i_fun_Gamma_i_eq. apply H.
  - exists 0. apply AxiomInstance.
  - 
    specialize (IHdeduction1 Gamma_nontrivial f). specialize (IHdeduction2 Gamma_nontrivial f).
    destruct IHdeduction1, IHdeduction2; try reflexivity.
    destruct (Nat.le_ge_cases x x0).
    + exists x0. pose proof (Gamma_i_m_included_Gamma_i_n f x x0).
      apply H4 in H3. pose proof (lfi1_monotonicity (Gamma_i_set x0 f) (Gamma_i_set x f) ).
      specialize (H5 φ0 → ψ). 
      assert (Gamma_i_set x f ⊢ φ0 → ψ /\ Gamma_i_set x f ⊆ Gamma_i_set x0 f).
      split. assumption. rewrite Gamma_i_fun_Gamma_i_eq. rewrite Gamma_i_fun_Gamma_i_eq.
      assumption.
      apply H5 in H6. apply (MP (Gamma_i_set x0 f) φ0).
      * apply H6.
      * apply H2.
    + exists x. pose proof (Gamma_i_m_included_Gamma_i_n f x0 x).
      apply H4 in H3. pose proof (lfi1_monotonicity (Gamma_i_set x f) (Gamma_i_set x0 f)).
      specialize (H5 φ0). 
      assert (Gamma_i_set x0 f ⊢ φ0 /\ Gamma_i_set x0 f ⊆ Gamma_i_set x f).
      split. assumption. rewrite Gamma_i_fun_Gamma_i_eq. rewrite Gamma_i_fun_Gamma_i_eq.
      assumption.
      apply H5 in H6. apply (MP (Gamma_i_set x f) φ0).
      * apply H1.
      * apply H6.
Qed.

(** ~(Δ ⊢ φ) *)
Fact Delta_nvdash_phi : 
  forall (f : nat -> Formula), 
  ~ (Delta f) ⊢ φ.
Proof.
  intros. intro. pose proof (Gamma_i_non_trivial).
  apply Delta_f_i_Gamma_i_con in H. destruct H.
  specialize (H0 x f). rewrite Gamma_i_fun_Gamma_i_eq in H.
  contradiction.
Qed.

(** ψ ∉ Δ -> ∀n : nat, ψ ∉ Γₙ *)
Fact not_in_Delta_Gamma_i : forall (ψ : Formula) (f : nat -> Formula),
  ψ ∉ (Delta f) -> forall n : nat, ψ ∉ (Gamma_i_fun n f).
Proof.
  intros. intro. destruct H.
  unfold Delta. exists n. apply H0.
Qed.

(** φᵢ ∉ Γ₍ᵢ₊₁₎ -> Γᵢ ∪ {φᵢ} ⊢ φ *)
Fact not_in_Gamma_i_trivial : forall (f : nat -> Formula) (i : nat),
  (f i) ∉ (Gamma_i_fun (S i) f) -> (Gamma_i_fun i f) ∪ [f i] ⊢ φ.
Proof.
  intros.
  simpl. simpl in H. destruct (strong_lem (Gamma_i_fun i f ∪ [f (i)] ⊢ φ)).
  - apply d.
  - destruct H. right. apply In_singleton.
Qed.

(** Delta is maximal nontrivial given a bijection between nat and Formula*)
Fact Delta_maximal_nontrivial : forall (f : surjection nat Formula),
  maximal_nontrivial (Delta f) φ.
Proof.
  intros. destruct f as [f su_bij]. simpl. 
  unfold function_surjective in su_bij. unfold maximal_nontrivial. split.
  - apply Delta_nvdash_phi.
  - intros. pose proof (su_bij ψ). destruct H0.
    rewrite <- H0 in H. assert (forall n : nat, (f x) ∉ (Gamma_i_fun n f));
    try (apply not_in_Delta_Gamma_i; apply H).
    specialize (H1 (S x)). apply not_in_Gamma_i_trivial in H1.
    rewrite <- H0. pose proof (lfi1_monotonicity (Delta f ∪ [f x]) (Gamma_i_fun x f ∪ [f x]) φ).
    apply H2. split.
    + apply H1.
    + unfold Included. intros. destruct H3.
      * left. pose proof (Gamma_i_fun_included_Delta x f).
        unfold Included in H4. apply H4. rewrite Gamma_i_fun_Gamma_i_eq.
        apply H3.
      * right. apply H3.
Qed.

End Lindenbaum.

(** For now, assume a surjection between nat and Formula *)
Axiom formula_countable : surjection nat Formula.

Theorem completeness_bivaluations : forall (Γ : Ensemble Formula) (α : Formula), 
(Γ ⊨ α) -> (Γ ⊢ α).
Proof.
  intros. destruct (strong_lem (Γ ⊢ α)); try assumption.
  exfalso.
  pose proof formula_countable as FC.
  pose proof (Delta_maximal_nontrivial Γ α n FC).
  pose proof (Delta_maximal_nontrivial Γ α n FC).
  destruct FC as [f]. simpl in H0, H1.
  destruct H0.
  assert (α ∉ (Delta Γ α f)). 
  { intro. apply Premisse in H3. contradiction. }
  pose proof (completeness_valuation_is_bivaluation (Delta Γ α f) α).
  apply H4 in H1 as H5. assert (completeness_valuation (Delta Γ α f) α = ⊥).
  { unfold completeness_valuation. destruct (strong_lem (α ∈ (Delta Γ α f))); auto; contradiction. }
  unfold bivaluationEntails in H. specialize (H (completeness_valuation (Delta Γ α f))).
  rewrite H6 in H. discriminate H.
  + apply H5.
  + intros. unfold completeness_valuation. destruct (strong_lem (ψ ∈ (Delta Γ α f))).
    * reflexivity.
    * pose proof (not_in_Delta_Gamma_i Γ α ψ f).
      assert (forall n : nat, ψ ∉ (Gamma_i_fun Γ α n f)); try (apply H8; assumption).
      specialize (H9 0). simpl in H9. contradiction.
Qed.
  
Corollary completeness_matrix : forall (Γ : Ensemble Formula) (α : Formula), 
(Γ ⊨m α) -> (Γ ⊢ α).
Proof.
  intros. apply completeness_bivaluations. apply matrix_bivaluation_imp. apply H.
Qed.

Corollary matrix_bivaluations_eq : forall (Γ : Ensemble Formula) (α : Formula),
(Γ ⊨m α) <-> (Γ ⊨ α).
Proof.
  intros. split.
  - apply matrix_bivaluation_imp.
  - intro. apply soundness_matrix. apply completeness_bivaluations. apply H.
Qed.