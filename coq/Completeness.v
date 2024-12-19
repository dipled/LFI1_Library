From LFI1 Require Import Utils Language Syntax Semantics.
From LFI1 Require Import Deduction_metatheorem Soundness.
Require Import Arith Constructive_sets.

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
  intros. destruct H. unfold Included in H0.
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

(* From now on, we need to include the Infinite_sets and
   Epsilon modules, which add the concepts needed to construct 
   the proof of completeness. These modules, however, include 
   the excluded middle and epsilon axioms, which result in 
   proof irrelevance.
*)

Require Import Infinite_sets Epsilon.
From LFI1 Require Import Countability.
Arguments Finite {U}.

(* We then state a trivial fact about sets *)
Proposition In_lem {U : Type} : forall (A : Ensemble U) (x : U),
  x ∈ A \/ x ∉ A.
Proof. intros. apply classic. Qed.

(* LFI1 is finitary *)
Proposition lfi1_finitary :
  forall (Γ : Ensemble Formula) (α : Formula),
    (Γ ⊢ α) -> (exists (Γ0 : Ensemble Formula), (Finite Γ0) /\ Γ0 ⊆ Γ /\ Γ0 ⊢ α).
Proof.
  intros. induction H.
  - exists (Add ∅ φ). split; try split.
    + unfold Add. apply Union_is_finite.
      * apply Empty_is_finite.
      * apply Noone_in_empty.
    + unfold Add. unfold Included. intro.
      intros. destruct H0.
      * destruct H0.
      * destruct H0. apply H.
    + unfold Add. apply Premisse.
      apply Union_intror. apply In_singleton.
  - exists ∅. split; try split.
    + apply Empty_is_finite.
    + unfold Included. intros. destruct H.
    + apply AxiomInstance.
  - destruct IHdeduction1, IHdeduction2.
    destruct H1. destruct H3. destruct H2. destruct H5.
    exists (Union x x0). split; try split.
    + apply Union_preserves_Finite.
      * apply H1.
      * apply H2.
    + apply Union_minimal.
      * apply H3.
      * apply H5.
    + pose proof (lfi1_monotonicity (x ∪ x0) x (φ → ψ)).
      pose proof (lfi1_monotonicity (x ∪ x0) x0 (φ)).
      assert (x ⊢ φ → ψ /\ x ⊆ (x ∪ x0)).
      * split. apply H4. apply Union_increases_l.
      * assert (x0 ⊢ φ /\ x0 ⊆ (x ∪ x0)).
        -- split. apply H6. apply Union_increases_r.
        -- apply H7 in H9. apply H8 in H10.
           apply (MP ((x ∪ x0)) φ ψ).
           apply H9. apply H10.
Qed.

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
    Extend a given nontrivial set Γ and build a maximal nontrivial set (Δ)
    
    Γ₀ = Γ

    Γᵢ = • Γᵢ₋₁         if (Γᵢ₋₁ ∪ [φᵢ₋₁]) ⊢ φ
         • Γᵢ₋₁ ∪ [φᵢ₋₁]  otherwise
    Δ = ⋃{ᵢ₌₀}{∞} Γᵢ
*)
Section Lindenbaum.

Context (Γ : Ensemble Formula)
        (φ : Formula).

Hypothesis Gamma_nontrivial_wrt_phi : (~ Γ ⊢ φ).

Fixpoint Gamma_i 
  (Γ : Ensemble Formula) (i : nat) (f: nat -> Formula) (φ : Formula) : Ensemble Formula :=
  match i with
  | O   => Γ
  | S n => match (strong_lem (((Gamma_i Γ n f φ) ∪ [f n]) ⊢ φ)) with
           | left _  => (Gamma_i Γ n f φ)
           | right _ => (Gamma_i Γ n f φ) ∪ [f n]
           end
  end.

Definition Gamma_i_fun
  (Γ : Ensemble Formula) (i : nat) (f : nat -> Formula) (φ : Formula) : Ensemble Formula :=
fun (ψ : Formula) => exists m : nat, m <= i /\ ψ ∈ (Gamma_i Γ i f φ).

Definition Delta
  (Γ : Ensemble Formula) (f: nat -> Formula) (φ : Formula) : Ensemble Formula :=
fun (ψ : Formula) => exists n : nat, ψ ∈ (Gamma_i Γ n f φ).

Proposition Gamma_i_fun_Gamma_i_eq : 
forall (i : nat) (f : nat -> Formula),
  (Gamma_i_fun Γ i f φ) = (Gamma_i Γ i f φ).
Proof.
  intros. induction i.
  - apply Extensionality_Ensembles. unfold Same_set. split.
    + unfold Included. intros. destruct H. destruct H.
      simpl in H0. unfold Gamma_i. apply H0.
    + unfold Included. intros. unfold Gamma_i in H.
      unfold Gamma_i_fun. exists 0. simpl. 
      split; try reflexivity; try apply H.
  - apply Extensionality_Ensembles. unfold Same_set. split.
    + unfold Included. intros. destruct H. destruct H.
      apply H0.
    + unfold Included. intros. unfold Gamma_i_fun.
      exists (S i). split; try reflexivity; try apply H.
Qed.

(** Γ ⊆ Γₙ, for all n*)
Fact Gamma_in_Gamma_i : forall (f : nat -> Formula) (i : nat), 
  Γ ⊆ (Gamma_i Γ i f φ).
Proof.
  intros. unfold Included. intros. induction i.
  - simpl. apply H.
  - simpl. destruct strong_lem.
    + apply IHi.
    + left. apply IHi.
Qed.

(** Γₘ ⊆ Γₙ , where m ≤ n*)
Fact Gamma_i_m_included_Gamma_i_n : 
forall (f : nat -> Formula) (m : nat) (n : nat), 
m <= n -> (Gamma_i Γ m f φ) ⊆ (Gamma_i Γ n f φ).
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

(** Γ ⊆ ∆ *)
Fact Gamma_i_fun_included_Delta : 
forall (i : nat) (f : nat -> Formula),
  (Gamma_i_fun Γ i f φ) ⊆ (Delta Γ f φ).
Proof.
  intros. unfold Included. intros.
  induction i.
  - unfold Delta. exists 0. rewrite <- Gamma_i_fun_Gamma_i_eq. apply H.
  - unfold Delta. exists (S i). unfold Gamma_i_fun in H.
    destruct H. destruct H. apply H0.
Qed.

(** ~(Γ ⊢ φ) -> ~(Γᵢ ⊢ φ) for all i *)
Fact Gamma_i_non_trivial :
forall (i : nat) (f : nat -> Formula),
  ~((Gamma_i Γ i f φ) ⊢ φ).
Proof.
  intros. intro. induction i.
  - simpl in H. contradiction.
  - simpl in H. destruct strong_lem in H.
    + contradiction.
    + contradiction.
Qed.

Fact Delta_f_i_Gamma_i : 
  forall (i : nat) (f : nat -> Formula),
(f i) ∈ (Delta Γ f φ) -> (f i) ∈ (Gamma_i Γ i f φ).
Proof.
  intros. destruct (strong_lem ((f i) ∈ (Gamma_i Γ i f φ))).
  - apply i0.
  - unfold Delta in H. destruct H. unfold Gamma_i in H.




End Lindenbaum.


(** We then need to prove that Formula is denumerable, i.e.,
    there is a bijection between Formula and nat.
    For this, we prove that:
      - There is an injection from nat to Formula
      - There is an injection from Formula to nat
*)