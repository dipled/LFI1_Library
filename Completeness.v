From LFI1 Require Export Soundness.
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

From Coq Require Export Infinite_sets Epsilon.
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
  ~ Γ ⊢ φ /\ (forall (ψ : Formula), ~ψ ∈ Γ -> (Add Γ ψ ⊢ φ)).

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

(** Strong LEM *)
Theorem strong_lem : forall P : Prop, {P} + {~P}.
Proof.
  intros. assert {x : bool | if x then P else ~P}.
  - apply constructive_indefinite_description.
    pose proof (classic P). destruct H.
    + exists true. apply H.
    + exists false. apply H.
  - destruct H. destruct x.
    + left. apply y.
    + right. apply y.
Qed. 

(** Extend a given nontrivial set Γ and build a maximal nontrivial set (Δ)
    
    Γ₀ = Γ

    Γᵢ = • Γᵢ₋₁         if (Γᵢ₋₁ ∪ [φᵢ]) ⊢ φ
         • Γᵢ₋₁ ∪ [φᵢ]  otherwise
    Δ = ⋃{ᵢ₌₀}{∞} Γᵢ
*)

Fixpoint extend_nontrivial_set 
  (Γ : Ensemble Formula) (n : nat) (f: nat -> Formula) (φ : Formula) : Ensemble Formula :=
match n with
  | O   => Γ
  | S m => match (strong_lem (((extend_nontrivial_set Γ m f φ) ∪ [f m]) ⊢ φ)) with
            | left _  => (extend_nontrivial_set Γ m f φ)
            | right _ => (extend_nontrivial_set Γ m f φ) ∪ [f m]
          end
end.

Definition maximal_nontrivial_set 
  (Γ : Ensemble Formula) (f: nat -> Formula) (φ : Formula): Ensemble Formula :=
fun x => exists n : nat, x ∈ (extend_nontrivial_set Γ n f φ).

(** We then need to prove that Formula is denumerable, i.e.,
    there is a bijection between Formula and nat.
    For this, we prove that:
      - There is an injection from nat to Formula
      - There is an injection from Formula to nat
*)
