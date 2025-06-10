From LFI1 Require Import Utils Language Deduction Semantics.
From LFI1 Require Import Deduction_metatheorem.
From Stdlib Require Import Arith Constructive_sets.

(* Function used to prove Γ ⊨m α -> Γ ⊨ α *)
Definition h_formula (α : Formula) (v : Formula -> BivaluationDomain) : MatrixDomain :=
  match (v α), (v ¬α) with
  | ⊤, ⊥ => One
  | ⊤, ⊤ => Half
  | ⊥, _ => Zero       
  end.

(* Proof that if v is a bivaluation, then h_formula is a valuation over the matrices 
   i.e., h_formula is a homomorphism.
*)
Lemma h_valuation : forall (v : Formula -> BivaluationDomain),
bivaluation v -> valuation (fun x => h_formula x v).
Proof.
  intros. pose proof H as H1. apply bivaluation_additional in H. 
  unfold bivaluation in H1. destruct_conjunction H. destruct_conjunction H1. 
  unfold valuation; try repeat split.
  - unfold preserveOr. intros. unfold h_formula.
    remember (v (φ ∨ ψ)). remember (v ¬(φ ∨ ψ)).
    destruct b,  b0; symmetry in Heqb; symmetry in Heqb0.
    + apply L0 in Heqb. apply L7 in Heqb0. destruct Heqb.
      apply L2 in H. apply L2 in H0. rewrite H in Heqb0.
      rewrite H0 in Heqb0.
      destruct Heqb0.
      * discriminate H1.
      * discriminate H1.
    + apply L0 in Heqb. apply L16 in Heqb0. destruct Heqb, Heqb0.
      rewrite H. rewrite H0. reflexivity.
    + apply L9 in Heqb. apply L7 in Heqb0. destruct Heqb; destruct Heqb0.
      * rewrite H. rewrite H0. simpl. reflexivity.
      * rewrite H. rewrite H0. apply L11 in H0. rewrite H0. 
        destruct (v ¬φ); reflexivity.
      * rewrite H. rewrite H0. apply L11 in H0. rewrite H0. reflexivity.
      * rewrite H. rewrite H0. destruct (v φ), (v ¬φ); reflexivity.
    + apply L9 in Heqb. apply L16 in Heqb0. destruct Heqb0. destruct Heqb.
      * rewrite H1; rewrite H; rewrite H0. destruct (v ψ); reflexivity.
      * rewrite H1; rewrite H0; rewrite H; destruct (v φ); reflexivity.
  - unfold preserveTo. intros. unfold h_formula. remember (v (φ → ψ)). 
    remember (v(¬(φ → ψ))). symmetry in Heqb, Heqb0. destruct b, b0.
      * apply L11 in Heqb0. rewrite Heqb in Heqb0; discriminate Heqb0.
      * apply bivaluation_dec2 in Heqb. 
        specialize (L10 φ ψ). apply iff_neg in L10.
        apply L10 in Heqb. apply R0 in Heqb0. destruct Heqb0. 
        rewrite H, H0. destruct (v φ), (v ψ). 
        -- discriminate H.
        -- discriminate H.
        -- destruct  (v ¬φ); reflexivity.
        -- exfalso. apply Heqb. right. reflexivity.
      * apply bivaluation_dec2 in Heqb0.
        apply L10 in Heqb. specialize (R0 φ ψ).
        apply iff_neg in R0. apply R0 in Heqb0.
        destruct Heqb.
        -- rewrite H. destruct (v ψ), (v ¬ψ); reflexivity.
        -- rewrite H. destruct (v ¬φ), (v φ), (v ¬ψ); try reflexivity;
           try discriminate H; exfalso; apply Heqb0; split; 
           reflexivity.
      * apply L10 in Heqb. apply R0 in Heqb0. destruct Heqb0.
        destruct Heqb.
        -- rewrite H1 in H; discriminate H.
        -- rewrite H1, H, H0. destruct (v ¬φ); reflexivity.
    - unfold preserveAnd. intros. unfold h_formula. 
      remember (v(φ ∧ ψ)). remember (v ¬(φ ∧ ψ)).
      symmetry in Heqb, Heqb0. destruct b, b0.
      * apply L11 in Heqb0. rewrite Heqb in Heqb0; discriminate Heqb0.
      * apply bivaluation_dec2 in Heqb. specialize (L8 φ ψ).
        apply iff_neg in L8. apply L8 in Heqb. apply L15 in Heqb0.
        destruct Heqb0.
        -- rewrite H. destruct (v φ), (v ψ), (v ¬ψ); try reflexivity;
           exfalso; apply Heqb; split; reflexivity.
        -- rewrite H. destruct (v φ), (v ¬φ), (v ψ); try discriminate H;
           try reflexivity; exfalso; apply Heqb; split; reflexivity.
      * apply bivaluation_dec2 in Heqb0. apply L8 in Heqb.
        destruct Heqb. rewrite H, H0. specialize (L15 φ ψ).
        apply iff_neg in L15. apply L15 in Heqb0.
        destruct (v ¬φ), (v ¬ψ); try reflexivity; 
        try (exfalso; apply Heqb0; try (left; reflexivity);
        try (right; reflexivity)).
      * apply L8 in Heqb. apply L15 in Heqb0. destruct Heqb, Heqb0;
        rewrite H, H0, H1; try (destruct (v ¬ψ); reflexivity);
        try (destruct (v ¬φ); reflexivity).
    - unfold preserveNeg. intros. unfold h_formula.
      remember (v ¬φ). remember (v φ). symmetry in Heqb, Heqb0.
      destruct b, b0.
      * apply L2 in Heqb0. rewrite Heqb in Heqb0; discriminate Heqb0.
      * reflexivity.
      * apply L5 in Heqb0. rewrite Heqb0. reflexivity.
      * apply L14 in Heqb0. rewrite Heqb0. reflexivity.
    - unfold preserveCirc. intros. unfold h_formula.
      remember (v ∘φ). remember (v ¬∘φ). symmetry in Heqb, Heqb0.
      destruct b, b0.
      * apply L2 in Heqb. rewrite Heqb in Heqb0; discriminate Heqb0.
      * apply L13 in Heqb0. destruct Heqb0.
        rewrite H, H0. reflexivity.
      * apply L12 in Heqb; destruct Heqb.
        -- rewrite H. reflexivity.
        -- rewrite H. apply L11 in H. rewrite H.
           reflexivity.
      * apply L13 in Heqb0; destruct Heqb0. apply L12 in Heqb; 
        destruct Heqb.
        -- rewrite H1 in H; discriminate H.
        -- rewrite H1 in H0; discriminate H0.
Qed.

(* Final lemma before proving Γ ⊨m α -> Γ ⊨ α, that generalizes the previous
   results regarding h_formula.
*)
Lemma bivaluation_matrix_lemma : forall (v : Formula -> BivaluationDomain),
bivaluation v -> 
(exists (h : Formula -> MatrixDomain),
 (forall φ : Formula, v φ = ⊤ <-> designatedValue (h φ)) /\ valuation h
).
Proof. 
  intros. exists (fun x => h_formula x v). intros. split. split.
  - intros. unfold h_formula.  destruct (v ¬ φ).
    + rewrite H0. reflexivity.
    + rewrite H0. reflexivity.
  - intros.
    unfold h_formula in H0. destruct (v ¬ φ), (v φ). 
    + simpl in H0. destruct H0.
    + reflexivity.
    + destruct H0.
    + reflexivity.
  - apply h_valuation. apply H.
Qed.

Corollary matrix_bivaluation_imp : forall (Γ : Ensemble Formula) (α : Formula), 
(Γ ⊨m α) -> (Γ ⊨ α).
Proof.
  intros. unfold matrixEntails in H. unfold bivaluationEntails.
  intros. apply bivaluation_matrix_lemma in H0. destruct H0 as [h].
  specialize (H h). destruct H0. apply H0. apply H.
  - apply H2.
  - intros. apply H0. apply H1. apply H3.
Qed.

Theorem soundness_matrix : forall (Γ : Ensemble Formula) (α : Formula), 
(Γ ⊢ α) -> (Γ ⊨m α).
Proof.
  intros. induction H.
  - unfold matrixEntails. intros. apply H1 in H. apply H.
  - 
  (* Here we perform a case analysis on each axiom and show that they're indeed valid 
     in the matrix semantic system. The repeat rewrite lines are applications of the homo-
     morphism equalities in order to evalue the formula. This should be made automatic with
     ltac in the future
  *)  
  destruct a; unfold matrixEntails; intros; simpl;
    try unfold valuation in H; try destruct_conjunction H;
    repeat rewrite L;
    repeat rewrite L0; 
    repeat rewrite L1;
    repeat rewrite L2;
    repeat rewrite R0;
    repeat rewrite L;
    repeat rewrite L0; 
    repeat rewrite L1;
    repeat rewrite L2;
    repeat rewrite R0;
    try destruct (v f);
    try destruct (v f0);
    try destruct (v f1);
    try reflexivity.
  - unfold matrixEntails in *. intros.
    specialize (IHdeduction1 v). specialize (IHdeduction2 v). 
    apply IHdeduction1 in H1 as H3.
    apply IHdeduction2 in H1 as H4.
    + unfold valuation in H1. destruct_conjunction H1. rewrite L0 in H3.
      destruct (v ψ), (v φ); try reflexivity; try destruct H3; try destruct H4;
      try apply H2. 
    + apply H2.
    + apply H2.
Qed.

Corollary soundness_bivaluations : forall (Γ : Ensemble Formula) (α : Formula), 
(Γ ⊢ α) -> (Γ ⊨ α).
Proof.
  intros. apply matrix_bivaluation_imp. apply soundness_matrix. apply H.
Qed.

(** LFI1 is an LFI w.r.t ¬ and ∘, i.e. 
  1) exists (α β : Formula), ~(α, ¬α ⊢ β)
  2) exists (α β : Formula), ~(α, ∘α ⊢ β) /\ ~(¬α, ∘α ⊢ β)
  3) forall (α β : Formula), ∘α, α, ¬α ⊢ β
*)


Fixpoint valuation_condition_1 (x : Formula) : MatrixDomain :=
 match x with 
 |#0 => Half
 | a ∧ b => (valuation_condition_1 a) ∧ₘ (valuation_condition_1 b)
 | a ∨ b => (valuation_condition_1 a) ∨ₘ (valuation_condition_1 b)
 | a → b => (valuation_condition_1 a) →ₘ (valuation_condition_1 b)
 | ¬a => ¬ₘ(valuation_condition_1 a)
 | ∘a => ∘ₘ(valuation_condition_1 a)
 |_ => Zero 
 end.

Fixpoint valuation_condition_2_l (x : Formula) : MatrixDomain :=
 match x with 
 |#0 => One
 | a ∧ b => (valuation_condition_2_l a) ∧ₘ (valuation_condition_2_l b)
 | a ∨ b => (valuation_condition_2_l a) ∨ₘ (valuation_condition_2_l b)
 | a → b => (valuation_condition_2_l a) →ₘ (valuation_condition_2_l b)
 | ¬a => ¬ₘ(valuation_condition_2_l a)
 | ∘a => ∘ₘ(valuation_condition_2_l a)
 |_ => Zero 
 end.

 Fixpoint valuation_condition_2_r (x : Formula) : MatrixDomain :=
 match x with 
 |#0 => Zero
 |¬#0 => One
 | a ∧ b => (valuation_condition_2_r a) ∧ₘ (valuation_condition_2_r b)
 | a ∨ b => (valuation_condition_2_r a) ∨ₘ (valuation_condition_2_r b)
 | a → b => (valuation_condition_2_r a) →ₘ (valuation_condition_2_r b)
 | ¬a => ¬ₘ(valuation_condition_2_r a)
 | ∘a => ∘ₘ(valuation_condition_2_r a)
 |_ => Zero 
 end.

Proposition lfi1_is_lfi :
(exists (α β : Formula), ~([α] ∪ [¬α] ⊢ β)) /\
(exists (α β : Formula), ~([∘α] ∪ [α] ⊢ β) /\ ~([∘α] ∪ [¬α] ⊢ β)) /\
(forall (α β : Formula), ([∘α] ∪ [α] ∪ [¬α]) ⊢ β).
Proof.
  split; try split.
  { 
    exists #0, #1. intro. apply deduction_metatheorem in H.
    apply soundness_matrix in H.
    unfold matrixEntails in H. 
    specialize (H valuation_condition_1). simpl in H. apply H.
    - unfold valuation. try repeat split.
    - intros. inversion H0. reflexivity. 
  }
  {
    exists #0, #1. split.
    - intro. apply deduction_metatheorem in H.
      apply soundness_matrix in H.
      unfold matrixEntails in H. 
      specialize (H valuation_condition_2_l). simpl in H. apply H.
      + unfold valuation. try repeat split.
      + intros. inversion H0. simpl. reflexivity.
    - intro. apply deduction_metatheorem in H.
      apply soundness_matrix in H.
      unfold matrixEntails in H. 
      specialize (H valuation_condition_2_r). simpl in H. apply H.
      + unfold valuation. try repeat split. unfold preserveNeg.
        intros. simpl. destruct φ; try destruct a; reflexivity.
      + intros. inversion H0. simpl. reflexivity.
  }
  {
    intros. pose proof (Premisse ([∘α] ∪ [α] ∪ [¬α]) (∘α)).
    pose proof (Premisse ([∘α] ∪ [α] ∪ [¬α]) (α)).
    pose proof (Premisse ([∘α] ∪ [α] ∪ [¬α]) (¬α)).
    pose proof (AxiomInstance ([∘α] ∪ [α] ∪ [¬α]) (bc1 α β)). simpl in H2.
    assert ((∘α ∈ ([∘α] ∪ [α] ∪ [¬α])) /\ (α ∈ ([∘α] ∪ [α] ∪ [¬α])) /\ ((¬α ∈ ([∘α] ∪ [α] ∪ [¬α]))));
    try repeat split.
    - apply Union_introl. apply Union_introl. apply In_singleton.
    - apply Union_introl. apply Union_intror. apply In_singleton.
    - apply Union_intror. apply In_singleton.
    - destruct_conjunction H3. apply H in L. apply H0 in L0. apply H1 in R0.
      pose proof (MP ([∘α] ∪ [α] ∪ [¬α]) (∘α) (α → ¬α → β)).
      apply H3 in H2.
      + pose proof (MP ([∘α] ∪ [α] ∪ [¬α]) (α) (¬α → β)).
        apply H4 in H2.
        * pose proof (MP ([∘α] ∪ [α] ∪ [¬α]) (¬α) (β)).
          apply H5 in R0.
          -- apply R0.
          -- apply H2.
        * apply L0.
      + apply L.
  }
Qed.