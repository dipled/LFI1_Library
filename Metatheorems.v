From LFI1 Require Export Syntax Semantics.

(* Deduction metatheorem for Hilbert calculus *)

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

Lemma quasi_monotonicity : forall (Γ : Ensemble Formula) (α β : Formula), (Γ ⊢ β) -> 
(Add Γ α) ⊢ β.
Proof.
  intros. induction H.
  - apply Premisse. left. apply H.
  - apply AxiomInstance.
  - apply (MP _ φ ψ).
    + apply IHdeduction1.
    + apply IHdeduction2.
Qed.

Theorem deduction_metatheorem : forall (Γ : Ensemble Formula) (α β : Formula), 
((Add Γ α) ⊢ β) <-> (Γ ⊢ α → β).
Proof. 
  intros. split.
  - intro. remember (Add Γ α) as Δ eqn: Heq in H. induction H.
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
    pose proof quasi_monotonicity Γ α (α → β). apply H0 in H as H1.
    assert ((Add Γ α) ⊢ α) as H2.
    + apply Premisse. simpl. right. reflexivity.
    + apply (MP (Add Γ α) α β).
      * apply H1.
      * apply H2.
Qed.

Corollary proof_by_cases : forall (Γ : Ensemble Formula) (α β φ : Formula), 
(Add Γ α ⊢ φ) /\ (Add Γ β ⊢ φ) -> (Add Γ (α ∨ β) ⊢ φ).
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
(Add Γ α ⊢ φ) /\ (Add Γ (¬α) ⊢ φ) -> (Γ ⊢ φ).
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

Definition h_formula (α : Formula) (v : Formula -> BivaluationDomain) : MatrixDomain :=
  match (v α), (v ¬α) with
  | ⊤, ⊥ => One
  | ⊤, ⊤ => Half
  | ⊥, _ => Zero       
  end.

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

Lemma bivaluation_matrix_lemma : forall (v : Formula -> BivaluationDomain),
bivaluation v -> 
(exists (h : Formula -> MatrixDomain),
 (forall φ : Formula, v φ = ⊤ <-> designatedValue (h φ)) /\ valuation h
).
Proof. 
  intros. exists (fun x => h_formula x v). intros. split. split.
  - intros. pose proof (bivaluation_lem v ¬φ). unfold h_formula.
    destruct H1.
    + rewrite H0. rewrite H1. reflexivity.
    + rewrite H0. rewrite H1. reflexivity.
  - intros. pose proof (bivaluation_lem v ¬φ). pose proof (bivaluation_lem v φ).
    unfold h_formula in H0. 
    destruct H1, H2.
    + apply H2.
    + rewrite H1 in H0. rewrite H2 in H0. destruct H0.
    + apply H2.
    + rewrite H1 in H0. rewrite H2 in H0. destruct H0.
  - apply h_valuation. apply H.
Qed.

Corollary bivaluation_matrix_imp1 : forall (Γ : Ensemble Formula) (α : Formula), 
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
  - destruct a; unfold matrixEntails; intros; simpl;
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

Theorem soundness_bivaluations : forall (Γ : Ensemble Formula) (α : Formula), 
(Γ ⊢ α) -> (Γ ⊨ α).
Proof.
  intros. apply bivaluation_matrix_imp1. apply soundness_matrix. apply H.
Qed.

(* Soundness *)

(* LFI1 is tarskian:  *)

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