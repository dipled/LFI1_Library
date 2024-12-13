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

Lemma bivaluation_matrix_lemma : forall (v : Formula -> BivaluationDomain),
bivaluation v -> 
(exists (h : Formula -> MatrixDomain), valuation h ->
 forall φ : Formula, v φ = ⊤ <-> designatedValue (h φ)
).
Proof. Admitted.

Theorem soundness_mat : forall (Γ : Ensemble Formula) (α : Formula), 
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