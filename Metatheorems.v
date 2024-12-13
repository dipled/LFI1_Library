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

Lemma bivaluation_lem : forall (v : Formula -> BivaluationDomain) (φ : Formula),
v φ = ⊤ \/ v φ = ⊥.
Proof.
  intros. destruct (v φ).
  - right. reflexivity.
  - left. reflexivity.
Qed.

Lemma bivaluation_dec1 : forall (v : Formula -> BivaluationDomain) (φ : Formula),
v φ = ⊤ <-> ~ v φ = ⊥.
Proof.
  intros. split.
  + intro. destruct (v φ).
    - discriminate H.
    - intro. discriminate H0.
  + intro. destruct (v φ).
    - exfalso. apply H. reflexivity.
    - reflexivity.
Qed.

Lemma bivaluation_dec2 : forall (v : Formula -> BivaluationDomain) (φ : Formula),
v φ = ⊥ <-> ~ v φ = ⊤.
Proof.
    intros. split.
  + intro. destruct (v φ).
    - intro. discriminate H0.
    - discriminate H.
  + intro. destruct (v φ).
    - reflexivity.
    - exfalso. apply H. reflexivity.
Qed.

(* Fixpoint h_atom (α : Formula) (v : Formula -> BivaluationDomain) : MatrixDomain :=
  match α with
  | # a   => match (v α), (v ¬α) with
             | ⊤, ⊥ => One
             | ⊤, ⊤ => Half
             | ⊥, _ => Zero
             end
  | ¬ β   => ¬'(h_atom β v)
  | ∘ β   => ∘'(h_atom β v)
  | β ∧ γ => (h_atom β v) ∧' (h_atom γ v)
  | β ∨ γ => (h_atom β v) ∨' (h_atom γ v)
  | β → γ => (h_atom β v) →' (h_atom γ v)
  end. *)

Definition h_formula (α : Formula) (v : Formula -> BivaluationDomain) : MatrixDomain :=
  match (v α), (v ¬α) with
  | ⊤, ⊥ => One
  | ⊤, ⊤ => Half
  | ⊥, _ => Zero       
  end.

Lemma h_valuation : forall (v : Formula -> BivaluationDomain),
bivaluation v -> valuation (fun x => h_formula x v).
Proof.
  intros. unfold bivaluation in H. destruct_conjunction H. 
  unfold valuation; try repeat split.
  - unfold preserveOr. intros. unfold h_formula.
    remember (v (φ ∨ ψ)). remember (v ¬(φ ∨ ψ)).
    destruct b,  b0; symmetry in Heqb; symmetry in Heqb0.
    + apply L2 in Heqb0. apply bivaluation_dec2 in Heqb. 
      apply Heqb in Heqb0. destruct Heqb0.
    Admitted.

(* Lemma designatedValue_prop : forall φ v, bivaluation v ->
(h_atom φ v = One <-> (v φ = ⊤ /\ v (¬φ) = ⊥)) /\
(h_atom φ v = Half <-> (v φ = ⊤ /\ v (¬φ) = ⊤)) /\ 
(h_atom φ v = Zero <-> (v φ = ⊤ /\ v (¬φ) = ⊤)).
Proof.
  intros. split.
  - intros. induction φ.
    + split.
      * intros. simpl in H0. destruct (v #a), (v ¬#a); try discriminate H0; split;
        reflexivity.
      * intros. simpl. destruct (v #a), (v ¬#a); destruct H0; try discriminate H0;
        try discriminate H1; reflexivity.
    + split.
      * intros. simpl in H0. remember (h_atom φ v). destruct m; try discriminate H0.
        rewrite Heqm in IHφ.
Qed.  *)

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