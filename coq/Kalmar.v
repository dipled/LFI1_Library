From LFI1 Require Import Utils Language Deduction Semantics.
From LFI1 Require Import Deduction_metatheorem Soundness.
From Stdlib Require Import Arith Constructive_sets Image.
From Coq Require Import Equality.
From LFI1 Require Import Cardinality.

Fact T1 : forall Γ φ, Γ ⊢ ∘φ → ∘¬φ.
Proof.
  intros. apply deduction_metatheorem.
  pose proof (id (Γ ∪ [∘φ]) ∘¬φ).
  assert (Γ ∪ [∘φ] ⊢ ¬∘¬φ → ∘¬φ).
  - apply -> deduction_metatheorem. 
  assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬∘¬φ).
    apply Premisse. right. reflexivity. assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬∘¬φ → (¬φ ∧ ¬¬φ)). apply (AxiomInstance _ (ci ¬φ)). assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ (¬φ ∧ ¬¬φ)). apply (MP _ ¬∘¬φ _); assumption. assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬φ ∧ ¬¬φ → ¬φ ). apply (AxiomInstance _ (Ax4 ¬φ ¬¬φ)).
    assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬φ). apply (MP _ ¬φ ∧ ¬¬φ _); assumption.
    assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬φ ∧ ¬¬φ → ¬¬φ ). apply (AxiomInstance _ (Ax5 ¬φ ¬¬φ)).
    assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬¬φ). apply (MP _ ¬φ ∧ ¬¬φ _); assumption.
    assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬¬φ → φ). apply (AxiomInstance _ (cf _)).
    assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ φ). apply (MP _ ¬¬φ); assumption.
    apply (MP _ ¬φ). apply (MP _ φ). apply (MP _ ∘φ). apply (AxiomInstance _ (bc1 _ _)). apply Premisse. left. right. reflexivity. assumption.
    assumption.
  - assert (Γ ∪ [∘φ] ⊢ (∘¬φ → ∘¬φ) → (¬∘¬φ → ∘¬φ) → (∘¬φ ∨ ¬∘¬φ) → ∘¬φ).
    apply (AxiomInstance _ (Ax8 _ _ _)). assert (Γ ∪ [∘φ] ⊢ ∘¬φ ∨ ¬∘¬φ).
    apply (AxiomInstance _ (Ax10 _)). apply (MP _ ∘¬φ ∨ ¬∘¬φ).
    apply (MP _ (¬∘¬φ → ∘¬φ)). apply (MP _ (∘¬φ → ∘¬φ)). assumption.
    assumption. assumption. assumption.
Qed.

Fact T2 : forall Γ φ, Γ ⊢ ¬∘φ → ¬∘¬φ.
Proof.
  intros. apply deduction_metatheorem.
  assert (Γ ∪ [¬∘φ] ⊢ ¬∘φ → φ ∧ ¬φ). apply (AxiomInstance _ (ci _)).
  assert (Γ ∪ [¬∘φ] ⊢ φ ∧ ¬φ). apply (MP _ ¬∘φ). assumption. apply Premisse.
  right. reflexivity. assert ( Γ ∪ [¬∘φ] ⊢ φ). apply (MP _ φ ∧ ¬φ).
  apply (AxiomInstance _ (Ax4 _ _)). assumption. assert ( Γ ∪ [¬∘φ] ⊢ ¬φ).
  apply (MP _ φ ∧ ¬φ). apply (AxiomInstance _ (Ax5 _ _)). assumption.
  assert (Γ ∪ [¬∘φ] ⊢ ¬¬φ). apply (MP _ φ). apply (AxiomInstance _ (ce _)). assumption.
  assert (Γ ∪ [¬∘φ] ⊢ ∘¬φ ∨ ¬∘¬φ). apply (AxiomInstance _ (Ax10 _)).
  assert (Γ ∪ [¬∘φ] ⊢ ∘¬φ → ¬∘¬φ). apply -> deduction_metatheorem.
  apply (MP _ ¬¬φ). apply (MP _ ¬φ). apply (MP _ ∘¬φ). apply (AxiomInstance _ (bc1 _ _)).
  apply Premisse. right. reflexivity.
  apply (lfi1_monotonicity _ (Γ ∪ [¬∘φ])). split. assumption. left. assumption.
  apply (lfi1_monotonicity _ (Γ ∪ [¬∘φ])). split. assumption. left. assumption.
  assert (Γ ∪ [¬∘φ] ⊢ ¬∘¬φ → ¬∘¬φ). apply id. assert (Γ ∪ [¬∘φ] ⊢ (∘¬φ → ¬∘¬φ) → (¬∘¬φ → ¬∘¬φ) → (∘¬φ ∨ ¬∘¬φ) → ¬∘¬φ). apply (AxiomInstance _ (Ax8 _ _ _)). apply (MP _ ∘¬φ ∨ ¬∘¬φ).
  apply (MP _ (¬∘¬φ → ¬∘¬φ)). apply (MP _ (∘¬φ → ¬∘¬φ)). assumption. assumption.
  assumption. assumption. 
Qed.

Fact T3 : forall Γ φ, Γ ⊢ ∘¬∘φ.
Proof.
  intros. pose proof (AxiomInstance Γ (Ax10 ∘¬∘φ)). simpl in H.
  pose proof (id Γ ∘¬∘φ).
  assert (Γ ⊢ ¬∘¬∘φ → ∘¬∘φ).
  apply deduction_metatheorem. assert (Γ ∪ [¬∘¬∘φ] ⊢ ¬∘φ ∧ ¬¬∘φ).
  apply (MP _ ¬∘¬∘φ). apply (AxiomInstance _ (ci _)). apply Premisse. right. reflexivity.
  assert (Γ ∪ [¬∘¬∘φ] ⊢ ¬∘φ). apply (MP _ ¬∘φ ∧ ¬¬∘φ). apply (AxiomInstance _ (Ax4 _ _)).
  assumption. assert (Γ ∪ [¬∘¬∘φ] ⊢ ¬¬∘φ). apply (MP _ ¬∘φ ∧ ¬¬∘φ).
  apply (AxiomInstance _ (Ax5 _ _)). assumption. assert (Γ ∪ [¬∘¬∘φ] ⊢ ∘φ).
  apply (MP _ ¬¬∘φ). apply (AxiomInstance _ (cf _)). assumption.
  assert (Γ ∪ [¬∘¬∘φ] ⊢ φ ∧ ¬φ). apply (MP _ ¬∘φ).
  apply (AxiomInstance _ (ci _)). assumption. assert (Γ ∪ [¬∘¬∘φ] ⊢ φ).
  apply (MP _ φ ∧ ¬φ). apply (AxiomInstance _ (Ax4 _ _)). assumption.
  assert (Γ ∪ [¬∘¬∘φ] ⊢ ¬φ).
  apply (MP _ φ ∧ ¬φ). apply (AxiomInstance _ (Ax5 _ _)). assumption.
  apply (MP _ ¬φ). apply (MP _ φ). apply (MP _ ∘φ). apply (AxiomInstance _ (bc1 _ _)).
  assumption. assumption. assumption. apply (MP _ ∘¬∘φ ∨ ¬∘¬∘φ).
  apply (MP _ ¬∘¬∘φ → ∘¬∘φ). apply (MP _ ∘¬∘φ → ∘¬∘φ). apply (AxiomInstance _ (Ax8 _ _ _)).
  assumption. assumption. assumption.
Qed.


Arguments Im {U} {V}.

Definition kalmar_function (v : Formula -> MatrixDomain) (φ : Formula):=
  match v φ with
  | Zero => ∘φ ∧ ¬φ
  | One => ∘φ ∧ φ
  | Half => ¬∘φ
  end.

Section Kalmar_like.
  Variable v : Formula -> MatrixDomain.
  Variable v_is_valuation : valuation v.
  Variable φ : Formula.

  Definition Δᵥ := Im (atoms φ) (kalmar_function v).

Theorem kalmar: Δᵥ ⊢ kalmar_function v φ.
Proof.
  unfold Δᵥ. unfold valuation in v_is_valuation. induction φ.
  - simpl. apply Premisse. apply Im_intro with (#a); reflexivity.
  - destruct_conjunction v_is_valuation. simpl. unfold preserveNeg in L2. specialize (L2 f). unfold kalmar_function at 2. unfold kalmar_function at 2 in IHf. destruct (v ¬f); destruct (v f); try discriminate L2.
    + assert (Im (atoms f) (kalmar_function v) ⊢ ∘f). apply (MP _ ∘f ∧ ¬f).
      apply (AxiomInstance _ (Ax4 _ _)). assumption.
      assert (Im (atoms f) (kalmar_function v) ⊢ ¬f). apply (MP _ ∘f ∧ ¬f).
      apply (AxiomInstance _ (Ax5 _ _)). assumption.
      assert ((Im (atoms f) (kalmar_function v) ⊢ ∘¬f)). apply (MP _ ∘f).
      apply T1. assumption. apply (MP _ ¬f). apply (MP _ ∘¬f).
      apply (AxiomInstance _ (Ax3 _ _)). assumption. assumption.
    + apply (MP _ ¬∘f). apply T2. assumption.
    + assert (Im (atoms f) (kalmar_function v) ⊢ ∘f).
      apply (MP _ ∘f ∧ f). apply (AxiomInstance _ (Ax4 _ _)). assumption.
      assert (Im (atoms f) (kalmar_function v) ⊢ f).
      apply (MP _ ∘f ∧ f). apply(AxiomInstance _ (Ax5 _ _)). assumption.
      assert (Im (atoms f) (kalmar_function v) ⊢ ¬¬f). apply (MP _ f).
      apply (AxiomInstance _ (ce _)). assumption. apply (MP _ ¬¬f).
      apply (MP _ ∘¬f). apply (AxiomInstance _ (Ax3 _ _)).
      apply (MP _ ∘f). apply T1. apply H. apply H1.
  -
      
End Kalmar_like.

