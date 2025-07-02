From LFI1 Require Import Utils Language Deduction Semantics.
From LFI1 Require Import Deduction_metatheorem Soundness.
From Stdlib Require Import Arith Constructive_sets Image.
From Coq Require Import Equality.
From LFI1 Require Import Cardinality.

Fact t1 : forall Γ φ, Γ ⊢ ∘φ → ∘¬φ.
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
  unfold Δᵥ. unfold valuation in v_is_valuation. destruct_conjunction v_is_valuation. dependent induction φ.
  - simpl. apply Premisse. apply Im_intro with (#a); reflexivity.
  - simpl. unfold preserveNeg in L2. specialize (L2 f). unfold kalmar_function in *. destruct (v ¬f).

End Kalmar_like.

