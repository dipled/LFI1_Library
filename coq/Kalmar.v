From LFI1 Require Import Utils Language Deduction Semantics.
From LFI1 Require Import Deduction_metatheorem Soundness.
From Stdlib Require Import Arith Constructive_sets Image.
From Coq Require Import Equality.

Fact T1 : forall Γ φ, Γ ⊢ ∘φ → ∘¬φ.
Proof.
  intros. apply deduction_metatheorem.
  pose proof (id (Γ ∪ [∘φ]) ∘¬φ).
  assert (Γ ∪ [∘φ] ⊢ ¬∘¬φ → ∘¬φ).
  - apply -> deduction_metatheorem. 
  assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬∘¬φ).
    apply Premisse. right. reflexivity. assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬∘¬φ → (¬φ ∧ ¬¬φ)). 
    apply (AxiomInstance _ (ci ¬φ)). assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ (¬φ ∧ ¬¬φ)). apply (MP _ ¬∘¬φ _); 
    assumption. assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬φ ∧ ¬¬φ → ¬φ ). apply (AxiomInstance _ (Ax4 ¬φ ¬¬φ)).
    assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬φ). apply (MP _ ¬φ ∧ ¬¬φ _); assumption.
    assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬φ ∧ ¬¬φ → ¬¬φ ). apply (AxiomInstance _ (Ax5 ¬φ ¬¬φ)).
    assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬¬φ). apply (MP _ ¬φ ∧ ¬¬φ _); assumption.
    assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ ¬¬φ → φ). apply (AxiomInstance _ (cf _)).
    assert (Γ ∪ [∘φ] ∪ [¬∘¬φ] ⊢ φ). apply (MP _ ¬¬φ); assumption.
    apply (MP _ ¬φ). apply (MP _ φ). apply (MP _ ∘φ). apply (AxiomInstance _ (bc1 _ _)). 
    apply Premisse. left. right. reflexivity. assumption.
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
  assert (Γ ∪ [¬∘φ] ⊢ ¬∘¬φ → ¬∘¬φ). apply id. 
  assert (Γ ∪ [¬∘φ] ⊢ (∘¬φ → ¬∘¬φ) → (¬∘¬φ → ¬∘¬φ) → (∘¬φ ∨ ¬∘¬φ) → ¬∘¬φ). 
  apply (AxiomInstance _ (Ax8 _ _ _)). 
  apply (MP _ ∘¬φ ∨ ¬∘¬φ).
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

Fact T4 : forall Γ φ ψ, Γ ⊢ ((∘φ ∧ φ) ∧ (∘ψ ∧ ψ)) → (∘(φ ∧ ψ) ∧ (φ ∧ ψ)).
Proof.
  intros. apply deduction_metatheorem.
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ⊢ ∘φ ∧ φ). apply (MP _ ∘φ ∧ φ ∧ (∘ψ ∧ ψ)).
  apply (AxiomInstance _ (Ax4 _ _)). apply Premisse. right. reflexivity.
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ⊢ ∘ψ ∧ ψ). apply (MP _ ∘φ ∧ φ ∧ (∘ψ ∧ ψ)).
  apply (AxiomInstance _ (Ax5 _ _)). apply Premisse. right. reflexivity.
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ⊢ ∘φ). apply (MP _ ∘φ ∧ φ).
  apply (AxiomInstance _ (Ax4 _ _)). assumption.
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ⊢ φ). apply (MP _ ∘φ ∧ φ).
  apply (AxiomInstance _ (Ax5 _ _)). assumption.
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ⊢ ∘ψ). apply (MP _ ∘ψ ∧ ψ).
  apply (AxiomInstance _ (Ax4 _ _)). assumption.
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ⊢ ψ). apply (MP _ ∘ψ ∧ ψ).
  apply (AxiomInstance _ (Ax5 _ _)). assumption.
  pose proof (AxiomInstance (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)]) (Ax10 ∘(φ ∧ ψ))). simpl in H5.
  pose proof (id (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)]) ∘(φ ∧ ψ)).
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ⊢ ¬∘(φ ∧ ψ) → ∘(φ ∧ ψ)).
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ⊢ ¬∘(φ ∧ ψ) → (φ ∧ ψ) ∧ ¬((φ ∧ ψ))).
  apply (AxiomInstance _ (ci _)). apply -> deduction_metatheorem. apply deduction_metatheorem in H7.
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ∪ [¬∘(φ ∧ ψ)] ⊢ ¬(φ ∧ ψ)). apply (MP _ (φ ∧ ψ ∧ ¬(φ ∧ ψ))).
  apply (AxiomInstance _ (Ax5 _ _)). assumption. assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ∪ [¬∘(φ ∧ ψ)] ⊢ ¬φ ∨ ¬ ψ).
  apply (MP _ ¬(φ ∧ ψ)). apply (AxiomInstance _ (negland1 _ _)). assumption. 
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ∪ [¬∘(φ ∧ ψ)] ⊢ ¬φ → ∘(φ ∧ ψ)). apply (MP _ φ).
  apply (MP _ ∘φ). apply (AxiomInstance _ (bc1 _ _)). apply (lfi1_monotonicity _ (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)])).
  split. assumption. left. assumption. apply (lfi1_monotonicity _ (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)])). split.
  assumption. left. assumption.
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ∪ [¬∘(φ ∧ ψ)] ⊢ ¬ψ → ∘(φ ∧ ψ)). apply (MP _ ψ).
  apply (MP _ ∘ψ). apply (AxiomInstance _ (bc1 _ _)). apply (lfi1_monotonicity _ (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)])).
  split. assumption. left. assumption. apply (lfi1_monotonicity _ (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)])). split.
  assumption. left. assumption. apply (MP _ ¬φ ∨ ¬ψ). apply (MP _ ¬ψ → ∘(φ ∧ ψ)). apply (MP _ ¬φ → ∘(φ ∧ ψ)).
  apply (AxiomInstance _ (Ax8 _ _ _)). assumption. assumption. assumption.
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ⊢ ∘(φ ∧ ψ)). apply (MP _ ∘(φ ∧ ψ) ∨ ¬∘(φ ∧ ψ)). 
  apply (MP _ ¬∘(φ ∧ ψ) → ∘(φ ∧ ψ)). apply (MP _ ∘(φ ∧ ψ) → ∘(φ ∧ ψ)). apply (AxiomInstance _ (Ax8 _ _ _)).
  assumption. assumption. assumption. assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ⊢ (φ ∧ ψ)).
  apply (MP _ ψ). apply (MP _ φ). apply (AxiomInstance _ (Ax3 _ _)). assumption. assumption.
  apply (MP _ (φ ∧ ψ)). apply (MP _ ∘(φ ∧ ψ)). apply (AxiomInstance _ (Ax3 _ _)).
  assumption. assumption.
Qed.

Fact T5 : forall Γ φ ψ, Γ ⊢ ((∘φ ∧ ¬φ) ∨ (∘ψ ∧ ¬ψ)) → (∘(φ ∧ ψ) ∧ ¬(φ ∧ ψ)).
Proof.
  intros.
  assert (Γ ⊢ ∘φ ∧ ¬φ → ∘(φ ∧ ψ) ∧ ¬(φ ∧ ψ)).
  apply -> deduction_metatheorem. 
  assert (Γ ∪ [∘φ ∧ ¬φ] ⊢ ∘φ ).
  apply (MP _ ∘φ ∧ ¬φ). apply (AxiomInstance _ (Ax4 _ _)). apply Premisse. right.
  reflexivity. 
  assert (Γ ∪ [∘φ ∧ ¬φ] ⊢ ¬φ ).
  apply (MP _ ∘φ ∧ ¬φ). apply (AxiomInstance _ (Ax5 _ _)). apply Premisse. right.
  reflexivity.
  assert  (Γ ∪ [∘φ ∧ ¬φ] ⊢ ∘(φ ∧ ψ) → ∘(φ ∧ ψ)). apply id.
  assert (Γ ∪ [∘φ ∧ ¬φ] ⊢ ¬∘(φ ∧ ψ) → ∘(φ ∧ ψ)).
  apply -> deduction_metatheorem.
  assert (Γ ∪ [∘φ ∧ ¬φ] ∪ [¬∘(φ ∧ ψ)] ⊢ (φ ∧ ψ) ∧ ¬(φ ∧ ψ)).
  apply (MP _ ¬∘(φ ∧ ψ)). apply (AxiomInstance _ (ci _)). apply Premisse.
  right. reflexivity.
  assert (Γ ∪ [∘φ ∧ ¬φ] ∪ [¬∘(φ ∧ ψ)] ⊢ φ ∧ ψ).
  apply (MP _ φ ∧ ψ ∧ ¬(φ ∧ ψ)). apply (AxiomInstance _ (Ax4 _ _)). assumption.
  assert (Γ ∪ [∘φ ∧ ¬φ] ∪ [¬∘(φ ∧ ψ)] ⊢ ¬(φ ∧ ψ)).
  apply (MP _ φ ∧ ψ ∧ ¬(φ ∧ ψ)). apply (AxiomInstance _ (Ax5 _ _)). assumption.
  assert (Γ ∪ [∘φ ∧ ¬φ] ∪ [¬∘(φ ∧ ψ)] ⊢ φ).
  apply (MP _ φ ∧ ψ). apply (AxiomInstance _ (Ax4 _ _)). assumption.
  assert (Γ ∪ [∘φ ∧ ¬φ] ∪ [¬∘(φ ∧ ψ)] ⊢ ψ).
  apply (MP _ φ ∧ ψ). apply (AxiomInstance _ (Ax5 _ _)). assumption.
  assert (Γ ∪ [∘φ ∧ ¬φ] ∪ [¬∘(φ ∧ ψ)] ⊢ ¬φ ∨ ¬ψ).
  apply (MP _ ¬(φ ∧ ψ)). apply (AxiomInstance _ (negland1 _ _)).
  assumption. apply (MP _ ¬φ). apply (MP _ φ). apply (MP _ ∘φ). 
  apply (AxiomInstance _ (bc1 _ _)).
  apply (lfi1_monotonicity _ (Γ ∪ [∘φ ∧ ¬φ])).
  split. assumption. left. assumption. assumption. 
  apply (lfi1_monotonicity _ (Γ ∪ [∘φ ∧ ¬φ])).
  split. assumption. left. assumption.
  assert (Γ ∪ [∘φ ∧ ¬φ] ⊢ ∘(φ ∧ ψ)). 
  apply (MP _ (∘(φ ∧ ψ) ∨ ¬∘(φ ∧ ψ))). apply (MP _ ¬∘(φ ∧ ψ) → ∘(φ ∧ ψ)).
  apply (MP _ (∘(φ ∧ ψ) → ∘(φ ∧ ψ))). apply (AxiomInstance _ (Ax8 _ _ _)).
  assumption. assumption. apply (AxiomInstance _ (Ax10 _)).
  assert (Γ ∪ [∘φ ∧ ¬φ] ⊢ ¬(φ ∧ ψ)).
  apply (MP _ ¬φ ∨ ¬ψ). apply (AxiomInstance _ (negland2 _ _)).
  apply (MP _ ¬φ). apply (AxiomInstance _ (Ax6 _ _)). assumption.
  apply (MP _ ¬(φ ∧ ψ)). apply (MP _ ∘(φ ∧ ψ)). apply (AxiomInstance _ (Ax3 _ _)).
  assumption. assumption.
  assert (Γ ⊢ ∘ψ ∧ ¬ψ → ∘(φ ∧ ψ) ∧ ¬(φ ∧ ψ)).
  apply -> deduction_metatheorem. 
  assert (Γ ∪ [∘ψ ∧ ¬ψ] ⊢ ∘ψ ).
  apply (MP _ ∘ψ ∧ ¬ψ). apply (AxiomInstance _ (Ax4 _ _)). apply Premisse. right.
  reflexivity. 
  assert (Γ ∪ [∘ψ ∧ ¬ψ] ⊢ ¬ψ ).
  apply (MP _ ∘ψ ∧ ¬ψ). apply (AxiomInstance _ (Ax5 _ _)). apply Premisse. right.
  reflexivity.
  assert  (Γ ∪ [∘ψ ∧ ¬ψ] ⊢ ∘(φ ∧ ψ) → ∘(φ ∧ ψ)). apply id.
  assert (Γ ∪ [∘ψ ∧ ¬ψ] ⊢ ¬∘(φ ∧ ψ) → ∘(φ ∧ ψ)).
  apply -> deduction_metatheorem.
  assert (Γ ∪ [∘ψ ∧ ¬ψ] ∪ [¬∘(φ ∧ ψ)] ⊢ (φ ∧ ψ) ∧ ¬(φ ∧ ψ)).
  apply (MP _ ¬∘(φ ∧ ψ)). apply (AxiomInstance _ (ci _)). apply Premisse.
  right. reflexivity.
  assert (Γ ∪ [∘ψ ∧ ¬ψ] ∪ [¬∘(φ ∧ ψ)] ⊢ φ ∧ ψ).
  apply (MP _ φ ∧ ψ ∧ ¬(φ ∧ ψ)). apply (AxiomInstance _ (Ax4 _ _)). assumption.
  assert (Γ ∪ [∘ψ ∧ ¬ψ] ∪ [¬∘(φ ∧ ψ)] ⊢ ¬(φ ∧ ψ)).
  apply (MP _ φ ∧ ψ ∧ ¬(φ ∧ ψ)). apply (AxiomInstance _ (Ax5 _ _)). assumption.
  assert (Γ ∪ [∘ψ ∧ ¬ψ] ∪ [¬∘(φ ∧ ψ)] ⊢ φ).
  apply (MP _ φ ∧ ψ). apply (AxiomInstance _ (Ax4 _ _)). assumption.
  assert (Γ ∪ [∘ψ ∧ ¬ψ] ∪ [¬∘(φ ∧ ψ)] ⊢ ψ).
  apply (MP _ φ ∧ ψ). apply (AxiomInstance _ (Ax5 _ _)). assumption.
  assert (Γ ∪ [∘ψ ∧ ¬ψ] ∪ [¬∘(φ ∧ ψ)] ⊢ ¬φ ∨ ¬ψ).
  apply (MP _ ¬(φ ∧ ψ)). apply (AxiomInstance _ (negland1 _ _)).
  assumption. apply (MP _ ¬ψ). apply (MP _ ψ). apply (MP _ ∘ψ). 
  apply (AxiomInstance _ (bc1 _ _)).
  apply (lfi1_monotonicity _ (Γ ∪ [∘ψ ∧ ¬ψ])).
  split. assumption. left. assumption. assumption. 
  apply (lfi1_monotonicity _ (Γ ∪ [∘ψ ∧ ¬ψ])).
  split. assumption. left. assumption.
  assert (Γ ∪ [∘ψ ∧ ¬ψ] ⊢ ∘(φ ∧ ψ)). 
  apply (MP _ (∘(φ ∧ ψ) ∨ ¬∘(φ ∧ ψ))). apply (MP _ ¬∘(φ ∧ ψ) → ∘(φ ∧ ψ)).
  apply (MP _ (∘(φ ∧ ψ) → ∘(φ ∧ ψ))). apply (AxiomInstance _ (Ax8 _ _ _)).
  assumption. assumption. apply (AxiomInstance _ (Ax10 _)).
  assert (Γ ∪ [∘ψ ∧ ¬ψ] ⊢ ¬(φ ∧ ψ)).
  apply (MP _ ¬φ ∨ ¬ψ). apply (AxiomInstance _ (negland2 _ _)).
  apply (MP _ ¬ψ). apply (AxiomInstance _ (Ax7 _ _)). assumption.
  apply (MP _ ¬(φ ∧ ψ)). apply (MP _ ∘(φ ∧ ψ)). apply (AxiomInstance _ (Ax3 _ _)).
  assumption. assumption.
  apply (MP _ ∘ψ ∧ ¬ψ → ∘(φ ∧ ψ) ∧ ¬(φ ∧ ψ)).
  apply (MP _ ∘φ ∧ ¬φ → ∘(φ ∧ ψ) ∧ ¬(φ ∧ ψ)).
  apply (AxiomInstance _ (Ax8 _ _ _)). assumption. assumption.
Qed.

Fact T6 : forall Γ φ ψ, Γ ⊢ ((∘φ ∧ ¬φ) ∧ (∘ψ ∧ ¬ψ)) → (∘(φ ∨ ψ) ∧ ¬(φ ∨ ψ)).
Proof.
  intros. apply deduction_metatheorem. apply (MP _ ¬(φ ∨ ψ)). apply (MP _ ∘(φ ∨ ψ)).
  apply (AxiomInstance _ (Ax3 _ _)). apply (MP _ (∘(φ ∨ ψ) ∨ ¬∘(φ ∨ ψ))).
  apply (MP _ ¬∘(φ ∨ ψ) → ∘(φ ∨ ψ)). apply (MP _ ∘(φ ∨ ψ) → ∘(φ ∨ ψ)).
  apply (AxiomInstance _ (Ax8 _ _ _)). apply id.
  apply -> deduction_metatheorem. assert (Γ ∪ [∘φ ∧ ¬φ ∧ (∘ψ ∧ ¬ψ)] ∪ [¬∘(φ ∨ ψ)] ⊢ φ ∨ ψ).
  apply (MP _ ((φ ∨ ψ) ∧ ¬(φ ∨ ψ))). apply (AxiomInstance _ (Ax4 _ _)).
  apply (MP _ ¬∘(φ ∨ ψ)). apply (AxiomInstance _ (ci _)). apply Premisse. right.
  reflexivity.
  apply (MP _ φ ∨ ψ). apply (MP _ ψ → ∘(φ ∨ ψ)). apply (MP _ φ → ∘(φ ∨ ψ)). 
  apply (AxiomInstance _ (Ax8 _ _ _)). 
  apply -> deduction_metatheorem.
  apply (MP _ ¬φ). apply (MP _ φ). apply (MP _ ∘φ). apply (AxiomInstance _ (bc1 _ _)).
  assert (Γ ∪ [∘φ ∧ ¬φ ∧ (∘ψ ∧ ¬ψ)] ∪ [¬∘(φ ∨ ψ)] ∪ [φ] ⊢ ∘φ ∧ ¬φ).
  apply (MP _ ∘φ ∧ ¬φ ∧ (∘ψ ∧ ¬ψ)). apply (AxiomInstance _ (Ax4 _ _)).
  apply Premisse. left. left. right. reflexivity. apply (MP _ ∘φ ∧ ¬φ).
  apply (AxiomInstance _ (Ax4 _ _)). assumption. apply Premisse. right.
  reflexivity.
  assert (Γ ∪ [∘φ ∧ ¬φ ∧ (∘ψ ∧ ¬ψ)] ∪ [¬∘(φ ∨ ψ)] ∪ [φ] ⊢ ∘φ ∧ ¬φ).
  apply (MP _ ∘φ ∧ ¬φ ∧ (∘ψ ∧ ¬ψ)). apply (AxiomInstance _ (Ax4 _ _)).
  apply Premisse. left. left. right. reflexivity. apply (MP _ ∘φ ∧ ¬φ).
  apply (AxiomInstance _ (Ax5 _ _)). assumption.
  apply -> deduction_metatheorem.  
  apply (MP _ ¬ψ). apply (MP _ ψ). apply (MP _ ∘ψ). apply (AxiomInstance _ (bc1 _ _)).
  assert (Γ ∪ [∘φ ∧ ¬φ ∧ (∘ψ ∧ ¬ψ)] ∪ [¬∘(φ ∨ ψ)] ∪ [ψ] ⊢ ∘ψ ∧ ¬ψ).
  apply (MP _ ∘φ ∧ ¬φ ∧ (∘ψ ∧ ¬ψ)). apply (AxiomInstance _ (Ax5 _ _)).
  apply Premisse. left. left. right. reflexivity. apply (MP _ ∘ψ ∧ ¬ψ).
  apply (AxiomInstance _ (Ax4 _ _)). assumption. apply Premisse. right.
  reflexivity.
  assert (Γ ∪ [∘φ ∧ ¬φ ∧ (∘ψ ∧ ¬ψ)] ∪ [¬∘(φ ∨ ψ)] ∪ [ψ] ⊢ ∘ψ ∧ ¬ψ).
  apply (MP _ ∘φ ∧ ¬φ ∧ (∘ψ ∧ ¬ψ)). apply (AxiomInstance _ (Ax5 _ _)).
  apply Premisse. left. left. right. reflexivity. apply (MP _ ∘ψ ∧ ¬ψ).
  apply (AxiomInstance _ (Ax5 _ _)). assumption. assumption.
  apply (AxiomInstance _ (Ax10 _)). apply (MP _ (¬φ ∧ ¬ψ)). apply (AxiomInstance _ (neglor2 _ _)).
  apply (MP _ ¬ψ). apply (MP _ ¬φ). apply (AxiomInstance _ (Ax3 _ _)).
  apply (MP _ ∘φ ∧ ¬φ). apply (AxiomInstance _ (Ax5 _ _)). apply (MP _ ∘φ ∧ ¬φ ∧ (∘ψ ∧ ¬ψ)).
  apply (AxiomInstance _ (Ax4 _ _)). apply Premisse. right. reflexivity.
  apply (MP _ ∘ψ ∧ ¬ψ). apply (AxiomInstance _ (Ax5 _ _)). apply (MP _ ∘φ ∧ ¬φ ∧ (∘ψ ∧ ¬ψ)).
  apply (AxiomInstance _ (Ax5 _ _)). apply Premisse. right. reflexivity.
Qed.

Fact T7 : forall Γ φ ψ, Γ ⊢ ((∘φ ∧ φ) ∧ (∘ψ ∧ ψ)) → (∘(φ ∨ ψ) ∧ (φ ∨ ψ)).
Proof.
  intros. apply deduction_metatheorem.
  apply (MP _ (φ ∨ ψ)). apply (MP _ ∘(φ ∨ ψ)). apply (AxiomInstance _ (Ax3 _ _)).
  apply (MP _ ∘(φ ∨ ψ) ∨ ¬∘(φ ∨ ψ)). apply (MP _ ¬∘(φ ∨ ψ)→∘(φ ∨ ψ)). apply (MP _ ∘(φ ∨ ψ)→∘(φ ∨ ψ)).
  apply (AxiomInstance _ (Ax8 _ _ _)). apply id. apply -> deduction_metatheorem.
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ∪ [¬∘(φ ∨ ψ)] ⊢ ¬(φ ∨ ψ)). 
  apply (MP _ (φ ∨ ψ) ∧ ¬(φ ∨ ψ)). apply (AxiomInstance _ (Ax5 _ _)).
  apply deduction_metatheorem. apply (AxiomInstance _ (ci _)).
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ∪ [¬∘(φ ∨ ψ)] ⊢ ¬φ ∧ ¬ψ).
  apply (MP _ ¬(φ ∨ ψ)). apply (AxiomInstance _ (neglor1 _ _)). assumption.
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ∪ [¬∘(φ ∨ ψ)] ⊢ ∘φ ∧ φ).
  apply (MP _ ∘φ ∧ φ ∧ (∘ψ ∧ ψ)). apply (AxiomInstance _ (Ax4 _ _)).
  apply Premisse. left. right. reflexivity.
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ∪ [¬∘(φ ∨ ψ)] ⊢ ∘φ).
  apply (MP _ ∘φ ∧ φ). apply (AxiomInstance _ (Ax4 _ _)). assumption.
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ∪ [¬∘(φ ∨ ψ)] ⊢ φ).
  apply (MP _ ∘φ ∧ φ). apply (AxiomInstance _ (Ax5 _ _)). assumption.
  apply (MP _ ¬φ). apply (MP _ φ). apply (MP _ ∘φ). apply (AxiomInstance _ (bc1 _ _)).
  assumption. assumption. apply (MP _ ¬φ ∧ ¬ψ). apply (AxiomInstance _ (Ax4 _ _)).
  assumption. apply (AxiomInstance _ (Ax10 _)).
  assert (Γ ∪ [∘φ ∧ φ ∧ (∘ψ ∧ ψ)] ⊢ φ).
  apply (MP _ ∘φ ∧ φ). apply (AxiomInstance _ (Ax5 _ _)).
  apply (MP _ ∘φ ∧ φ ∧ (∘ψ ∧ ψ)). apply (AxiomInstance _ (Ax4 _ _)).
  apply Premisse. right. reflexivity. apply (MP _ φ).
  apply (AxiomInstance _ (Ax6 _ _)). assumption. 
Qed.

Fact T8 : forall Γ φ ψ, Γ ⊢ ((∘φ ∧ ¬φ) ∨ (∘ψ ∧ ψ)) → (∘(φ → ψ) ∧ (φ → ψ)).
Proof.
  intros. apply deduction_metatheorem. apply (MP _ (φ → ψ)). apply (MP _ ∘(φ → ψ)).
  apply (AxiomInstance _ (Ax3 _ _)). apply (MP _ (∘(φ → ψ) ∨ ¬∘(φ → ψ))).
  apply (MP _ ¬∘(φ → ψ) → ∘(φ → ψ)). apply (MP _ ∘(φ → ψ) → ∘(φ → ψ)).
  apply (AxiomInstance _ (Ax8 _ _ _)). apply id.
  apply -> deduction_metatheorem. assert (Γ ∪ [∘φ ∧ ¬φ ∨ (∘ψ ∧ ψ)] ∪ [¬∘(φ → ψ)] ⊢ ¬(φ → ψ)).
  apply (MP _ ((φ → ψ) ∧ ¬(φ → ψ))). apply (AxiomInstance _ (Ax5 _ _)).
  apply (MP _ ¬∘(φ → ψ)). apply (AxiomInstance _ (ci _)). apply Premisse. right.
  reflexivity. assert (Γ ∪ [∘φ ∧ ¬φ ∨ (∘ψ ∧ ψ)] ∪ [¬∘(φ → ψ)] ⊢ (φ ∧ ¬ψ)).
  apply (MP _ ¬(φ → ψ)). apply (AxiomInstance _ (negto1 _ _)). assumption.
  assert (Γ ∪ [∘φ ∧ ¬φ ∨ (∘ψ ∧ ψ)] ∪ [¬∘(φ → ψ)] ⊢ φ). apply (MP _ φ ∧ ¬ψ).
  apply (AxiomInstance _ (Ax4 _ _)). assumption. assert (Γ ∪ [∘φ ∧ ¬φ ∨ (∘ψ ∧ ψ)] ∪ [¬∘(φ → ψ)] ⊢ ¬ψ).
  apply (MP _ φ ∧ ¬ψ). apply (AxiomInstance _ (Ax5 _ _)). assumption.
  apply (MP _ ∘φ ∧ ¬φ ∨ ∘ψ ∧ ψ). apply (MP _ ∘ψ ∧ ψ → ∘(φ → ψ)). apply (MP _ ∘φ ∧ ¬φ → ∘(φ → ψ)).
  apply (AxiomInstance _ (Ax8 _ _ _)). 
  apply -> deduction_metatheorem.
  assert (Γ ∪ [∘φ ∧ ¬φ ∨ (∘ψ ∧ ψ)] ∪ [¬∘(φ → ψ)] ∪ [∘φ ∧ ¬φ]  ⊢ ∘φ).
  apply (MP _ ∘φ ∧ ¬φ). apply (AxiomInstance _ (Ax4 _ _)). apply Premisse. right.
  reflexivity.
  assert (Γ ∪ [∘φ ∧ ¬φ ∨ (∘ψ ∧ ψ)] ∪ [¬∘(φ → ψ)] ∪ [∘φ ∧ ¬φ]  ⊢ ¬φ).
  apply (MP _ ∘φ ∧ ¬φ). apply (AxiomInstance _ (Ax5 _ _)). apply Premisse. right.
  reflexivity. apply (MP _ ¬φ). apply (MP _ φ). apply (MP _ ∘φ). apply (AxiomInstance _ (bc1 _ _)).
  assumption. apply (lfi1_monotonicity _ (Γ ∪ [∘φ ∧ ¬φ ∨ ∘ψ ∧ ψ] ∪ [¬∘(φ → ψ)])). split.
  assumption. left. assumption. assumption.
  apply -> deduction_metatheorem.
  assert (Γ ∪ [∘φ ∧ ¬φ ∨ (∘ψ ∧ ψ)] ∪ [¬∘(φ → ψ)] ∪ [∘ψ ∧ ψ]  ⊢ ∘ψ).
  apply (MP _ ∘ψ ∧ ψ). apply (AxiomInstance _ (Ax4 _ _)). apply Premisse. right.
  reflexivity.
  assert (Γ ∪ [∘φ ∧ ¬φ ∨ (∘ψ ∧ ψ)] ∪ [¬∘(φ → ψ)] ∪ [∘ψ ∧ ψ]  ⊢ ψ).
  apply (MP _ ∘ψ ∧ ψ). apply (AxiomInstance _ (Ax5 _ _)). apply Premisse. right.
  reflexivity. apply (MP _ ¬ψ). apply (MP _ ψ). apply (MP _ ∘ψ). apply (AxiomInstance _ (bc1 _ _)).
  assumption. assumption. apply (lfi1_monotonicity _ (Γ ∪ [∘φ ∧ ¬φ ∨ ∘ψ ∧ ψ] ∪ [¬∘(φ → ψ)])). split.
  assumption. left. assumption. apply Premisse. left. right. reflexivity.
  apply (AxiomInstance _ (Ax10 _)). apply -> deduction_metatheorem.
  apply (MP _ ∘φ ∧ ¬φ ∨ ∘ψ ∧ ψ). apply (MP _ ∘ψ ∧ ψ → ψ). apply (MP _ ∘φ ∧ ¬φ → ψ).
  apply (AxiomInstance _ (Ax8 _ _ _)). 
  apply -> deduction_metatheorem. assert (Γ ∪ [∘φ ∧ ¬φ ∨ ∘ψ ∧ ψ] ∪ [φ] ∪ [∘φ ∧ ¬φ]  ⊢ ∘φ).
  apply (MP _ ∘φ ∧ ¬φ). apply (AxiomInstance _ (Ax4 _ _)). apply Premisse. right.
  reflexivity.
  assert (Γ ∪ [∘φ ∧ ¬φ ∨ ∘ψ ∧ ψ] ∪ [φ] ∪ [∘φ ∧ ¬φ]  ⊢ ¬φ).
  apply (MP _ ∘φ ∧ ¬φ). apply (AxiomInstance _ (Ax5 _ _)). apply Premisse. right.
  reflexivity. apply (MP _ ¬φ). apply (MP _ φ). apply (MP _ ∘φ). apply (AxiomInstance _ (bc1 _ _)).
  assumption. apply Premisse. left. right. reflexivity.
  assumption.
  apply -> deduction_metatheorem.
  apply (MP _ ∘ψ ∧ ψ). apply (AxiomInstance _ (Ax5 _ _)). apply Premisse. right.
  reflexivity. apply Premisse. left. right. reflexivity.
Qed.

Fact T10 : forall Γ φ ψ, Γ ⊢ ((¬∘φ ∧ ¬∘ψ) → (¬∘(φ ∧ ψ) ∧ ¬∘(φ ∨ ψ) ∧ ¬∘(φ → ψ))).
Proof.
  intros. apply deduction_metatheorem. 
  assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ¬∘φ).
  apply (MP _ ¬∘φ ∧ ¬∘ψ). apply (AxiomInstance _ (Ax4 _ _)). apply Premisse. right. reflexivity.
  assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ¬∘ψ).
  apply (MP _ ¬∘φ ∧ ¬∘ψ). apply (AxiomInstance _ (Ax5 _ _)). apply Premisse. right. reflexivity.
  assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ φ).
  apply (MP _ φ ∧ ¬φ). apply (AxiomInstance _ (Ax4 _ _)). apply (MP _ ¬∘φ). apply (AxiomInstance _ (ci _)).
  assumption.
  assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ¬φ).
  apply (MP _ φ ∧ ¬φ). apply (AxiomInstance _ (Ax5 _ _)). apply (MP _ ¬∘φ). apply (AxiomInstance _ (ci _)).
  assumption.
  assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ψ).
  apply (MP _ ψ ∧ ¬ψ). apply (AxiomInstance _ (Ax4 _ _)). apply (MP _ ¬∘ψ). apply (AxiomInstance _ (ci _)).
  assumption.
  assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ¬ψ).
  apply (MP _ ψ ∧ ¬ψ). apply (AxiomInstance _ (Ax5 _ _)). apply (MP _ ¬∘ψ). apply (AxiomInstance _ (ci _)).
  assumption.
  assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ¬∘(φ ∧ ψ)).
  {
    assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ¬∘(φ ∧ ψ) → ¬∘(φ ∧ ψ)). apply id.
    assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ∘(φ ∧ ψ) → ¬∘(φ ∧ ψ)). apply -> deduction_metatheorem.
    assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ∪ [∘(φ ∧ ψ)] ⊢ (φ ∧ ψ)). apply (MP _ ψ).
    apply (MP _ φ). apply (AxiomInstance _ (Ax3 _ _)). 
    apply (lfi1_monotonicity _ (Γ ∪ [¬∘φ ∧ ¬∘ψ])). split.
    assumption. left. assumption.
    apply (lfi1_monotonicity _ (Γ ∪ [¬∘φ ∧ ¬∘ψ])). split.
    assumption. left. assumption.
    assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ∪ [∘(φ ∧ ψ)] ⊢ ¬(φ ∧ ψ)). apply (MP _ ¬φ ∨ ¬ψ).
    apply (AxiomInstance _ (negland2 _ _)).
    apply (MP _ ¬ψ). apply (AxiomInstance _ (Ax7 _ _)). 
    apply (lfi1_monotonicity _ (Γ ∪ [¬∘φ ∧ ¬∘ψ])). split.
    assumption. left. assumption.
    apply (MP _ ¬(φ ∧ ψ)). apply (MP _ (φ ∧ ψ)). apply (MP _ ∘(φ ∧ ψ)).
    apply (AxiomInstance _ (bc1 _ _)). apply Premisse. right. reflexivity.
    assumption. assumption. apply (MP _ ∘(φ ∧ ψ) ∨ ¬∘(φ ∧ ψ)).
    apply (MP _ ¬∘(φ ∧ ψ) → ¬∘(φ ∧ ψ)). apply (MP _ ∘(φ ∧ ψ) → ¬∘(φ ∧ ψ)).
    apply (AxiomInstance _ (Ax8 _ _ _)). assumption. assumption.
    apply (AxiomInstance _ (Ax10 _)).
  }
  assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ¬∘(φ ∨ ψ)).
  {
    assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ¬∘(φ ∨ ψ) → ¬∘(φ ∨ ψ)). apply id.
    assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ∘(φ ∨ ψ) → ¬∘(φ ∨ ψ)). apply -> deduction_metatheorem.
    assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ∪ [∘(φ ∨ ψ)] ⊢ (φ ∨ ψ)). apply (MP _ ψ).
    apply (AxiomInstance _ (Ax7 _ _)). 
    apply (lfi1_monotonicity _ (Γ ∪ [¬∘φ ∧ ¬∘ψ])). split.
    assumption. left. assumption.
    assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ∪ [∘(φ ∨ ψ)] ⊢ ¬(φ ∨ ψ)). apply (MP _ ¬φ ∧ ¬ψ).
    apply (AxiomInstance _ (neglor2 _ _)).
    apply (MP _ ¬ψ). apply (MP _ ¬φ). apply (AxiomInstance _ (Ax3 _ _)). 
    apply (lfi1_monotonicity _ (Γ ∪ [¬∘φ ∧ ¬∘ψ])). split.
    assumption. left. assumption.
    apply (lfi1_monotonicity _ (Γ ∪ [¬∘φ ∧ ¬∘ψ])). split.
    assumption. left. assumption.
    apply (MP _ ¬(φ ∨ ψ)). apply (MP _ (φ ∨ ψ)). apply (MP _ ∘(φ ∨ ψ)).
    apply (AxiomInstance _ (bc1 _ _)). apply Premisse. right. reflexivity.
    assumption. assumption. apply (MP _ ∘(φ ∨ ψ) ∨ ¬∘(φ ∨ ψ)).
    apply (MP _ ¬∘(φ ∨ ψ) → ¬∘(φ ∨ ψ)). apply (MP _ ∘(φ ∨ ψ) → ¬∘(φ ∨ ψ)).
    apply (AxiomInstance _ (Ax8 _ _ _)). assumption. assumption.
    apply (AxiomInstance _ (Ax10 _)).
  }
  assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ¬∘(φ → ψ)).
  {
    assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ¬∘(φ → ψ) → ¬∘(φ → ψ)). apply id.
    assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ⊢ ∘(φ → ψ) → ¬∘(φ → ψ)). apply -> deduction_metatheorem.
    assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ∪ [∘(φ → ψ)] ⊢ (φ → ψ)). apply (MP _ ψ).
    apply (AxiomInstance _ (Ax1 _ _)). 
    apply (lfi1_monotonicity _ (Γ ∪ [¬∘φ ∧ ¬∘ψ])). split.
    assumption. left. assumption.
    assert (Γ ∪ [¬∘φ ∧ ¬∘ψ] ∪ [∘(φ → ψ)] ⊢ ¬(φ → ψ)). apply (MP _ φ ∧ ¬ψ).
    apply (AxiomInstance _ (negto2 _ _)).
    apply (MP _ ¬ψ). apply (MP _ φ). apply (AxiomInstance _ (Ax3 _ _)). 
    apply (lfi1_monotonicity _ (Γ ∪ [¬∘φ ∧ ¬∘ψ])). split.
    assumption. left. assumption.
    apply (lfi1_monotonicity _ (Γ ∪ [¬∘φ ∧ ¬∘ψ])). split.
    assumption. left. assumption.
    apply (MP _ ¬(φ → ψ)). apply (MP _ (φ → ψ)). apply (MP _ ∘(φ → ψ)).
    apply (AxiomInstance _ (bc1 _ _)). apply Premisse. right. reflexivity.
    assumption. assumption. apply (MP _ ∘(φ → ψ) ∨ ¬∘(φ → ψ)).
    apply (MP _ ¬∘(φ → ψ) → ¬∘(φ → ψ)). apply (MP _ ∘(φ → ψ) → ¬∘(φ → ψ)).
    apply (AxiomInstance _ (Ax8 _ _ _)). assumption. assumption.
    apply (AxiomInstance _ (Ax10 _)).
  }
  apply (MP _ ¬∘(φ → ψ)). apply (MP _ ¬∘(φ ∧ ψ) ∧ ¬∘(φ ∨ ψ)).
  apply (AxiomInstance _ (Ax3 _ _)).
  apply (MP _ ¬∘(φ ∨ ψ)). apply (MP _ ¬∘(φ ∧ ψ)).
  apply (AxiomInstance _ (Ax3 _ _)).
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
  - destruct_conjunction v_is_valuation. simpl. unfold preserveNeg in L2. 
  specialize (L2 f). unfold kalmar_function at 2. unfold kalmar_function at 2 in IHf. 
  destruct (v ¬f); destruct (v f); try discriminate L2.
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
  - destruct_conjunction v_is_valuation. simpl. unfold preserveAnd in L1.
    specialize (L1 f1 f2).
    assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ kalmar_function v f1).
      apply (lfi1_monotonicity _ (Im (atoms f1) (kalmar_function v))).
      split. assumption. unfold Included. intros. destruct H. apply Im_intro with (x := x). left. 
      assumption. assumption. 
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ kalmar_function v f2).
      apply (lfi1_monotonicity _ (Im (atoms f2) (kalmar_function v))).
      split. assumption. unfold Included. intros. destruct H0. 
      apply Im_intro with (x := x). right. assumption. assumption.
    unfold kalmar_function at 2.
    unfold kalmar_function at 2 in H. unfold kalmar_function at 2 in H0.
    clear IHf1. clear IHf2.
    destruct (v f1 ∧ f2), (v f1), (v f2); try discriminate L1.
    + assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ∘f1 ∧ f1 ∧ (∘f2 ∧ f2)).
      apply (MP _ ∘f2 ∧ f2). apply (MP _ ∘f1 ∧ f1).
      apply (AxiomInstance _ (Ax3 _ _)). assumption. assumption.
      apply (MP _ ∘f1 ∧ f1 ∧ (∘f2 ∧ f2)). apply T4. assumption.
    + assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ f2 ∧ ¬f2).
      apply (MP _ ¬∘f2). apply (AxiomInstance _ (ci _)). assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ f2).
      apply (MP _ f2 ∧ ¬f2). apply (AxiomInstance _ (Ax4 _ _)). assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ¬f2).
      apply (MP _ f2 ∧ ¬f2). apply (AxiomInstance _ (Ax5 _ _)). assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ∘f1).
      apply (MP _ ∘f1 ∧ f1). apply (AxiomInstance _ (Ax4 _ _)). assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ f1).
      apply (MP _ ∘f1 ∧ f1). apply (AxiomInstance _ (Ax5 _ _)). assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ (f1 ∧ f2)).
      apply (MP _ f2). apply (MP _ f1). apply (AxiomInstance _ (Ax3 _ _)).
      assumption. assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ¬(f1 ∧ f2)).
      apply (MP _ ¬f1 ∨ ¬f2). apply (AxiomInstance _ (negland2 _ _)).
      apply (MP _ ¬f2). apply (AxiomInstance _ (Ax7 _ _)). assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ∘(f1 ∧ f2) → ¬∘(f1 ∧ f2)).
      apply deduction_metatheorem. apply (MP _ ¬(f1 ∧ f2)). apply (MP _ (f1 ∧ f2)).
      apply (MP _ ∘(f1 ∧ f2)). apply (AxiomInstance _ (bc1 _ _)).
      apply Premisse. right. reflexivity. 
      apply (lfi1_monotonicity _( Im (atoms f1 ∪ atoms f2) (kalmar_function v))). split. assumption. 
      left. assumption.
      apply (lfi1_monotonicity _( Im (atoms f1 ∪ atoms f2) (kalmar_function v))). split. assumption. 
      left. assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ¬∘(f1 ∧ f2) → ¬∘(f1 ∧ f2)).
      apply id. apply (MP _ (∘(f1 ∧ f2) ∨ ¬∘(f1 ∧ f2))).
      apply (MP _ ¬∘(f1 ∧ f2) → ¬∘(f1 ∧ f2)). apply (MP _ ∘(f1 ∧ f2) → ¬∘(f1 ∧ f2)).
      apply (AxiomInstance _ (Ax8 _ _ _)). assumption. assumption.
      apply (AxiomInstance _ (Ax10 _)).
    + assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ f1 ∧ ¬f1).
      apply (MP _ ¬∘f1). apply (AxiomInstance _ (ci _)). assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ f1).
      apply (MP _ f1 ∧ ¬f1). apply (AxiomInstance _ (Ax4 _ _)). assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ¬f1).
      apply (MP _ f1 ∧ ¬f1). apply (AxiomInstance _ (Ax5 _ _)). assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ∘f2).
      apply (MP _ ∘f2 ∧ f2). apply (AxiomInstance _ (Ax4 _ _)). assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ f2).
      apply (MP _ ∘f2 ∧ f2). apply (AxiomInstance _ (Ax5 _ _)). assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ (f1 ∧ f2)).
      apply (MP _ f2). apply (MP _ f1). apply (AxiomInstance _ (Ax3 _ _)).
      assumption. assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ¬(f1 ∧ f2)).
      apply (MP _ ¬f1 ∨ ¬f2). apply (AxiomInstance _ (negland2 _ _)).
      apply (MP _ ¬f1). apply (AxiomInstance _ (Ax6 _ _)). assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ∘(f1 ∧ f2) → ¬∘(f1 ∧ f2)).
      apply deduction_metatheorem. apply (MP _ ¬(f1 ∧ f2)). apply (MP _ (f1 ∧ f2)).
      apply (MP _ ∘(f1 ∧ f2)). apply (AxiomInstance _ (bc1 _ _)).
      apply Premisse. right. reflexivity. 
      apply (lfi1_monotonicity _( Im (atoms f1 ∪ atoms f2) (kalmar_function v))). split. assumption. 
      left. assumption.
      apply (lfi1_monotonicity _( Im (atoms f1 ∪ atoms f2) (kalmar_function v))). split. assumption. 
      left. assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ¬∘(f1 ∧ f2) → ¬∘(f1 ∧ f2)).
      apply id. apply (MP _ (∘(f1 ∧ f2) ∨ ¬∘(f1 ∧ f2))).
      apply (MP _ ¬∘(f1 ∧ f2) → ¬∘(f1 ∧ f2)). apply (MP _ ∘(f1 ∧ f2) → ¬∘(f1 ∧ f2)).
      apply (AxiomInstance _ (Ax8 _ _ _)). assumption. assumption.
      apply (AxiomInstance _ (Ax10 _)).
    + assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ¬∘f1 ∧ ¬∘f2).
      apply (MP _ ¬∘f2). apply (MP _ ¬∘f1). apply (AxiomInstance _ (Ax3 _ _)).
      assumption. assumption. 
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ¬∘(f1 ∧ f2) ∧ ¬∘(f1 ∨ f2) ∧ ¬∘(f1 → f2)).
      apply (MP _ ¬∘f1 ∧ ¬∘f2). apply T10. assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ¬∘(f1 ∧ f2) ∧ ¬∘(f1 ∨ f2)).
      apply (MP _ ¬∘(f1 ∧ f2) ∧ ¬∘(f1 ∨ f2) ∧ ¬∘(f1 → f2)). apply (AxiomInstance _ (Ax4 _ _)).
      assumption.
      assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ ¬∘(f1 ∧ f2)).
      apply (MP _ ¬∘(f1 ∧ f2) ∧ ¬∘(f1 ∨ f2)). apply (AxiomInstance _ (Ax4 _ _)).
      assumption. assumption.
    + assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ (∘f1 ∧ ¬f1) ∨ (∘f2 ∧ ¬f2)).
      apply (MP _ (∘f2 ∧ ¬f2)). apply (AxiomInstance _ (Ax7 _ _)). assumption.
      apply (MP _ ∘f1 ∧ ¬f1 ∨ ∘f2 ∧ ¬f2). apply T5. assumption.
    + assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ (∘f1 ∧ ¬f1) ∨ (∘f2 ∧ ¬f2)).
      apply (MP _ (∘f2 ∧ ¬f2)). apply (AxiomInstance _ (Ax7 _ _)). assumption.
      apply (MP _ ∘f1 ∧ ¬f1 ∨ ∘f2 ∧ ¬f2). apply T5. assumption.
    + assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ (∘f1 ∧ ¬f1) ∨ (∘f2 ∧ ¬f2)).
      apply (MP _ (∘f1 ∧ ¬f1)). apply (AxiomInstance _ (Ax6 _ _)). assumption.
      apply (MP _ ∘f1 ∧ ¬f1 ∨ ∘f2 ∧ ¬f2). apply T5. assumption.
    + assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ (∘f1 ∧ ¬f1) ∨ (∘f2 ∧ ¬f2)).
      apply (MP _ (∘f1 ∧ ¬f1)). apply (AxiomInstance _ (Ax6 _ _)). assumption.
      apply (MP _ ∘f1 ∧ ¬f1 ∨ ∘f2 ∧ ¬f2). apply T5. assumption.
    + assert (Im (atoms f1 ∪ atoms f2) (kalmar_function v) ⊢ (∘f1 ∧ ¬f1) ∨ (∘f2 ∧ ¬f2)).
      apply (MP _ (∘f1 ∧ ¬f1)). apply (AxiomInstance _ (Ax6 _ _)). assumption.
      apply (MP _ ∘f1 ∧ ¬f1 ∨ ∘f2 ∧ ¬f2). apply T5. assumption.
  
End Kalmar_like.

