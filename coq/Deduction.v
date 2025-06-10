From LFI1 Require Import Utils Language.
From Stdlib Require Import Arith Constructive_sets.

(* Hilbert calculus: *)

Inductive Ax : Set :=
  | Ax1      : Formula -> Formula -> Ax
  | Ax2      : Formula -> Formula -> Formula -> Ax
  | Ax3      : Formula -> Formula -> Ax
  | Ax4      : Formula -> Formula -> Ax
  | Ax5      : Formula -> Formula -> Ax
  | Ax6      : Formula -> Formula -> Ax
  | Ax7      : Formula -> Formula -> Ax
  | Ax8      : Formula -> Formula -> Formula -> Ax
  | Ax9      : Formula -> Formula -> Ax
  | Ax10     : Formula -> Ax
  | bc1      : Formula -> Formula -> Ax
  | cf       : Formula -> Ax
  | ce       : Formula -> Ax
  | ci       : Formula -> Ax
  | negland1 : Formula -> Formula -> Ax
  | negland2 : Formula -> Formula -> Ax
  | neglor1  : Formula -> Formula -> Ax
  | neglor2  : Formula -> Formula -> Ax
  | negto1   : Formula -> Formula -> Ax
  | negto2   : Formula -> Formula -> Ax.

Definition instantiate (a : Ax) : Formula :=
  match a with 
  | Ax1 α β      => α → (β → α)
  | Ax2 α β γ    => (α → (β → γ)) → ((α → β) → (α → γ))
  | Ax3 α β      => α → (β → (α ∧ β))
  | Ax4 α β      => (α ∧ β) → α
  | Ax5 α β      => (α ∧ β) → β
  | Ax6 α β      => α → (α ∨ β)
  | Ax7 α β      => β → (α ∨ β)
  | Ax8 α β γ    => (α → γ) → ((β → γ) → ((α ∨ β) → γ))
  | Ax9 α β      => (α → β) ∨ α
  | Ax10 α       => α ∨ ¬α
  | bc1 α β      => ∘α → (α → (¬α → β))
  | cf α         => ¬¬α → α
  | ce α         => α → ¬¬α
  | ci α         => ¬∘α → (α ∧ ¬ α)
  | neglor1 α β  => ¬(α ∨ β) → (¬α ∧ ¬β)
  | neglor2 α β  => (¬α ∧ ¬β) → ¬(α ∨ β)
  | negland1 α β => ¬(α ∧ β) → (¬α ∨ ¬β)
  | negland2 α β => (¬α ∨ ¬β) → ¬(α ∧ β)
  | negto1 α β   => ¬(α → β) → (α ∧ ¬β)
  | negto2 α β   => (α ∧ ¬β) → ¬(α → β)
  end.
  
Inductive deduction : Ensemble Formula -> Formula -> Prop :=
  | Premisse : forall (Γ : Ensemble Formula) (φ : Formula), φ ∈ Γ -> deduction Γ φ
  | AxiomInstance : forall (Γ : Ensemble Formula) (a : Ax), deduction Γ (instantiate a)
  | MP : forall (Γ : Ensemble Formula) (φ ψ : Formula), (deduction Γ (φ → ψ)) -> 
    (deduction Γ φ) -> deduction Γ ψ.

Notation " Γ ⊢ φ " := (deduction Γ φ) (at level 50, no associativity).
