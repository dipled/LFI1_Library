Require Import Arith List ListSet.
From Coq Require Export String.
From LFI1 Require Import Language.
Require Import Coq.Program.Equality.

(* Deductive System: Hilbert Calculus *)

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
  | Ax1 φ β      => φ → (β → φ)
  | Ax2 φ β γ    => (φ → (β → γ)) → ((φ → β) → (φ → γ))
  | Ax3 φ β      => φ → (β → (φ ∧ β))
  | Ax4 φ β      => (φ ∧ β) → φ
  | Ax5 φ β      => (φ ∧ β) → β
  | Ax6 φ β      => φ → (φ ∨ β)
  | Ax7 φ β      => β → (φ ∨ β)
  | Ax8 φ β γ    => (φ → γ) → ((β → γ) → ((φ ∨ β) → γ))
  | Ax9 φ β      => (φ → β) ∨ φ
  | Ax10 φ       => φ ∨ ¬φ
  | bc1 φ β      => ∘φ → (φ → (¬φ → β))
  | cf φ         => ¬¬φ → φ
  | ce φ         => φ → ¬¬φ
  | ci φ         => ¬∘φ → (φ ∧ ¬ φ)
  | neglor1 φ β  => ¬(φ ∨ β) → (¬φ ∧ ¬β)
  | neglor2 φ β  => (¬φ ∧ ¬β) → ¬(φ ∨ β)
  | negland1 φ β => ¬(φ ∧ β) → (¬φ ∨ ¬β)
  | negland2 φ β => (¬φ ∨ ¬β) → ¬(φ ∧ β)
  | negto1 φ β   => ¬(φ → β) → (φ ∧ ¬β)
  | negto2 φ β   => (φ ∧ ¬β) → ¬(φ → β)
  end.

Inductive deduction : set Formula -> Formula -> Prop :=
  | Premisse : forall (Γ : set Formula) (φ : Formula), set_In φ Γ -> deduction Γ φ
  | AxiomInstance : forall (Γ : set Formula) (a : Ax), deduction Γ (instantiate a)
  | MP : forall (Γ : set Formula) (φ ψ : Formula), (deduction Γ (φ → ψ)) -> (deduction Γ φ) -> deduction Γ ψ.

Notation " Γ ⊢ φ " := (deduction Γ φ) (at level 110, no associativity).

(* Identity lemma for deduction metatheorem *)

Lemma id : forall (Γ : set Formula) (φ : Formula), Γ ⊢ φ → φ.
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

Theorem deduction_metatheorem : forall (Γ : set Formula) (α β : Formula), (α :: Γ ⊢ β) <-> (Γ ⊢ α → β).
Proof. 
  intros. split.
  - intro. dependent induction H.
    + simpl in H. destruct H.
      * rewrite H. apply id.
      * apply (MP Γ φ (α→φ)).
        -- apply (AxiomInstance Γ (Ax1 φ α)).
        -- apply Premisse. apply H.
    + apply (MP Γ (instantiate a) (α → (instantiate a))).
      * apply (AxiomInstance Γ (Ax1 (instantiate a) α)).
      * apply AxiomInstance.
    +  
    







