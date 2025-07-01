From LFI1 Require Import Utils Language Deduction Semantics.
From LFI1 Require Import Deduction_metatheorem Soundness.
From Stdlib Require Import Arith Constructive_sets Image.
From Coq Require Import Equality.
From LFI1 Require Import Cardinality.

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
  unfold Δᵥ. dependent induction φ.
  - simpl. apply Premisse. apply Im_intro with (#a); reflexivity.
  - unfold kalmar_function in *. remember (v f). unfold valuation in v_is_valuation. destruct_conjunction v_is_valuation. unfold preserveNeg in L2. specialize (L2 f). destruct (v f). simpl in L2. rewrite L2.

End Kalmar_like.

