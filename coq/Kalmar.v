From LFI1 Require Import Utils Language Deduction Semantics.
From LFI1 Require Import Deduction_metatheorem Soundness.
From Stdlib Require Import Arith Constructive_sets Image.
From LFI1 Require Import Cardinality.

Section Kalmar_like.
  Variable v : Formula -> MatrixDomain.
  Variable v_is_valuation : valuation v.

  Definition kalmar_function (α : Formula) :=
  match v α with
  | Zero => ∘α ∧ ¬α
  | One => ∘α ∧ α
  | Half => ¬∘α
  end.

  Variable φ : Formula.
  Check Im.
  Definition Δᵥ := Im

End Kalmar_like.

