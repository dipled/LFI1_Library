From Stdlib Require Import IndefiniteDescription Classical_sets Lia Arith.
Require Import Utils Language.

Theorem strong_lem : forall P : Prop, {P} + {~P}.
Proof.
  intros. assert {x : bool | if x then P else ~P}.
  - apply constructive_indefinite_description.
    pose proof (classic P). destruct H.
    + exists true. apply H.
    + exists false. apply H.
  - destruct H. destruct x.
    + left. apply y.
    + right. apply y.
Qed.

Theorem contraposition : forall A B : Prop, (A -> B) <-> (~B -> ~A).
Proof.
    intros. split.
    - intros. intro. apply H0. apply H. apply H1.
    - intros. pose proof (classic B). destruct H1; try assumption.
      apply H in H1. contradiction.
Qed.

Theorem le_lt_or_eq : forall n m, n <= m -> n < m \/ n = m.
Proof.
  induction 1; auto with arith.
Qed.

Inductive image_set {A B : Type} (f : A -> B) (M: Ensemble A) : Ensemble B :=
image_intro : forall a, a ∈ M -> (f a) ∈ (image_set f M).

Definition function_injective {A B : Type} (f: A -> B): Prop :=
  forall a1 a2, f a1 = f a2 -> a1 = a2.

Definition function_surjective {A B : Type} (f: A -> B): Prop :=
  forall b, exists a, f a = b.

Definition inverse_function {A B : Type} (f : A -> B) (g : B -> A) : Prop :=
  (forall x : A, g (f x) = x) /\ (forall y : B, f (g y) = y).

Record injection (A B: Type): Type := Build_injection {
  inj_f :> A -> B;
  in_inj : function_injective inj_f
}.

Record surjection (A B: Type): Type := Build_surjection {
  sur_f :> A -> B;
  su_surj : function_surjective sur_f
}.

(* Theorem inj_surj_inverse : forall {A B : Type} (f : injection A B), function_surjective (inverse_function f).
Proof.
  intros. destruct f as [f inj_f]. simpl. unfold function_injective in inj_f.
  unfold function_surjective. intros. unfold inverse_function.  *)