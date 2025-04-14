Require Import Epsilon Infinite_sets Utils Language Lia Arith.

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
  forall x : A, g (f x) = x.

Record injection (A B: Type): Type := Build_injection {
  inj_f :> A -> B;
  in_inj : function_injective inj_f
}.

Record surjection (A B: Type): Type := Build_surjection {
  sur_f :> A -> B;
  su_surj : function_surjective sur_f
}.