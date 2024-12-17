Require Import Epsilon.
(** Defining countability for inductive types, inspired by
  https://github.com/QinxiangCao/Countable_PaperSubmission
  and
  https://github.com/guodk/A-Comprehensive-Formalization-of-Propositional-Logic-in-Coq

 *)

Definition function_injective {A B : Type} (f: A -> B): Prop :=
  forall a1 a2, f a1 = f a2 -> a1 = a2.

Definition function_surjective {A B : Type} (f: A -> B): Prop :=
  forall b, exists a, f a = b.

Definition inverse_function {A B : Type} (f : A -> B) (g : B -> A) :=
  forall x : A, g (f x) = x.

Record injection (A B: Type): Type := Build_injection {
  inj_f :> A -> B;
  in_inj : function_injective inj_f
}.

Record surjection (A B: Type): Type := Build_surjection {
  sur_f :> A -> B;
  su_surj : function_surjective sur_f
}.

Record bijection (A B: Type): Type := Build_bijection {
  bij_f :> A -> B;
  in_bij : function_injective bij_f;
  su_bij : function_surjective bij_f;
}.

Definition injection_trans {A B C : Type} (f1: injection A B) (f2: injection B C): injection A C.
  apply (Build_injection A C (fun (x : A) => f2 (f1 x))). unfold function_injective. 
  intros. apply (in_inj B C f2) in H. apply (in_inj A B f1) in H. apply H.
Defined.

Definition bijection_injection {A B : Type} (f : bijection A B) : injection A B.
  apply (Build_injection A B f). apply (in_bij A B f).
Defined.

Definition bijection_surjection {A B : Type} (f : bijection A B) : surjection A B.
  apply (Build_surjection A B f). apply (su_bij _ _ f).
Defined.

Definition bijection_sym {A B : Type} (f : bijection A B): bijection B A.
  pose proof (su_bij A B f); unfold function_surjective in H.
  apply (Build_bijection _ _ 
  (
    fun (x : B) => 
        proj1_sig (constructive_indefinite_description _ ((su_bij A B f) x)))
  ).
    - unfold function_injective. intros.
      destruct constructive_indefinite_description in H0.
      destruct constructive_indefinite_description in H0.
      simpl in H0. rewrite <- e, <- e0, H0. reflexivity.
    - unfold function_surjective. intros.
      exists (f b). destruct constructive_indefinite_description.
      simpl. apply (in_bij _ _ f) in e. apply e.
Defined.

(** Defining countable *)

Definition Countable (A: Type): Type := injection A nat.

Definition injection_Countable {A B : Type} (f : injection A B) (CB : Countable B) : 
Countable A :=
  injection_trans f CB.