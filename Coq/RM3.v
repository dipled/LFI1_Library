From Coq Require Export String.


Inductive RM3Prop : Type :=
    |T
    |F
    |U.


Definition notrm3 (p : RM3Prop) : RM3Prop :=
    match p with
    |T => F
    |F => T
    |U => U
    end.


Definition andrm3 (p q : RM3Prop) : RM3Prop :=
    match p, q with
    |F,_ => F
    |_, F => F
    |T, T => T
    |_, _ => U
    end.


Definition orrm3 (p q : RM3Prop) : RM3Prop :=
    match p, q with
    |T, _ => T
    |_, T => T
    |U, _ => U
    |_, U => U
    |_, _ => F
    end.



Definition imprm3 (p q : RM3Prop) : RM3Prop :=
    match p, q with
    |F,_ => T
    |_, T => T
    |U, U => U
    |U, F => F
    |T, F => F
    |T, U => F
    end.



Example weakening_not_valid: 
~(forall a b : RM3Prop, (imprm3 a (imprm3 b a) = T)).
Proof.
    unfold not.
    intro.
    specialize (H U T).
    simpl in H.
    discriminate H.
Qed.