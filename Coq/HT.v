From Coq Require Export String.
Require Export Coq.Unicode.Utf8_core.

Inductive HTProp : Type :=
    |T
    |F
    |NF.


Definition notht (p : HTProp) : HTProp :=
    match p with
    |T => F
    |F => T
    |NF => F
    end.


Definition andht (p q : HTProp) : HTProp :=
    match p, q with
    |F,_ => F
    |_, F => F
    |T, T => T
    |_, _ => NF
    end.


Definition orht (p q : HTProp) : HTProp :=
    match p, q with
    |T, _ => T
    |_, T => T
    |NF, _ => NF
    |_, NF => NF
    |_, _ => F
    end.



Definition impht (p q : HTProp) : HTProp :=
    match p, q with
    |F,_ => T
    |_, T => T
    |NF, F => F
    |NF, _ => T
    |T, F => F
    |T, NF => NF
    end.

Definition bimpht (p q : HTProp) : HTProp :=
  match p, q with
  |F, F => T
  |T, T => T
  |F, _ => F
  |_, F => F
  |NF, T => NF
  |T, NF => NF
  |NF, NF => T
  end.



Notation "x ⇒ y" := (impht x y) (at level 80, right associativity).
Notation "x ⇔ y" := (bimpht x y) (at level 50, left associativity).
Notation "x & y" := (andht x y) (at level 20, left associativity).
Notation "x | y" := (impht x y) (at level 31, left associativity).
Notation " ! x " := (notht x) (at level 10, left associativity).

Theorem bimp_eq : ∀ a b : HTProp,
  (a ⇔ b = T) = ((a ⇒ b) & (b ⇒ a) = T).
Proof.
  intros a b.
  destruct a; destruct b; reflexivity.
Qed.




