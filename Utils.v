Require Export Arith Infinite_sets.
From Coq Require Export String.

Arguments In {U}.
Arguments Add {U}.
Arguments Empty_set {U}.
Arguments Union {U}.
Arguments Included {U}.
Arguments Finite {U}.
Arguments Singleton {U}.

Notation " a ∈ A " := (In A a) (at level 10).
Notation " B ∪ C " := (Union B C) (at level 63, left associativity).
Notation " [ a ] " := (Singleton a) (at level 0, right associativity).
Notation " A ⊆ B " := (Included A B) (at level 12).
Notation " ∅ "     := (Empty_set).

Theorem iff_neg : forall A B : Prop, (A <-> B) -> (~A <-> ~B).
Proof.
  intros. split; intros; intro; apply H0; apply H; apply H1.
Qed.

Theorem contra : forall A B : Prop, (A -> B) -> (~B -> ~A).
Proof.
  intros. intro. apply H0. apply H. apply H1.
Qed.

Theorem In_lem: forall (U : Type) (A : Ensemble U) (x : U),
  x ∈ A \/ ~ x ∈ A.
Proof.
  intros. unfold In. apply classic.
Qed.