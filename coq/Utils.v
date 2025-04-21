From Stdlib Require Import Arith Constructive_sets.

Arguments In {U}.
Arguments Add {U}.
Arguments Empty_set {U}.
Arguments Union {U}.
Arguments Included {U}.
Arguments Singleton {U}.
Arguments Complement {U}.

Notation " a ∈ A " := (In A a) (at level 10).
Notation " a ∉ A " := (~In A a) (at level 10).
Notation " B ∪ C " := (Union B C) (at level 48, left associativity).
Notation " [ a ] " := (Singleton a) (at level 0, right associativity).
Notation " A ⊆ B " := (Included A B) (at level 71). 
Notation " ∅ "     := (Empty_set).

Theorem iff_neg : forall A B : Prop, (A <-> B) -> (~A <-> ~B).
Proof.
  intros. split; intros; intro; apply H0; apply H; apply H1.
Qed.

Theorem contra : forall A B : Prop, (A -> B) -> (~B -> ~A).
Proof.
  intros. intro. apply H0. apply H. apply H1.
Qed. 

Ltac destruct_conjunction H :=
match type of H with
| _ /\ _ => 
  let L := fresh "L" in
  let R := fresh "R" in
  destruct H as [L R]; destruct_conjunction L; destruct_conjunction R
| _ => idtac
end.
