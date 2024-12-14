From Coq Require Export String.

Theorem iff_neg : forall A B : Prop, (A <-> B) -> (~A <-> ~B).
Proof.
  intros. split; intros; intro; apply H0; apply H; apply H1.
Qed.

Theorem contra : forall A B : Prop, (A -> B) -> (~B -> ~A).
Proof.
  intros. intro. apply H0. apply H. apply H1.
Qed.
