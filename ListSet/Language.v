Require Import Arith List ListSet.
From Coq Require Export String.


Definition Atom := nat.

Inductive Formula : Set :=
  | Lit    : Atom -> Formula
  | Neg    : Formula -> Formula
  | And    : Formula -> Formula -> Formula
  | Or     : Formula -> Formula -> Formula
  | Imp    : Formula -> Formula -> Formula
  | Cons   : Formula -> Formula.

Notation " x → y " := 
(Imp x y) (at level 80, right associativity).

(* Notation " x ↔ y " := 
(bimplf x y) (at level 50, left associativity). *)

Notation " x ∧ y " := 
(And x y) (at level 20, left associativity).

Notation " x ∨ y " := 
(Or x y) (at level 31, left associativity).

Notation " ¬ x " := 
(Neg x) (at level 9, right associativity, format "¬ x").

Notation " ∘ x " := 
(Cons x) (at level 9, right associativity, format "∘ x").

Notation " # x " :=
(Lit x) (at level 2, no associativity, x constr at level 1, format "# x").

Lemma neg_discrim : forall φ : Formula, φ <> ¬φ.
Proof.
  intros. induction φ; try discriminate.
  intro. injection H. intro. apply IHφ. apply H0.
Qed.

Lemma circ_discrim : forall φ : Formula, φ <> ∘φ.
Proof.
  intros. induction φ; try discriminate.
  intro. inversion H. apply IHφ. apply H1.
Qed.

Lemma and_discrim_l : forall φ ψ: Formula, φ <> φ ∧ ψ.
Proof.
  intros. induction φ; try discriminate.
  intro. inversion H. rewrite H2 in H1. apply IHφ1. apply H1.
Qed.

Lemma and_discrim_r : forall φ ψ: Formula, φ <> ψ ∧ φ.
Proof.
  intros. induction φ; try discriminate.
  intro. inversion H. apply IHφ2. apply H2. 
Qed.

Lemma or_discrim_l : forall φ ψ: Formula, φ <> φ ∨ ψ.
Proof.
  intros. induction φ; try discriminate.
  intro. inversion H. rewrite H2 in H1. apply IHφ1. apply H1.
Qed.

Lemma or_discrim_r : forall φ ψ: Formula, φ <> ψ ∨ φ.
Proof.
  intros. induction φ; try discriminate.
  intro. inversion H. apply IHφ2. apply H2. 
Qed.

Lemma to_discrim_l : forall φ ψ: Formula, φ <> (φ → ψ).
Proof.
  intros. induction φ; try discriminate.
  intro. inversion H. rewrite H2 in H1. apply IHφ1. apply H1.
Qed.

Lemma to_discrim_r : forall φ ψ: Formula, φ <> (ψ → φ).
Proof.
  intros. induction φ; try discriminate.
  intro. inversion H. apply IHφ2. apply H2.
Qed.

Theorem eq_formula_dec : forall x y : Formula, {x = y} + {x <> y}.
Proof.
  intro. induction x.
  - intro. induction y; try (right; discriminate).
    pose proof eq_nat_dec a a0. destruct H as [Heq | Hneq]. 
    + left. rewrite Heq. reflexivity.
    + right. intro. inversion H. apply Hneq. apply H1.
  - intro. induction y; try (right; discriminate). destruct IHy.
    + right. intro. rewrite <- e in H. inversion H. apply neg_discrim in H1.
      apply H1.
    + specialize (IHx y). destruct IHx.
      * left. rewrite e. reflexivity.
      * right. intro. inversion H. apply n0. apply H1.
  - intro. induction y; try (right; discriminate). intuition.
    + right. intro. inversion H. rewrite H1 in a. apply (and_discrim_l y1 x2). 
      symmetry. apply a.
    + right. intro. inversion H. rewrite H1 in a. apply (and_discrim_l y1 x2). 
      symmetry. apply a.
    + right. intro. inversion H. rewrite H2 in a. apply (and_discrim_r y2 x1).
      symmetry. apply a.
    + specialize (IHx1 y1). specialize (IHx2 y2). destruct IHx1, IHx2.
       * left. rewrite e. rewrite e0. reflexivity.
       * right. intro. inversion H. apply f. apply H2.
       * right. intro. inversion H. apply f. apply H1.
       * right. intro. inversion H. apply f. apply H1.
  - intro. induction y; try (right; discriminate). intuition.
    + right. intro. inversion H. rewrite H1 in a. apply (or_discrim_l y1 x2). 
      symmetry. apply a.
    + right. intro. inversion H. rewrite H1 in a. apply (or_discrim_l y1 x2). 
      symmetry. apply a.
    + right. intro. inversion H. rewrite H2 in a. apply (or_discrim_r y2 x1). 
      symmetry. apply a.
    + specialize (IHx1 y1). specialize (IHx2 y2). destruct IHx1, IHx2.
      * left. rewrite e. rewrite e0. reflexivity.
      * right. intro. inversion H. apply f. apply H2.
      * right. intro. inversion H. apply f. apply H1.
      * right. intro. inversion H. apply f. apply H1.
  - intro. induction y; try (right; discriminate). intuition.
    + right. intro. inversion H. rewrite H1 in a. apply (to_discrim_l y1 x2). 
      symmetry. apply a.
    + right. intro. inversion H. rewrite H1 in a. apply (to_discrim_l y1 x2). 
      symmetry. apply a.
    + right. intro. inversion H. rewrite H2 in a. apply (to_discrim_r y2 x1). 
      symmetry. apply a.
    + specialize (IHx1 y1). specialize (IHx2 y2). destruct IHx1, IHx2.
      * left. rewrite e. rewrite e0. reflexivity.
      * right. intro. inversion H. apply f. apply H2.
      * right. intro. inversion H. apply f. apply H1.
      * right. intro. inversion H. apply f. apply H1.
  - intro. induction y; try (right; discriminate). intuition.
    + right. intro. rewrite a in H. apply (circ_discrim y). apply H.
    + specialize (IHx y). destruct IHx.
      * left. f_equal. apply e.
      * right. intro. apply f. inversion H. reflexivity.
Qed.

Fixpoint size (f : Formula) : nat :=
 match f with
 | Lit x    => 1
 | Neg a    => 1 + size a
 | And a b  => 1 + size a + size b
 | Or a b   => 1 + size a + size b
 | Imp a b  => 1 + size a + size b
 | Cons a => 2 + size a
 end. 

Fixpoint atoms (f : Formula) : set nat :=
  match f with
  | Lit x    => set_add eq_nat_dec x (empty_set nat)
  | Neg a    => atoms a
  | And a b  => set_union eq_nat_dec (atoms a) (atoms b)
  | Or a b   => set_union eq_nat_dec (atoms a) (atoms b)
  | Imp a b  => set_union eq_nat_dec (atoms a) (atoms b)
  | Cons a => atoms a
  end.