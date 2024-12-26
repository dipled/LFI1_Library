Require Import Epsilon Infinite_sets Utils Language Lia Arith.

(** Defining countability for inductive types, inspired by
  https://github.com/QinxiangCao/Countable_PaperSubmission
  and
  https://github.com/guodk/A-Comprehensive-Formalization-of-Propositional-Logic-in-Coq

 *)

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

Definition function_bijective {A B} (f: A -> B): Prop :=
  function_injective f /\ function_surjective f.
  
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

Record bijection (A B: Type): Type := Build_bijection {
  bij_f :> A -> B;
  in_bij : function_injective bij_f;
  su_bij : function_surjective bij_f;
}.
(* 
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

Definition inverse_fun {A B : Type} (f : A -> B) (a: A) (y:B) : A :=
  match (strong_lem (exists x, f x = y)) with
  | left l => proj1_sig (constructive_indefinite_description _ l)
  | right _ => a
  end.

Fact injection_funrev : forall {A B : Type} (f : A -> B),
  inhabited A -> function_injective f -> exists g, inverse_function f g.
Proof.
  intros. destruct H as [x]. unfold function_injective in H0.
  exists (inverse_fun f x). unfold inverse_function. intros.
  unfold inverse_fun. destruct (strong_lem (exists x1 : A, f x1 = f x0)).
  - destruct constructive_indefinite_description. simpl. apply H0. apply e0.
  - exfalso. apply n. exists x0. reflexivity.
Qed.

Section CantorBernsteinShroder.

Context {A B : Type}
        (f : A -> B)
        (g : B -> A).

Hypothesis Inj_f : function_injective f.

Hypothesis Inj_g : function_injective g.

Hypothesis Inhabited_B : inhabited B.

Fixpoint Cn (n : nat) : Ensemble A :=
  match n with
  | O => Complement (image_set g (Full_set B))
  | S n' => image_set g (image_set f (Cn n'))
  end.

Let Cset : Ensemble A := fun x => exists n, x ∈ (Cn n).

Let g_rev := 
proj1_sig (constructive_indefinite_description _ (injection_funrev g Inhabited_B Inj_g)).

Let h (a : A) :=
  match (strong_lem (a ∈ Cset)) with
  | left _ => f a
  | right _ => g_rev a
  end.

Lemma cantor_bernstein_shroder : function_bijective h.
Proof.
  assert (inverse_function g g_rev).
  { unfold inverse_function. intros.
    unfold g_rev. destruct constructive_indefinite_description.
    simpl. unfold inverse_function in i. apply i. 
  }
  assert (in_cset : forall x : A, ~ x ∈ Cset -> exists y : B, x = g y).
  { 
    intros. destruct (strong_lem (exists y : B, x = g y)); try assumption.
    exfalso; apply H0. unfold In. unfold Cset. exists 0. simpl.
    unfold In. unfold Complement. intro. destruct H1. 
    apply n. exists a. reflexivity.
  }
  split.
  - unfold function_injective. intros. unfold h in H0.
    destruct (strong_lem (a1 ∈ Cset)), (strong_lem (a2 ∈ Cset)).
    + apply Inj_f; assumption.
    + assert (g (f a1) = a2). 
      { pose proof in_cset _ n. destruct H1 as [y].
        rewrite H1 in H0. rewrite H in H0. rewrite H0. rewrite H1. 
        reflexivity.
      }
      destruct i. exfalso; apply n. unfold In. unfold Cset. exists (S x). simpl. 
      rewrite <- H1. apply image_intro. apply image_intro. apply H2.
    + assert (g (f a2) = a1).
      { 
        destruct (strong_lem (exists y : B, a1 = g y)).
        - destruct e. rewrite H1 in H0. rewrite H in H0. rewrite <- H0.
          rewrite H1. reflexivity.
        - exfalso; apply n. unfold In. unfold Cset. exists 0. simpl.
          unfold In. unfold Complement. intro. destruct H1.
          apply n0. exists a. reflexivity.
      }
      destruct i. exfalso; apply n. unfold In. unfold Cset. exists (S x). simpl.
      rewrite <- H1. repeat apply image_intro. assumption.
    + pose proof in_cset _ n. destruct H1. pose proof in_cset _ n0.
      destruct H2. rewrite H1, H2. rewrite H1, H2 in H0. 
      rewrite H in H0, H0. rewrite H0. reflexivity.
  - unfold function_surjective. intros. destruct (strong_lem (b ∈ (image_set f Cset))).
    + destruct i. unfold h. exists a. destruct strong_lem.
      * reflexivity.
      * contradiction.
    + assert (~(g b) ∈ Cset).
      { 
        intro. destruct H0. destruct x.
        - simpl in H0. unfold In in H0.
          unfold Complement in H0. exfalso; apply H0.
          apply image_intro. apply Full_intro.
        - simpl in H0. destruct (strong_lem (b ∈ (image_set f (Cn x)))).
          + destruct i. apply n. apply image_intro. unfold In.
            unfold Cset. exists x. apply H1.          
          + remember (g b). destruct H0. exfalso; apply n0.
            apply Inj_g in Heqa. rewrite <- Heqa. apply H0.
      }
      exists (g b). unfold h. destruct strong_lem.
      * destruct i. exfalso; apply H0. unfold In. unfold Cset.
        exists x. apply H1.
      * apply H.
Qed.

End CantorBernsteinShroder.

Definition sum_injection {A1 B1 A2 B2} (f1: injection A1 B1) (f2: injection A2 B2): injection (sum A1 A2) (sum B1 B2).
  apply (Build_injection _ _ (fun a => match a with inl x => inl (f1 x) | inr y => inr (f2 y) end)).
  unfold function_injective. intros. destruct a1, a2.
  - inversion H. pose proof (in_inj _ _ f1). unfold function_injective in H0.
    apply H0 in H1. rewrite H1. reflexivity.
  - inversion H.
  - inversion H.
  - inversion H. pose proof (in_inj _ _ f2). unfold function_injective in H0.
    apply H0 in H1. rewrite H1. reflexivity.
Defined.

Definition prod_injection {A1 B1 A2 B2} (f1: injection A1 B1) (f2: injection A2 B2): injection (prod A1 A2) (prod B1 B2).
  apply (Build_injection _ _ (fun m =>
          match m with
          | (m1, m2) => (f1 m1, f2 m2) end )).
  unfold function_injective. intros.
  destruct a1, a2. inversion H. apply (in_inj _ _ f1) in H1.
  apply (in_inj _  _ f2) in H2. rewrite H1, H2. reflexivity.
Defined.

Definition sigT_injection 
(I: Type) (A: I -> Type) (B: Type) (f: forall i: I, injection (A i) B): injection (sigT A) (I * B).
  apply (Build_injection _ _ (fun a => (projT1 a, f (projT1 a) (projT2 a)))).
  unfold function_injective. intros. inversion H. destruct a1,a2. simpl in *.
  subst. apply (in_inj _ _ (f x0)) in H2. congruence.
Defined.

Definition nat2_nat_bijection: bijection (sum nat nat) nat.
  apply (Build_bijection _ _ (fun n => match n with | inl n => n + n | inr n => S (n + n) end)).
  - hnf; intros. destruct a1 eqn:Ha1, a2 eqn:Ha2; try lia; f_equal; lia.
  - hnf; intros. assert (forall n, exists m, n= m + m \/ n = S (m + m)).
    { intros. induction n. eauto. destruct IHn. destruct H.
      - exists x; lia.
      - exists (S x); lia. }
    destruct (H b) as [n []].
    + exists (inl n). auto.
    + exists (inr n); auto.
Defined.

Definition natnat_nat_bijection: bijection (prod nat nat) nat.
  set (fix sum (x : nat) : nat := match x with
       | 0 => 0
       | S x0 => S x0 + sum x0
       end) as f.
  apply (Build_bijection _ _
    (fun n => match n with | (n1, n2) => f (n1+n2) + n1 end)).
  - hnf; intros. destruct a1 as (a11, a12), a2 as (a21, a22).
    assert (forall m1 m2, m1 < m2 -> f m1 + m1 < f m2).
    { intros. remember (m2 - m1 - 1) as d; assert (m2 = (S d) + m1) by lia.
      subst m2. clear. induction d; simpl in *; lia. }
    destruct (Compare_dec.le_lt_dec (a11 + a12) (a21 + a22)).
    + destruct (le_lt_or_eq _ _ l).
      * pose proof H0 _ _ H1. lia.
      * rewrite H1 in *. assert (a11=a21) by lia. subst.
        assert (a12 = a22) by lia. auto.
    + apply H0 in l. lia.
  - hnf; intros. assert ( forall a, exists s, f s <= a < f (S s)).
    { induction a. exists 0. auto. destruct IHa as [s Hs].
      remember (a - f s) as d.
      destruct (PeanoNat.Nat.lt_ge_cases d s).
      + exists s. simpl in *. lia.
      + exists (S s). simpl in *; lia. }
    destruct (H b) as [s Hs].
    remember (b - (f s)) as a1. assert (a1 <= s) by (unfold f in *; lia).
    exists (a1, s-a1). replace (a1 + (s - a1)) with s by lia. 
    lia.
Defined.

Definition Countable (A: Type): Type := injection A nat.

Definition injection_Countable {A B} (R: injection A B) (CB: Countable B): Countable A := injection_trans R CB.

Definition bijection_Countable {A B} (R: bijection A B) (CB: Countable B): Countable A := injection_Countable (bijection_injection R) CB.

Definition sum_Countable {A B} (CA: Countable A) (CB: Countable B): Countable (sum A B) :=
  injection_trans (sum_injection CA CB) (bijection_injection nat2_nat_bijection).

Definition prod_Countable {A B} (CA: Countable A) (CB: Countable B): Countable (prod A B) :=
  injection_trans (prod_injection CA CB) (bijection_injection natnat_nat_bijection).

Definition nCountable_Countable {A: nat -> Type} (CA: forall n, Countable (A n)): Countable (sigT A) :=
  injection_trans (sigT_injection _ _ _ CA) (bijection_injection natnat_nat_bijection).

Definition nat_Countable : Countable nat.
  apply (Build_injection _ _ (fun n => n )).
  hnf; intros. eauto.
Defined.

Ltac solve_Countable :=
  match goal with
  | |- Countable (sum _ _) => apply sum_Countable; solve_Countable
  | |- Countable (prod _ _) => apply prod_Countable; solve_Countable
  | |- Countable (sigT _) => try (apply nCountable_Countable; intro; solve_Countable)
  | |- Countable nat => apply nat_Countable
  | _ => try assumption
  end.

Fixpoint rankF (p : Formula): nat :=
  match p with
  | # _ => 0
  | ¬ x => 1 + rankF x
  | ∘ x => 1 + rankF x
  | x → y => 1 + rankF x + rankF y
  | x ∧ y => 1 + rankF x + rankF y
  | x ∨ y => 1 + rankF x + rankF y
  end.

Lemma rankF_countable : forall n,
  Countable (sig (fun x: Formula => rankF x <= n)).
Proof.
  induction n.
  - apply (@bijection_Countable _ nat); solve_Countable.
    apply bijection_sym.
    apply (Build_bijection _ _ (fun x => exist (fun x => rankF x <= 0) (#x) (le_n 0))).
    + hnf; intros. inversion H; auto.
    + hnf; intros. destruct b. inversion l. destruct x; inversion H0.
      exists a. f_equal. apply proof_irrelevance.
  - set (s := sig (fun x => rankF x <= n)).
    apply (@injection_Countable _ (nat + s + s * s)%type); [| solve_Countable].
    assert (SNeg : forall y m, rankF (¬y) <= S m -> rankF y <= m).
    { intros. simpl in H. lia. }
    assert (SCon : forall y m, rankF (∘y) <= S m -> rankF y <= m).
    { intros. simpl in H. lia. }
    assert (SImpl : forall m a b, rankF (a → b) <= S m -> rankF a <= m).
    { intros. simpl in H. lia. }
    assert (SImpr : forall m a b, rankF (a → b) <= S m -> rankF b <= m).
    { intros. simpl in H. lia. }
    assert (SAndl : forall m a b, rankF (a ∧ b) <= S m -> rankF a <= m).
    { intros. simpl in H. lia. }
    assert (SAndr : forall m a b, rankF (a ∧ b) <= S m -> rankF b <= m).
    { intros. simpl in H. lia. }
    assert (SOrl : forall m a b, rankF (a ∨ b) <= S m -> rankF a <= m).
    { intros. simpl in H. lia. }
    assert (SOrr : forall m a b, rankF (a ∨ b) <= S m -> rankF b <= m).
    { intros. simpl in H. lia. }

    apply (Build_injection _ _ (fun x => match x with
          | exist _ (# p) _ => inl (inl p)
          | exist _ (¬ y) l => inl (inr (exist _ y (SNeg _ _ l) ))
          | exist _ (∘ y) l => inl (inr (exist _ y (SCon _ _ l) ))
          | exist _ (a → b) l => inr
            (exist _ a (SImpl _ _ _ l), exist _ b (SImpr _ _ _ l)) 
          | exist _ (a ∧ b) l => inr
            (exist _ a (SAndl _ _ _ l), exist _ b (SAndr _ _ _ l))
          | exist _ (a ∨ b) l => inr
            (exist _ a (SOrl _ _ _ l), exist _ b (SOrr _ _ _ l)) end)).
    hnf; intros. 
    destruct a1 as [[p1 | y1 | y1 z1 | y1 z1| y1 z1 | y1] ?H];
    destruct a2 as [[p2 | y2 | y2 z2 | y2 z2| y2 z2 | y2] ?H]; try inversion H.
    + f_equal. apply proof_irrelevance.
    + subst. f_equal. apply proof_irrelevance.
    + subst. f_equal. apply proof_irrelevance.
Qed.

Theorem Formula_contable : Countable Formula.
Proof.
  apply (@injection_Countable _ (sigT (fun n => sig (fun x => rankF x <= n)))).
  - apply (Build_injection _ _ 
    (fun x0 => existT (fun n => sig (fun x => rankF x <= n))
       (rankF x0) (exist (fun x => rankF x <= rankF x0) x0 (le_n (rankF x0))))).
    hnf; intros. inversion H. auto.
  - solve_Countable. apply rankF_countable.
Qed.

Lemma bijection_nat_formula : bijection nat Formula.
Proof.
  pose proof @Bernstein_Theorem nat Formula.
  pose proof Formula_contable. destruct X.
  assert (@function_injective nat Formula (fun n => (Var n))).
  { hnf; intros. inversion H0; auto. }
  apply (H _ _ H0 in_inj). constructor. exact (Var 0).
Qed. *)