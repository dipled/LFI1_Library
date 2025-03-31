Require Import LFI1.Utils LFI1.Language.
Require Import Arith Constructive_sets.

(* Matrix Semantics: *)

Inductive MatrixDomain : Set :=
  | One
  | Half
  | Zero.

Definition designatedValue (a : MatrixDomain) : Prop :=
  match a with
  | Zero => False
  | _ => True
  end.

Definition andM (a b : MatrixDomain) : MatrixDomain :=
  match a, b with
  | Zero, _  => Zero
  | _, Zero  => Zero
  | One, One => One
  | _, _     => Half
  end.

Definition orM (a b : MatrixDomain) : MatrixDomain :=
  match a, b with
  | One, _     => One
  | _, One     => One
  | Zero, Zero => Zero
  | _, _       => Half
  end.

Definition impM (a b : MatrixDomain) : MatrixDomain :=
  match a, b with
  | Zero, _ => One
  | _, One  => One
  | _, Half => Half

  | _, Zero => Zero
  end.

Definition negM (a : MatrixDomain) : MatrixDomain :=
  match a with
  | One  => Zero
  | Half => Half
  | Zero => One
  end.

Definition consM (a : MatrixDomain) : MatrixDomain :=
  match a with
  | Half => Zero
  | _    => One
  end.

Notation " x →ₘ y " := 
(impM x y) (at level 21, right associativity).

Notation " x ∧ₘ y " := 
(andM x y) (at level 20, left associativity).

Notation " x ∨ₘ y " := 
(orM x y) (at level 22, left associativity).

Notation " ¬ₘ x " := 
(negM x) (at level 9, right associativity, format "¬ₘ x").

Notation " ∘ₘ x " := 
(consM x) (at level 9, right associativity, format "∘ₘ x").

(* Defining the conditions for a function to be a valuation over the matrix,
   i.e., it must be a homomorphism from Formula to MatrixDomain.
*)

Definition preserveAnd (v : Formula -> MatrixDomain) : Prop := 
  forall φ ψ: Formula, (v (φ ∧ ψ)) = (v φ) ∧ₘ (v ψ).

Definition preserveOr (v : Formula -> MatrixDomain) : Prop := 
  forall φ ψ: Formula, (v (φ ∨ ψ)) = (v φ) ∨ₘ (v ψ).

Definition preserveTo (v : Formula -> MatrixDomain) : Prop := 
  forall φ ψ: Formula, (v (φ → ψ)) = (v φ) →ₘ (v ψ).

Definition preserveNeg (v : Formula -> MatrixDomain) : Prop := 
  forall φ: Formula, (v (¬φ)) = ¬ₘ(v φ).

Definition preserveCirc (v : Formula -> MatrixDomain) : Prop := 
  forall φ: Formula, (v (∘φ)) = ∘ₘ(v φ).

Definition valuation (v : Formula -> MatrixDomain) : Prop :=
  preserveOr v /\ preserveTo v /\ preserveAnd v /\ preserveNeg v /\ preserveCirc v.

(* Defining the semantic consequence relation w.r.t matrices *)
Definition matrixEntails (Γ : Ensemble Formula) (φ : Formula) := 
forall v : (Formula -> MatrixDomain),
valuation v -> 
  (forall (ψ: Formula), 
    ψ ∈ Γ -> designatedValue (v ψ)) -> 
      designatedValue (v φ).

Notation " Γ ⊨m φ " := (matrixEntails Γ φ) (at level 50, no associativity).

(* Bivaluation semantics *)

Inductive BivaluationDomain : Set :=
  | Bot
  | Top.

Notation " ⊥ " := Bot.
Notation " ⊤ " := Top.

(* Defining the conditions a given map from Formula to BivaluationDomain must
   follow in order to be a bivaluation (it doesn't have to be a homomorphism)
*)
Definition vAnd (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v (φ ∧ ψ)) = ⊤ <-> (v φ = ⊤) /\ (v ψ = ⊤).

Definition vOr (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v (φ ∨ ψ)) = ⊤ <-> (v φ = ⊤) \/ (v ψ = ⊤).

Definition vImp (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v (φ → ψ)) = ⊤ <-> (v φ = ⊥) \/ (v ψ = ⊤).

Definition vNeg (v : Formula -> BivaluationDomain) : Prop :=
  forall φ : Formula, (v ¬φ) = ⊥ -> v φ = ⊤.

Definition vCon (v : Formula -> BivaluationDomain) : Prop :=
  forall φ : Formula, (v ∘φ) = ⊤ -> (v φ = ⊥) \/ (v ¬φ = ⊥).

Definition vCi (v : Formula -> BivaluationDomain) : Prop :=
  forall φ : Formula, (v ¬∘φ) = ⊤ -> (v φ = ⊤) /\ (v ¬φ = ⊤).

Definition vDne (v : Formula -> BivaluationDomain) : Prop :=
  forall φ : Formula, (v ¬¬φ) = ⊤ <-> v φ = ⊤.

Definition vDmAND (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v ¬(φ ∧ ψ)) = ⊤ <-> (v ¬φ = ⊤) \/ (v ¬ψ = ⊤).

Definition vDmOR (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v ¬(φ ∨ ψ)) = ⊤ <-> (v ¬φ = ⊤) /\ (v ¬ψ = ⊤).

Definition vCip (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v ¬(φ → ψ)) = ⊤ <-> (v φ = ⊤) /\ (v ¬ψ = ⊤).
  
Definition bivaluation (v : Formula -> BivaluationDomain) : Prop :=
  vAnd v /\ vOr v /\ vImp v /\ vNeg v /\ vCon v /\ vCi v /\
  vDne v /\ vDmAND v /\ vDmOR v /\ vCip v.

(* Defining the semantic consequence relation w.r.t bivaluations *)
Definition bivaluationEntails (Γ:Ensemble Formula) (φ : Formula) := 
forall v : (Formula -> BivaluationDomain),
bivaluation v -> 
  (forall (ψ: Formula), 
    ψ ∈ Γ -> (v ψ) = ⊤) -> 
      (v φ) = ⊤.

Notation " Γ ⊨ φ " := (bivaluationEntails Γ φ) (at level 50, no associativity).


(* Proving some useful lemmas regarding bivaluations *)

Lemma bivaluation_lem : forall (v : Formula -> BivaluationDomain) (φ : Formula),
v φ = ⊤ \/ v φ = ⊥.
Proof.
  intros. destruct (v φ).
  - right. reflexivity.
  - left. reflexivity.
Qed.

Lemma bivaluation_dec1 : forall (v : Formula -> BivaluationDomain) (φ : Formula),
v φ = ⊤ <-> ~ v φ = ⊥.
Proof.
  intros. split.
  + intro. destruct (v φ).
    - discriminate H.
    - intro. discriminate H0.
  + intro. destruct (v φ).
    - exfalso. apply H. reflexivity.
    - reflexivity.
Qed.

Lemma bivaluation_dec2 : forall (v : Formula -> BivaluationDomain) (φ : Formula),
v φ = ⊥ <-> ~ v φ = ⊤.
Proof.
    intros. split.
  + intro. destruct (v φ).
    - intro. discriminate H0.
    - discriminate H.
  + intro. destruct (v φ).
    - reflexivity.
    - exfalso. apply H. reflexivity.
Qed.

Definition vAndf (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v (φ ∧ ψ)) = ⊥ <-> (v φ = ⊥) \/ (v ψ = ⊥).

Definition vOrf (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v (φ ∨ ψ)) = ⊥ <-> (v φ = ⊥) /\ (v ψ = ⊥).

Definition vImpf (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v (φ → ψ)) = ⊥ <-> (v φ = ⊤) /\ (v ψ = ⊥).

Definition vNegf (v : Formula -> BivaluationDomain) : Prop :=
  forall φ : Formula, (v φ) = ⊥ -> (v ¬φ) = ⊤.

Definition vConf (v : Formula -> BivaluationDomain) : Prop :=
  forall φ : Formula, (v φ = ⊤) /\ (v ¬φ = ⊤) -> (v ∘φ) = ⊥.

Definition vCif (v : Formula -> BivaluationDomain) : Prop :=
  forall φ : Formula, (v φ = ⊥) \/ (v ¬φ = ⊥) -> (v ¬∘φ) = ⊥.

Definition vDnef (v : Formula -> BivaluationDomain) : Prop :=
  forall φ : Formula, (v ¬¬φ) = ⊥ <-> v φ = ⊥.

Definition vDmANDf (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v ¬(φ ∧ ψ)) = ⊥ <-> (v ¬φ = ⊥) /\ (v ¬ψ = ⊥).

Definition vDmORf (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v ¬(φ ∨ ψ)) = ⊥ <-> (v ¬φ = ⊥) \/ (v ¬ψ = ⊥).

Definition vCipf (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v ¬(φ → ψ)) = ⊥ <-> (v φ = ⊥) \/ (v ¬ψ = ⊥).

Lemma bivaluation_additional : 
forall (v : Formula -> BivaluationDomain),
bivaluation v ->
vAndf v /\ vOrf v /\ vImpf v /\ vNegf v /\ vConf v /\ vCif v /\
  vDnef v /\ vDmANDf v /\ vDmORf v /\ vCipf v.
Proof.
  intros. unfold bivaluation in H. destruct_conjunction H. repeat try split.
  - intros. apply bivaluation_dec2 in H. specialize (L φ ψ). apply iff_neg in L.
    apply L in H. destruct (v φ), (v ψ).
    * left. reflexivity.
    * left. reflexivity.
    * right. reflexivity.
    * exfalso. apply H. split; reflexivity.
  - intros. specialize (L φ ψ). apply bivaluation_dec2. apply iff_neg in L.
    apply L. intro. destruct H0. destruct H. rewrite H in H0. discriminate H0.
    rewrite H in H1. discriminate H1.
  - intros. apply bivaluation_dec2 in H. specialize (L0 φ ψ). apply iff_neg in L0.
    apply L0 in H. destruct (v φ), (v ψ).
    * reflexivity.
    * reflexivity.
    * exfalso. apply H. left. reflexivity.
    * exfalso. apply H. left. reflexivity.
  - intros. apply bivaluation_dec2 in H. specialize (L0 φ ψ). apply iff_neg in L0.
    apply L0 in H. destruct (v φ), (v ψ).
    * reflexivity.
    * exfalso. apply H. right. reflexivity.
    * exfalso. apply H. left. reflexivity.
    * exfalso. apply H. right. reflexivity.
  - intros. destruct H. apply bivaluation_dec2. specialize (L0 φ ψ).
    apply iff_neg in L0. apply L0. intro. destruct H1.
    * rewrite H in H1. discriminate H1.
    * rewrite H0 in H1. discriminate H1.
  - specialize (L1 φ ψ). apply bivaluation_dec2 in H. apply iff_neg in L1.
    apply L1 in H. apply bivaluation_dec1. intro. apply H. left. apply H0.
  - specialize (L1 φ ψ). apply bivaluation_dec2 in H. apply iff_neg in L1.
    apply L1 in H. apply bivaluation_dec2. intro. apply H. right. apply H0.
  - intros. destruct H. apply bivaluation_dec2. specialize (L1 φ ψ).
    apply iff_neg in L1. apply L1. intro. destruct H1.
    * rewrite H in H1. discriminate H1.
    * rewrite H0 in H1. discriminate H1.
  - unfold vNegf. intros. specialize (L2 φ). apply contra in L2. 
    * apply bivaluation_dec1 in L2. apply L2.
    * intro. rewrite H in H0. discriminate H0.
  - unfold vConf. intros. apply bivaluation_dec2. intro.
    apply L3 in H0. destruct H, H0.
    * rewrite H in H0; discriminate H0.
    * rewrite H1 in H0; discriminate.
  - unfold vCif. intros. apply bivaluation_dec2. intro.
    apply L4 in H0. destruct H, H0.
    * rewrite H in H0; discriminate H0.
    * rewrite H in H1; discriminate H1.
  - intros. remember (v φ). destruct b.
    * reflexivity.
    * symmetry in Heqb. apply L5 in Heqb. rewrite H in Heqb. discriminate Heqb.
  - intros. remember (v ¬¬φ). destruct b.
    * reflexivity.
    * symmetry in Heqb. apply (L5 φ) in Heqb. rewrite H in Heqb. discriminate Heqb.
  - apply bivaluation_dec2 in H. specialize (L6 φ ψ). apply iff_neg in L6.
    apply L6 in H. apply bivaluation_dec2. intro. apply H. left. apply H0.
  - apply bivaluation_dec2 in H. specialize (L6 φ ψ). apply iff_neg in L6.
    apply L6 in H. apply bivaluation_dec2. intro. apply H. right. apply H0.
  - intros. destruct H. apply bivaluation_dec2. intro.
    apply L6 in H1. destruct H1.
    * rewrite H in H1; discriminate H1.
    * rewrite H0 in H1; discriminate H1.
  - intros. apply bivaluation_dec2 in H. specialize (L7 φ ψ). apply iff_neg in L7.
    apply L7 in H. destruct (v ¬φ), (v ¬ψ).
    * left. reflexivity.
    * left. reflexivity.
    * right. reflexivity.
    * exfalso. apply H. split; reflexivity.
  - intros. destruct H.
    * apply bivaluation_dec2. intro. apply L7 in H0. destruct H0. rewrite H in H0;
      discriminate H0.
    * apply bivaluation_dec2. intro. apply L7 in H0. destruct H0. rewrite H in H1;
      discriminate H1.
  - intros. apply bivaluation_dec2 in H. specialize (R φ ψ). apply iff_neg in R.
    apply R in H. destruct (v φ), (v ¬ψ).
    * left; reflexivity.
    * left; reflexivity.
    * right; reflexivity.
    * exfalso; apply H; split; reflexivity.
  - intros. destruct H.
    * apply bivaluation_dec2. intro. apply R in H0.
      destruct H0. rewrite H in H0; discriminate H0.
    * apply bivaluation_dec2. intro. apply R in H0.
      destruct H0. rewrite H in H1; discriminate H1.
Qed.