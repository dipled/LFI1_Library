From Coq Require Export String.
Require Import Arith List ListSet.
From LFI1 Require Import Language.

Inductive Matrix_Domain : Set :=
  | One
  | Half
  | Zero.

Definition Trivaluation := list (atom * Matrix_Domain). Search list.


Fixpoint lookup_prod (l : list (atom * Matrix_Domain)) (a : atom) : option Matrix_Domain :=
match l with
  | nil => None
  | (x, y) :: t => if x =? a then Some y else lookup_prod t a
end.

Definition andM (a b : Matrix_Domain) : Matrix_Domain :=
  match a, b with
  | Zero, _  => Zero
  | _, Zero  => Zero
  | One, One => One
  | _, _     => Half
  end.

Definition orM (a b : Matrix_Domain) : Matrix_Domain :=
  match a, b with
  | One, _     => One
  | _, One     => One
  | Zero, Zero => Zero
  | _, _       => Half
  end.

Definition impM (a b : Matrix_Domain) : Matrix_Domain :=
  match a, b with
  | Zero, _ => One
  | _, One  => One
  | _, Half => Half

  | _, Zero => Zero
  end.

Definition negM (a : Matrix_Domain) : Matrix_Domain :=
  match a with
  | One  => Zero
  | Half => Half
  | Zero => One
  end.

Definition consM (a : Matrix_Domain) : Matrix_Domain :=
  match a with
  | Half => Zero
  | _    => One
  end.

Definition bimpM (a b : Matrix_Domain) : Matrix_Domain := 
andM (impM a b) (impM b a).


Fixpoint Matrix_Valuation (φ : Formula) (v : Trivaluation) : Matrix_Domain :=
  match φ with
  | a ∧ b => andM (Matrix_Valuation a v) (Matrix_Valuation b v)
  | a ∨ b => orM (Matrix_Valuation a v) (Matrix_Valuation b v)
  | a → b => impM (Matrix_Valuation a v) (Matrix_Valuation b v)
  | ¬a    => negM (Matrix_Valuation a v)
  | ◦a    => consM (Matrix_Valuation a v)
  | #a    => match lookup_prod v a with
              | Some x => x
              | None => Zero
              end
  end.


Fixpoint evenP (n : nat) : Prop :=
  match n with
  | S (S n) => evenP n
  | O => True
  | S O => False
  end.
(* 
Fixpoint formulaSAT (v : nat -> Prop) (f : Formula) : Prop :=
  match f with
  | #x    => v x
  | a ∧ b => (formulaSAT v a) /\ (formulaSAT v b)
  | a ∨ b => (formulaSAT v a) \/ (formulaSAT v b)
  | a → b => ~(formulaSAT v a) \/ (formulaSAT v b)
  | ¬a    => ~(formulaSAT v a) \/ (formulaSAT v a)
  | ◦a    => (formulaSAT v a) 
  end.

Definition theory := set Formula.


Fixpoint theorySAT (v : nat -> Prop) (Γ : theory) : Prop :=
  match Γ with
  | nil => True
  | h :: t => (formulaSAT v h) /\ (theorySAT v t)
  end.

Definition entails (Γ : theory) (f : Formula) : Prop :=
forall (v : nat -> Prop), theorySAT v Γ -> formulaSAT v f.

Notation " A |= B " :=
(entails A B) (at level 110, no associativity).

Example teste : forall (Γ : theory) (A B : Formula), 
  ((∙A) :: Γ) |= A ∧ ¬A.
Proof.
  intros.
  unfold entails. intros. apply H. 
Qed. 

Compute (inconslf Half). *)