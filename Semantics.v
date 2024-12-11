Require Import Arith List ListSet.
From Coq Require Export String.
From LFI1 Require Import Language.

Inductive Matrix_Domain : Set :=
  | One
  | Half
  | Zero.

(* Definition Trivaluation := list (literal * Matrix_Domain). Search list.


Fixpoint lookup_prod (l : list (literal * Matrix_Domain)) (a : literal) : option Matrix_Domain :=
match l with
  | nil => None
  | (x, y) :: t => if x =? a then Some y else lookup_prod t a
end. *)

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


Fixpoint Matrix_Evaluation (v : literal -> Matrix_Domain) (φ : Formula) : Matrix_Domain :=
  match φ with
  | a ∧ b => andM (Matrix_Evaluation v a) (Matrix_Evaluation v b)
  | a ∨ b => orM (Matrix_Evaluation v a) (Matrix_Evaluation v b)
  | a → b => impM (Matrix_Evaluation v a) (Matrix_Evaluation v b)
  | ¬a    => negM (Matrix_Evaluation v a)
  | ∘a    => consM (Matrix_Evaluation v a)
  | #a    => v a
  end.

Definition example_valuation (n : literal) : Matrix_Domain :=
  match n with
  | O => One
  | 1 => Half
  | _ => Zero
  end.

Definition eqmat (a b : Matrix_Domain) : Prop :=
  match a, b with
  | One, One => True
  | Zero, Zero => True
  | Half, Half => True
  | _, _ => False
  end.

Definition formulaSAT (v : literal -> Matrix_Domain) (f : Formula) : Prop := eqmat (Matrix_Evaluation v f) One \/ eqmat (Matrix_Evaluation v f) Half.


Fixpoint formulaSetSAT (v : literal -> Matrix_Domain) (Γ : set Formula) : Prop :=
  match Γ with
  | nil => True
  | h :: t => (formulaSAT v h) /\ (formulaSetSAT v t)
  end.

Definition entails (Γ : set Formula) (f : Formula) : Prop :=
forall (v : literal -> Matrix_Domain), formulaSetSAT v Γ -> formulaSAT v f.

Notation " A |= B " :=
(entails A B) (at level 110, no associativity).

Example teste : forall (Γ : set Formula) (α : Formula), 
  ((¬∘α) :: Γ) |= α ∧ ¬α.
Proof.
  intros. unfold entails. intros. destruct H. unfold formulaSAT.
  right. destruct H.
  - simpl. simpl in H. destruct (Matrix_Evaluation v α).
    -- simpl in H. destruct H.
    -- reflexivity.
    -- simpl in H. destruct H.
  - simpl. simpl in H. destruct (Matrix_Evaluation v α).
    -- simpl in H. destruct H.
    -- reflexivity.
    -- simpl in H. destruct H.
Qed. 

(*
Compute (inconslf Half). *)