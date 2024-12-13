From LFI1 Require Export Language.

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

Notation " x →' y " := 
(impM x y) (at level 21, right associativity).

Notation " x ∧' y " := 
(andM x y) (at level 20, left associativity).

Notation " x ∨' y " := 
(orM x y) (at level 22, left associativity).

Notation " ¬' x " := 
(negM x) (at level 9, right associativity, format "¬' x").

Notation " ∘' x " := 
(consM x) (at level 9, right associativity, format "∘' x").

(* Defining the conditions for a function to be a valuation over the matrix,
   i.e., it must be a homomorphism from Formula to MatrixDomain.
*)

Definition preserveAnd (v : Formula -> MatrixDomain) : Prop := 
  forall φ ψ: Formula, (v (φ ∧ ψ)) = (v φ) ∧' (v ψ).

Definition preserveOr (v : Formula -> MatrixDomain) : Prop := 
  forall φ ψ: Formula, (v (φ ∨ ψ)) = (v φ) ∨' (v ψ).

Definition preserveTo (v : Formula -> MatrixDomain) : Prop := 
  forall φ ψ: Formula, (v (φ → ψ)) = (v φ) →' (v ψ).

Definition preserveNeg (v : Formula -> MatrixDomain) : Prop := 
  forall φ: Formula, (v (¬φ)) = ¬'(v φ).

Definition preserveCirc (v : Formula -> MatrixDomain) : Prop := 
  forall φ: Formula, (v (∘φ)) = ∘'(v φ).

Definition valuation (v : Formula -> MatrixDomain) : Prop :=
  preserveOr v /\ preserveTo v /\ preserveAnd v /\ preserveNeg v /\ preserveCirc v.
  
Ltac destruct_conjunction H :=
match type of H with
| _ /\ _ => 
  let L := fresh "L" in
  let R := fresh "R" in
  destruct H as [L R]; destruct_conjunction L; destruct_conjunction R
| _ => idtac
end.

(* Defining the semantic consequence relation *)

Definition matrixEntails (Γ:Ensemble Formula) (φ : Formula) := 
forall v : (Formula -> MatrixDomain),
valuation v -> 
  (forall (ψ: Formula), 
    ψ ∈ Γ -> designatedValue (v ψ)) -> 
      designatedValue (v φ).

Notation " Γ ⊨m φ " := (matrixEntails Γ φ) (at level 110, no associativity).

(* Semantic System: Valuations *)

Inductive BivaluationDomain : Set :=
  | Bot
  | Top.

Notation " ⊥ " := Bot.
Notation " ⊤ " := Top.

Definition vAnd (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v (φ ∧ ψ)) = ⊤ <-> (v φ = ⊤) /\ (v ψ = ⊤).

Definition vOr (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v (φ ∨ ψ)) = ⊤ <-> (v φ = ⊤) \/ (v ψ = ⊤).

Definition vImp (v : Formula -> BivaluationDomain) : Prop :=
  forall φ ψ : Formula, (v (φ → ψ)) = ⊤ <-> (v φ = ⊥) /\ (v ψ = ⊤).

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

Definition bivaluationEntails (Γ:Ensemble Formula) (φ : Formula) := 
forall v : (Formula -> BivaluationDomain),
bivaluation v -> 
  (forall (ψ: Formula), 
    ψ ∈ Γ -> (v ψ) = ⊤) -> 
      (v φ) = ⊤.

Notation " Γ ⊨ φ " := (bivaluationEntails Γ φ) (at level 110, no associativity).

