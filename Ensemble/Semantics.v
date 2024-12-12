From LFI1 Require Export Language.

(* Semantic System: Matrix *)

Inductive MatrixDomain : Set :=
  | One
  | Half
  | Zero.

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
(impM x y) (at level 80, right associativity).

Notation " x ∧' y " := 
(andM x y) (at level 20, left associativity).

Notation " x ∨' y " := 
(orM x y) (at level 31, left associativity).

Notation " ¬' x " := 
(negM x) (at level 9, right associativity, format "¬' x").

Notation " ∘' x " := 
(consM x) (at level 9, right associativity, format "∘' x").

Fixpoint matrixEvaluation (v : Atom -> MatrixDomain) (φ : Formula) : MatrixDomain :=
  match φ with
  | a ∧ b => (matrixEvaluation v a) ∧' (matrixEvaluation v b)
  | a ∨ b => (matrixEvaluation v a) ∨' (matrixEvaluation v b)
  | a → b => (matrixEvaluation v a) →' (matrixEvaluation v b)
  | ¬a    => ¬'(matrixEvaluation v a)
  | ∘a    => ∘'(matrixEvaluation v a)
  | #a    => v a
  end.

Definition designatedValue (a : MatrixDomain) : Prop :=
  match a with
  | Zero => False
  | _ => True
  end.

Definition matrixFormulaSAT (v : Atom -> MatrixDomain) (φ : Formula) : Prop := 
designatedValue (matrixEvaluation v φ).

Definition matrixEntails (Γ:Ensemble Formula) (φ : Formula) := 
forall v : (Atom -> MatrixDomain),
(forall (ψ: Formula), 
  ψ ∈ Γ -> designatedValue (matrixEvaluation v ψ)) -> 
designatedValue ( matrixEvaluation v φ).

Notation " A ⊨ B " := (matrixEntails A B) (at level 110, no associativity).

Example teste : forall (Γ : Ensemble Formula) (α : Formula), 
 Γ ⊨ ¬ (α ∧ ¬α).
Proof.
  intros. unfold matrixEntails. intros.
  unfold matrixFormulaSAT in *. simpl in *. destruct (matrixEvaluation v α); reflexivity.
Qed.

(* Semantic System: Valuations *)