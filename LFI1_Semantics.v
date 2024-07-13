From Coq Require Export String.

Inductive TruthValue : Set :=
  | One
  | Half
  | Zero.

Definition andlf (a b : TruthValue) : TruthValue :=
  match a, b with
  | Zero, _  => Zero
  | _, Zero  => Zero
  | One, One => One
  | _, _     => Half
  end.

Definition orlf (a b : TruthValue) : TruthValue :=
  match a, b with
  | One, _     => One
  | _, One     => One
  | Zero, Zero => Zero
  | _, _       => Half
  end.

Definition implf (a b : TruthValue) : TruthValue :=
  match a, b with
  | Zero, _ => One
  | _, One  => One
  | _, Half => Half
  | _, Zero => Zero
  end.

Definition neglf (a : TruthValue) : TruthValue :=
  match a with
  | One  => Zero
  | Half => Half
  | Zero => One
  end.

Definition inconslf (a : TruthValue) : TruthValue :=
  match a with
  | Half => One
  | _    => Zero
  end.

Definition bimplf (a b : TruthValue) : TruthValue := 
andlf (implf a b) (implf b a). 

