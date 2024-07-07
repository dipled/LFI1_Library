From Coq Require Export String.


Inductive LProp : Type :=
    |T
    |F
    |U.


Definition notl (p : LProp) : LProp :=
    match p with
    |T => F
    |F => T
    |U => U
    end.


Definition andl (p q : LProp) : LProp :=
    match p, q with
    |F,_ => F
    |_, F => F
    |T, T => T
    |_, _ => U
    end.


Definition orl (p q : LProp) : LProp :=
    match p, q with
    |T, _ => T
    |_, T => T
    |U, _ => U
    |_, U => U
    |_, _ => F
    end.



Definition impl (p q : LProp) : LProp :=
    match p, q with
    |F,_ => T
    |_, T => T
    |U, U => T
    |U, F => F
    |T, F => F
    |T, U => U
    end.

Definition ml (p : LProp) : LProp :=
    match p with
    | T => T
    | U => T
    | F => F
    end.

Definition ll (p : LProp) : LProp :=
    match p with
    | T => T
    | U => F
    | F => F
    end.



Definition il (p : LProp) : LProp :=
    match p with
    | T => F
    | U => T
    | F => F
    end.
