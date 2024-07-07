From Coq Require Export String.


Inductive KProp : Type :=
    |T
    |F
    |U.


Definition notk (p : KProp) : KProp :=
    match p with
    |T => F
    |F => T
    |U => U
    end.


Definition andk (p q : KProp) : KProp :=
    match p, q with
    |F,_ => F
    |_, F => F
    |T, T => T
    |_, _ => U
    end.


Definition ork (p q : KProp) : KProp :=
    match p, q with
    |T, _ => T
    |_, T => T
    |U, _ => U
    |_, U => U
    |_, _ => F
    end.



Definition impk (p q : KProp) : KProp :=
    match p, q with
    |F,_ => T
    |_, T => T
    |U, _ => U
    |T, F => F
    |T, U => U
    end.
