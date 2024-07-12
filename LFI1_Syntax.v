From Coq Require Export String.

Inductive Formula : Set :=
    | Lit    : nat -> Formula
    | Neg    : Formula -> Formula
    | And    : Formula -> Formula -> Formula
    | Or     : Formula -> Formula -> Formula
    | Imp    : Formula -> Formula -> Formula
    | Incons : Formula -> Formula.

