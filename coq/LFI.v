From LFI1 Require Export Utils.

Record Logic : Type := mklogic
{ L : Ensemble Set;
  c : (Ensemble Set) -> Set -> Prop
}.
