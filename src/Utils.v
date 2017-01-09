Require Import Coq.Bool.Sumbool.

Notation "'true_dec'" := (left _ _).
Notation "'false_dec'" := (right _ _).
Notation "'decide_dec' x" := (if x then
    true_dec
  else
    false_dec) (at level 42).
Notation "x :&& y" := (decide_dec (sumbool_and _ _ _ _ x y)) (at level 42).
Notation "x :|| y" := (decide_dec (sumbool_or _ _ _ _ x y)) (at level 42).
