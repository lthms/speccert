Notation "'true_dec'" := (left _ _).
Notation "'false_dec'" := (right _ _).
Notation "'decide_dec' x" := (if x then
    true_dec
  else
    false_dec) (at level 42).
