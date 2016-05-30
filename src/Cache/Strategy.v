Inductive Strategy :=
| Uncachable
| WriteBack
| SmrrHit.

Definition strat_eq_dec (s s':Strategy): {s = s'}+{s <> s'}.
                                                    repeat decide equality.
Defined.
