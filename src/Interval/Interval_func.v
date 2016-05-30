Require Import SpecCert.Interval.Interval_ind.

Definition lower_bound (i:Interval) :=
  match i with
  | interval_def b e _ => b
  end.

Definition upper_bound (i:Interval) :=
  match i with
  | interval_def b e _ => e
  end.
