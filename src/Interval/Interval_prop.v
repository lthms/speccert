Require Import SpecCert.Interval.Interval_ind.
Require Import SpecCert.Interval.Interval_func.

Definition is_inside_interval (x:nat) (i:Interval) := 
  let b := lower_bound i in
  let e := upper_bound i in
    b <= x /\ x <= e.

Definition is_included_in(i1 i2:Interval) :=
  let b1 := lower_bound i1 in
  let b2 := lower_bound i2 in
  let e2 := upper_bound i2 in
  let e1 := upper_bound i1 in
    b2 <= b1 /\ e1 <= e2.

Definition disjoint (i1 i2:Interval) :=
  let b1 := lower_bound i1 in
  let b2 := lower_bound i2 in
  let e2 := upper_bound i2 in
  let e1 := upper_bound i1 in
    e1 < b2 /\ e2 < b1.
