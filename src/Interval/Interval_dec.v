Require Import Coq.Bool.Sumbool.
Require Import Coq.Arith.Compare_dec.
Require Import Omega.

Require Import SpecCert.Interval.Interval_ind.
Require Import SpecCert.Interval.Interval_func.
Require Import SpecCert.Interval.Interval_prop.
Require Import SpecCert.Utils.

Program Definition is_inside_interval_dec
        (x: nat)
        (i: Interval)
  :{ is_inside_interval x i } + { ~ is_inside_interval x i } :=
    let b := lower_bound i in
    let e := upper_bound i in
    (le_dec b x) :&& (le_dec x e).
Next Obligation.
  unfold is_inside_interval.
  omega.
Qed.
Next Obligation.
  unfold is_inside_interval.
  omega.
Qed.

Program Definition is_included_dec
        (i1 i2: Interval)
  : { is_included_in i1 i2 } + { ~ is_included_in i1 i2 } :=
  let b1 := lower_bound i1 in
  let b2 := lower_bound i2 in
  let e2 := upper_bound i2 in
  let e1 := upper_bound i1 in
  (le_dec b2 b1) :&& (le_dec e1 e2).
Next Obligation.
  unfold is_included_in.
  omega.
Qed.
Next Obligation.
  unfold is_included_in.
  omega.
Qed.

Program Definition disjoint_dec
        (i1 i2: Interval)
  : { disjoint i1 i2 } + { ~ disjoint i1 i2 } :=
  let b1 := lower_bound i1 in
  let b2 := lower_bound i2 in
  let e1 := upper_bound i1 in
  let e2 := upper_bound i2 in
  (lt_dec e1 b2) :&& (lt_dec e2 b1).
Next Obligation.
  unfold disjoint.
  omega.
Qed.
Next Obligation.
  unfold disjoint.
  omega.
Qed.