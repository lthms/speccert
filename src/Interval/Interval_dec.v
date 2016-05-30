Require Import Coq.Bool.Sumbool.
Require Import Coq.Arith.Compare_dec.

Require Import SpecCert.Interval.Interval_ind.
Require Import SpecCert.Interval.Interval_func.
Require Import SpecCert.Interval.Interval_prop.
Require Import SpecCert.Utils.

Definition is_inside_interval_dec (x:nat)(i:Interval)
  :{is_inside_interval x i}+{~is_inside_interval x i}. 
Proof.
  refine (
    let b := lower_bound i in
    let e := upper_bound i in
      decide_dec (sumbool_and _ _ _ _ (le_dec b x) (le_dec x e))
  ); unfold is_inside_interval; intuition.
Defined.

Definition is_included_dec (i1 i2:Interval)
  :{is_included_in i1 i2}+{~is_included_in i1 i2}.
Proof.
  refine (
  let b1 := lower_bound i1 in
  let b2 := lower_bound i2 in
  let e2 := upper_bound i2 in
  let e1 := upper_bound i1 in
    decide_dec (sumbool_and _ _ _ _ (le_dec b2 b1) (le_dec e1 e2))
  ); unfold is_included_in; intuition.
Defined.

Definition disjoint_dec (i1 i2:Interval): {disjoint i1 i2}+{~disjoint i1 i2}.
refine (
  let b1 := lower_bound i1 in
  let b2 := lower_bound i2 in
  let e1 := upper_bound i1 in
  let e2 := upper_bound i2 in
  decide_dec (sumbool_and _ _ _ _ (lt_dec e1 b2) (lt_dec e2 b1))
); unfold disjoint; simpl; intuition.
Defined.
