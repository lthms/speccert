Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Le.
Require Import Coq.Logic.Classical_Prop.

Require Import SpecCert.Interval.Interval_ind.
Require Import SpecCert.Interval.Interval_prop.
Require Import SpecCert.Interval.Interval_func.

Lemma x_in_i1_in_i2: forall i1 i2:Interval, is_included_in i1 i2
  -> forall x, is_inside_interval x i1 -> is_inside_interval x i2.
Proof.
  intros i1 i2 Hinclude x Hinside.
  inversion Hinclude as [Hlower Hupper].
  inversion Hinside as [Hxlow Hxup].
  firstorder.
  + apply le_trans with (m:= lower_bound i1); trivial.
  + apply le_trans with (m:= upper_bound i1); trivial.
Qed.

Lemma x1_in_interval_x2_not_in_interval_x1_neq_x2:
  forall x1 x2, forall i, is_inside_interval x1 i -> ~is_inside_interval x2 i
    -> x1 <> x2.
Proof.
  unfold is_inside_interval.
  intros x1 x2 i Hin Hout.
  destruct Hin as [Hinl Hinu].
  apply not_and_or in Hout.
  destruct Hout as [Houtl|Houtu];
  unfold not; intro Hfalse.
  unfold not in Houtl.
  rewrite Hfalse in Hinl.
  apply Houtl in Hinl.
  trivial.
  unfold not in Houtu.
  rewrite Hfalse in Hinu.
  apply Houtu in Hinu.
  trivial.
Qed.

Lemma x1_not_in_interval_x2_in_interval_x1_neq_x2:
  forall x1 x2, forall i, ~is_inside_interval x1 i -> is_inside_interval x2 i
    -> x1 <> x2.
Proof.
  unfold is_inside_interval.
  intros x1 x2 i Hout Hin.
  destruct Hin as [Hinl Hinu].
  apply not_and_or in Hout.
  destruct Hout as [Houtl|Houtu];
  unfold not; intro Hfalse.
  unfold not in Houtl.
  rewrite <- Hfalse in Hinl.
  apply Houtl in Hinl.
  trivial.
  unfold not in Houtu.
  rewrite <- Hfalse in Hinu.
  apply Houtu in Hinu.
  trivial.
Qed.

(* TODO one day
   works with omega, but not useful
Lemma is_included_not_disjoint: forall i1 i2:Interval, is_included_in i1 i2 -> ¬disjoint i1 i2.
Proof.
  intros i1 i2.
  unfold is_included_in;
  unfold disjoint.
  firstorder.
  apply or_not_and.
  right.
  apply le_not_lt.

Qed.
*)
