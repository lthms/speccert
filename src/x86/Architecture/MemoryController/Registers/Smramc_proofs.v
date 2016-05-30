Require Import SpecCert.x86.Architecture.MemoryController.Registers.Smramc_rec.
Require Import SpecCert.x86.Architecture.MemoryController.Registers.Smramc_func.

Lemma set_d_open_d_open_is_true: forall s s':SmramcRegister, forall h,
  s' = set_d_open s h -> d_open s' = true.
Proof.
  intros s s' h Hset.
  induction s' as [open lock].
  unfold set_d_open in Hset.
  inversion Hset.
  unfold d_open.
  trivial.
Qed.

Lemma set_d_open_d_lock_does_not_change: forall s s':SmramcRegister, forall h,
  s' = set_d_open s h -> d_lock s = d_lock s'.
Proof.
  intros s s' h Hset.
  induction s' as [open lock].
  unfold set_d_open in Hset.
  inversion Hset.
  unfold d_open.
  symmetry; trivial.
Qed.

Lemma unset_d_open_d_open_is_false: forall s s':SmramcRegister, forall h,
  s' = unset_d_open s h -> d_open s' = false.
Proof.
  intros s s' h Hunset.
  induction s' as [open lock].
  unfold unset_d_open in Hunset.
  inversion Hunset.
  unfold d_open.
  trivial.
Qed.

Lemma unset_d_open_d_lock_does_not_change: forall s s':SmramcRegister, forall h,
  s' = unset_d_open s h -> d_lock s = d_lock s'.
Proof.
  intros s s' h Hunset.
  induction s as [open lock].
  induction s' as [open' lock'].
  inversion Hunset.
  unfold d_lock.
  symmetry; trivial.
Qed.

Lemma set_d_lock_d_lock_is_true_d_open_is_false: forall s s':SmramcRegister,
  forall h, s' = set_d_lock s h -> d_lock s' = true /\ d_open s' = false.
Proof.
  intros s s' h Hset.
  induction s' as [open lock].
  unfold set_d_lock in Hset.
  inversion Hset.
  unfold d_open, d_lock.
  split; trivial.
Qed.
