Require Import SpecCert.x86.
Require Import SpecCert.Smm.Delta.Invariant.

Lemma lock_smramc_inv:
  preserve_inv (software LockSmramc).
Proof.
  unfold preserve_inv.
  unfold inv.
  unfold smramc_inv, smram_code_inv.
  intros a a' Hinv Hstep.
  inversion Hstep as [Hpre Hpost].
  unfold lock_smramc_pre in Hpre.
  unfold smramc_is_locked in Hinv.
  unfold smramc_is_unlocked in Hpre.
  destruct Hinv as [Hsmramc Hsmm].
  unfold smramc_is_ro in Hsmramc.
  unfold smramc_is_rw in Hpre.
  rewrite Hpre in Hsmramc; discriminate Hsmramc.
Qed.
