Require Import SpecCert.Formalism.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.x86.

Lemma open_smram_inv:
  preserve_inv OpenSmram.
Proof.
  unfold preserve_inv.
  unfold inv.
  unfold smramc_inv, smram_code_inv.
  intros a a' Hinv Hpre Hpost.
  unfold open_smram_pre in Hpre.
  unfold smramc_is_locked in Hinv.
  unfold smramc_is_unlocked in Hpre.
  destruct Hinv as [Hsmramc Hsmm].
  unfold smramc_is_ro in Hsmramc.
  unfold smramc_is_rw in Hpre.
  rewrite Hpre in Hsmramc; discriminate Hsmramc.
Qed.