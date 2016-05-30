Require Import SpecCert.x86.

Require Import SpecCert.Smm.Delta.Invariant.

Lemma enable_interrupt_inv:
  preserve_inv (software EnableInterrupt).
Proof.
  unfold preserve_inv.
  unfold inv.
  unfold smramc_inv, smram_code_inv, smrr_inv, cache_clean_inv.
  intros a a' [Hsmramc [Hsmram [Hsmrr Hclean]]] Hstep.
  inversion Hstep as [Hpre Hpost].
  unfold enable_interrupt_post in Hpost.
  unfold enable_interrupt in Hpost.
  rewrite Hpost.
  simpl.
  do 3 (try split); trivial.
Qed.
