Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.Formalism.
Require Import SpecCert.x86.

Lemma disable_interrupt_inv:
  preserve_inv DisableInterrupt.
Proof.
  unfold preserve_inv.
  unfold Invariant.inv.
  unfold smramc_inv, smram_code_inv, smrr_inv, cache_clean_inv.
  intros a a' [Hsmramc [Hsmram [Hsmrr Hclean]]] Hpre Hpost.
  unfold x86_postcondition in Hpost.
  unfold disable_interrupt_post in Hpost.
  unfold disable_interrupt in Hpost.
  rewrite Hpost.
  simpl.
  do 3 (try split); trivial.
Qed.