Require Import SpecCert.Formalism.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.x86.

Lemma enable_interrupt_inv:
  preserve_inv EnableInterrupt.
Proof.
  unfold preserve_inv.
  unfold inv.
  unfold smramc_inv, smram_code_inv, smrr_inv, cache_clean_inv.
  intros a a' [Hsmramc [Hsmram [Hsmrr Hclean]]] Hpre Hpost.
  unfold x86_postcondition, enable_interrupt_post, enable_interrupt in Hpost.
  rewrite Hpost.
  simpl.
  do 3 (try split); trivial.
Qed.
