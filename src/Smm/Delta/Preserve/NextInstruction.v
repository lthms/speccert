Require Import SpecCert.Address.
Require Import SpecCert.Cache.
Require Import SpecCert.Interval.
Require Import SpecCert.Memory.
Require Import SpecCert.x86.

Require Import SpecCert.Smm.Software.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Behavior.
Require Import SpecCert.Smm.Delta.Preserve.Architecture.

Lemma nextinstr_smramc_inv:
  forall pa :PhysicalAddress,
    preserve (software (NextInstruction pa)) smramc_inv.
Proof.
  unfold preserve.
  intros pa a a' [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] [Hpre Hpost].
  unfold nextinstr_post in Hpost.
  unfold smramc_inv.
  apply update_proc_changes_only_proc in Hpost as [Hmemc _].
  rewrite <- Hmemc.
  apply Hsmramc.
Qed.

Lemma nextinstr_smram_code_inv:
  forall pa :PhysicalAddress,
    preserve (software (NextInstruction pa)) smram_code_inv.
Proof.
  unfold preserve.
  intros pa a a' [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] [Hpre Hpost].
  unfold nextinstr_post in Hpost.
  unfold smram_code_inv, find_memory_content.
  apply update_proc_changes_only_proc in Hpost as [_ [Hmem _]].
  rewrite <- Hmem.
  apply Hsmram.
Qed.

Lemma nextinstr_smrr_inv:
  forall pa :PhysicalAddress,
    preserve (software (NextInstruction pa)) smrr_inv.
Proof.
  unfold preserve.
  intros pa a a' [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] [Hpre Hpost].
  unfold nextinstr_post in Hpost.
  rewrite Hpost.
  unfold smrr_inv, find_memory_content.
  simpl.
  apply Hsmrr.
Qed.

Lemma nextinstr_cache_clean_inv:
  forall pa :PhysicalAddress,
    preserve (software (NextInstruction pa)) cache_clean_inv.
Proof.
  unfold preserve.
  intros pa a a' [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] [Hpre Hpost].
  unfold nextinstr_post in Hpost.
  rewrite Hpost.
  apply Hclean.
Qed.

Lemma nextinstr_ip_inv:
  forall pa :PhysicalAddress,
    software_preserve (NextInstruction pa) ip_inv.
Proof.
  unfold software_preserve.
  intros pa a a' [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hsmm [Hpre Hpost].
  unfold nextinstr_post in Hpost.
  rewrite Hpost.
  unfold ip_inv.
  intro Hcont.
  apply Hsmm in Hcont.
  simpl in Hcont.
  unfold nextinstr_behavior in Hcont.
  exact Hcont.
Qed.

Lemma nextinstr_smbase_inv:
  forall pa :PhysicalAddress,
    preserve (software (NextInstruction pa)) smbase_inv.
Proof.
  unfold preserve.
  intros pa a a' [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] [Hpre Hpost].
  unfold nextinstr_post in Hpost.
  rewrite Hpost.
  apply Hsmbase.
Qed.

Lemma nextinstr_inv:
  forall pa :PhysicalAddress,
    software_preserve (NextInstruction pa) inv.
Proof.
  unfold software_preserve.
  intros pa a a' Hinv Hsmm Htrans.
  split; [| split; [| split; [| split; [| split]]]].
  * apply (nextinstr_smramc_inv pa a a' Hinv Htrans).
  * apply (nextinstr_smram_code_inv pa a a' Hinv Htrans).
  * apply (nextinstr_smrr_inv pa a a' Hinv Htrans).
  * apply (nextinstr_cache_clean_inv pa a a' Hinv Htrans).
  * apply (nextinstr_ip_inv pa a a' Hinv Hsmm Htrans).
  * apply (nextinstr_smbase_inv pa a a' Hinv Htrans).
Qed.