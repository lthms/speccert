Require Import Coq.Logic.Classical_Prop.
Require Import SpecCert.Address.
Require Import SpecCert.Memory.
Require Import SpecCert.Cache.
Require Import SpecCert.Interval.
Require Import SpecCert.Map.
Require Import SpecCert.x86.

Require Import SpecCert.Smm.Software.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Preserve.Architecture.

Lemma dram_neq_interval_1:
  forall i    :Interval,
  forall x x' :Address,
    is_inside_interval (address_offset x) i
    -> ~ is_inside_interval (address_offset x') i
    -> ~ hardware_addr_eq (dram x) (dram x').
Proof.
  intros i x x' Hin Hout Hfalse.
  unfold hardware_addr_eq in Hfalse.
  intuition.
  simpl in H0.
  inversion H0.
  assert (~ addr_eq x x'); [
    intro Hneq;
    apply (x1_not_in_interval_x2_in_interval_x1_neq_x2 _ _ _ Hout Hin);
    symmetry;
    exact H2
     |].
  unfold not in H1.
  apply H1.
  exact H0.
Qed.

Lemma dram_neq_interval_2:
  forall i    :Interval,
  forall x x' :Address,
    is_inside_interval (address_offset x) i
    -> ~ is_inside_interval (address_offset x') i
    -> ~ hardware_addr_eq (dram x') (dram x).
Proof.
  intros i x x' Hin Hout Hfalse.
  apply hardware_addr_eq_sym in Hfalse.
  assert (~ hardware_addr_eq (dram x) (dram x')); [
      eapply dram_neq_interval_1 with i; intuition |].
  intuition.
Qed.

Lemma dram_neq_interval_3:
  forall i    :Interval,
  forall x x' :Address,
    ~ is_inside_interval (address_offset x) i
    -> is_inside_interval (address_offset x') i
    -> ~ hardware_addr_eq (dram x) (dram x').
Proof.
  intros i x x' Hout Hin Hfalse.
  unfold hardware_addr_eq in Hfalse.
  intuition.
  simpl in H0.
  inversion H0.
  assert (~ addr_eq x x'); [
      intro Hneq;
      apply (x1_not_in_interval_x2_in_interval_x1_neq_x2 _ _ _ Hout Hin);
      exact H0
     |].
  unfold not in H1.
  apply H1.
  exact H0.
Qed.

Lemma dram_neq_interval_4:
  forall i    :Interval,
  forall x x' :Address,
    ~ is_inside_interval (address_offset x) i
    -> is_inside_interval (address_offset x') i
    -> ~ hardware_addr_eq (dram x') (dram x).
Proof.
  intros i x x' Hout Hin Hfalse.
  apply hardware_addr_eq_sym in Hfalse.
  assert (~ hardware_addr_eq (dram x) (dram x')); [
      eapply dram_neq_interval_3 with i; intuition |].
  intuition.
Qed.

Lemma write_strat_uc:
  forall pa :PhysicalAddress,
    partial_preserve (software (Write pa))
                     (fun a => resolve_cache_strategy (proc a) pa = Uncachable)
                     inv.
Proof.
  unfold partial_preserve.
  intros pa a a' Hinv Hsmm_strat
         [Hpre Hpost].
  unfold write_post in Hpost.
  rewrite Hsmm_strat in Hpost.
  unfold write_uncachable in Hpost.
  apply (update_memory_content_with_context_preserves_inv a a' pa Hinv Hpost).
Qed.

Lemma write_strat_sh:
  forall pa :PhysicalAddress,
    partial_preserve (software (Write pa))
                     (fun a => resolve_cache_strategy (proc a) pa = SmrrHit)
                     inv.
Proof.
  unfold partial_preserve.
  intros pa a a' Hinv Hsmm_strat
         [Hpre Hpost].
  unfold write_post in Hpost.
  rewrite Hsmm_strat in Hpost.
  unfold write_smrrhit in Hpost.
  rewrite Hpost.
  exact Hinv.
Qed.

Lemma write_strat_smrr_wb:
  forall pa :PhysicalAddress,
    partial_preserve (software (Write pa))
                     (fun a => is_inside_smrr (proc a) pa
                            /\ smm_strategy (smrr (proc a)) = WriteBack)
                     inv.
Proof.
  unfold partial_preserve.
  intros pa a a' Hinv [Hinside_smrr Hsmm_strat]
         [Hpre Hpost].
  unfold write_post, resolve_cache_strategy in Hpost.
  destruct is_inside_smrr_dec; [| intuition ].
  destruct is_in_smm_dec as [Hin_smm|Hnot].
  + rewrite Hsmm_strat in Hpost.
    unfold write_writeback in Hpost.
    assert (is_inside_smram pa -> is_in_smm (proc a)); [
        intro Hin;
        exact Hin_smm |].
    destruct cache_hit_dec.
    * apply (update_cache_content_with_context_preserves_inv a a' pa Hinv H Hpost).
    * remember (load_in_cache_from_memory a pa) as a''.
      assert (inv a'') as Hinv''; [
          apply (load_in_cache_from_memory_preserves_inv a a'' pa Hinv H Heqa'') |].
      assert (proc a = proc a'').
      apply load_in_cache_from_memory_changes_only_mem_and_cache in Heqa'' as [Hproc Hmc].
      rewrite <- Hproc.
      reflexivity.
      assert (is_in_smm (proc a'')).
      rewrite <- H0.
      exact Hin_smm.
      assert (is_inside_smram pa -> is_in_smm (proc a'')); [
        intro Hin;
          exact H1 |].
      rewrite H0 in Hpost.
      eapply (update_cache_content_with_context_preserves_inv a'' a' pa Hinv'' H2 Hpost).
  + unfold write_smrrhit in Hpost.
    rewrite Hpost.
    exact Hinv.
Qed.

Lemma write_not_smrr:
  forall pa :PhysicalAddress,
    partial_preserve (software (Write pa))
                     (fun a => ~ is_inside_smrr (proc a) pa)
                     inv.
Proof.
  unfold partial_preserve.
  intros pa a a' Hinv Hnot_inside_smrr Htrans.
  assert (write_post context pa a a') as Hpost.
  destruct Htrans as [H1 H2]; exact H2.
  remember (resolve_cache_strategy (proc a) pa) as strat.
  unfold write_post in Hpost.
  assert (strat = strategy (proc a)).
  unfold resolve_cache_strategy in Heqstrat.
  destruct is_inside_smrr_dec; [ intuition |].
  exact Heqstrat.
  case_eq (resolve_cache_strategy (proc a) pa); intro Hres; rewrite Hres in Hpost.
  + apply (write_strat_uc pa a a' Hinv Hres Htrans).
  + destruct (is_inside_smrr_dec (proc a) pa); [ intuition |].
    unfold write_writeback in Hpost.
    assert (is_inside_smram pa -> is_in_smm (proc a)).
    intro Hfalse.
    destruct Hinv as [Hsmramc [Hsmram [Hsmrr Hclean]]].
    apply Hsmrr in Hfalse.
    apply n in Hfalse.
    destruct Hfalse.
    destruct (cache_hit_dec (cache a) pa).
    * apply (update_cache_content_with_context_preserves_inv a a' pa Hinv H0 Hpost).
    * apply (load_then_update_cache_with_context_preserves_inv a a' pa Hinv H0 Hpost).
 + apply (write_strat_sh pa a a' Hinv Hres Htrans).
Qed.

Lemma write_inv:
  forall pa :PhysicalAddress,
    preserve (software (Write pa)) inv.
Proof.
  unfold preserve.
  intros pa a a' Hinv Htrans.
  destruct (is_inside_smrr_dec (proc a) pa).
  + case_eq (resolve_cache_strategy (proc a) pa); intro Hres.
    * apply (write_strat_uc pa a a' Hinv Hres Htrans).
    * assert (is_inside_smrr (proc a) pa /\ smm_strategy (smrr (proc a)) = WriteBack).
      split; [ exact i |].
      unfold resolve_cache_strategy in Hres.
      destruct is_inside_smrr_dec; [| intuition ].
      destruct is_in_smm_dec; [| discriminate Hres ].
      exact Hres.
      apply (write_strat_smrr_wb pa a a' Hinv H Htrans).
    * apply (write_strat_sh pa a a' Hinv Hres Htrans).
  + apply (write_not_smrr pa a a' Hinv n Htrans).
Qed.