Require Import Coq.Logic.Classical_Prop.

Require Import SpecCert.Equality.
Require Import SpecCert.Map.
Require Import SpecCert.Address.
Require Import SpecCert.Cache.
Require Import SpecCert.Interval.
Require Import SpecCert.Memory.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.x86.

Lemma pa1_not_in_interval_pa2_in_interval_pa1_neq_pa2
      (pa pa': PhysicalAddress)
      (i:      Interval)
      (not_in: ~ address_offset pa ∈ i)
      (is_in:  address_offset pa' ∈ i)
  : ~ eq pa pa'.
  simpl.
  unfold addr_eq.
  intros [Heq Heq'].
  assert (address_offset pa <> address_offset pa').
  + apply (x1_not_in_interval_x2_in_interval_x1_neq_x2 (address_offset pa) (address_offset pa') i not_in is_in).
  + apply H in Heq.
    exact Heq.
Qed.

Lemma neq_dram_vga_cast
      (pa pa': PhysicalAddress)
  : ~ eq (dram pa) (vga pa').
Proof.
  unfold not.
  simpl.
  unfold addr_eq.
  unfold vga, dram.
  induction pa; induction pa'.
  simpl.
  intros [_H H].
  apply eq_equal in H.
  discriminate H.
Qed.

Lemma hardware_dram_cast
      (pa pa': PhysicalAddress)
      : eq (dram pa) (dram pa') <-> eq pa pa'.
Proof.
  split.
  + intro Heq.
    induction pa; induction pa'; unfold dram in *; unfold addr_eq in *;
      unfold address_offset in *; unfold address_scope in *.
    destruct Heq as [Heq Heq'].
    split.
    * exact Heq.
    * simpl.
      apply mm_singleton.
  + intro Heq.
    induction pa; induction pa'; unfold dram in *; unfold addr_eq in *;
      unfold address_offset in *; unfold address_scope in *.
    destruct Heq as [Heq Heq'].
    split.
    * exact Heq.
    * apply eq_refl.
Qed.

Lemma update_memory_content_with_cache_content_preserves_smram_code_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a
                                 (phys_to_hard a (cache_location_address (cache a) pa))
                                 (find_in_cache_location (cache a) pa)
    -> smram_code_inv a'.
Proof.
  intros a a' pa.
  remember (cache_location_address (cache a) pa) as pa'.
  remember (find_in_cache_location (cache a) pa) as c'.
  remember (phys_to_hard a pa') as ha.
  intros [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Heqa'.
  destruct (is_inside_smram_dec pa') as [Hinside|Houtside].
  + rewrite (cache_location_cache_location (cache a) pa pa') in Heqc'; [
    | apply hardware_ensures_cache_is_well_formed
    | trivial
    ].
    symmetry in Heqc'.
    apply find_in_cache_cache_location in Heqc'; [
      | apply hardware_ensures_cache_is_well_formed ].
    assert (cache_hit (cache a) pa') as Hhit.
    rewrite Heqpa';
      apply cache_hit_cache_location_address;
      apply hardware_ensures_cache_is_well_formed.
    rewrite <- cache_hit_cache_location_cache_find in Heqc'; [
      | trivial
      ].
    unfold cache_clean_inv in *.
    unfold find_cache_content in Hclean.
    rewrite Hclean in Heqc'; try trivial.
    unfold smram_code_inv.
    intros addr Haddr.
    induction c'; [| inversion Heqc' ].
    rewrite Heqa'.
    destruct (eq_dec ha (dram addr)) as [Heq|_H].
    * apply eq_equal in Heq.
      rewrite Heq.
      rewrite update_ha_in_memory_is_ha.
      trivial.
    * rewrite <- (update_ha_in_memory_changes_only_ha a ha (dram addr) smm); [
      | trivial
      ].
      apply Hsmram; trivial.
  + unfold smram_code_inv.
    intros addr Haddr.
    unfold phys_to_hard, translate_physical_address in Heqha.
    destruct (is_inside_smram_dec pa') as [_H|_H']; [ intuition |].
    rewrite Heqha in *.
    rewrite Heqa'.
    assert (~ eq (dram pa') (dram addr)) as Hneqdram.
    * unfold not; intro Hfalse.
      assert (~ eq pa' addr).
      unfold is_inside_smram in *.
      apply hardware_dram_cast in Hfalse.
      apply (pa1_not_in_interval_pa2_in_interval_pa1_neq_pa2 pa' addr smram_space Houtside Haddr).
      apply hardware_dram_cast in Hfalse.
      apply H in Hfalse.
      exact Hfalse.
    * rewrite <- update_ha_in_memory_changes_only_ha.
      apply Hsmram; trivial.
      trivial.
Qed.

Lemma update_memory_content_with_cache_content_preserves_cache_clean_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a
                                 (phys_to_hard a (cache_location_address (cache a) pa))
                                 (find_in_cache_location (cache a) pa)
    -> cache_clean_inv a'.
Proof.
  intros a a' pa.
  remember (cache_location_address (cache a) pa) as pa'.
  remember (find_in_cache_location (cache a) pa) as c'.
  remember (phys_to_hard a pa') as ha'.
  intros [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Heqa'.
  unfold cache_clean_inv.
  unfold find_cache_content.
  apply update_memory_changes_only_memory in Heqa'.
  destruct Heqa' as [Hmc [Hproc Hcache]].
  rewrite <- Hcache.
  apply Hclean.
Qed.

Lemma update_memory_content_with_cache_content_preserves_smrr_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a
                                 (phys_to_hard a (cache_location_address (cache a) pa))
                                 (find_in_cache_location (cache a) pa)
    -> smrr_inv a'.
Proof.
  intros a a' pa.
  remember (cache_location_address (cache a) pa) as pa'.
  remember (find_in_cache_location (cache a) pa) as c'.
  remember (phys_to_hard a pa') as ha'.
  intros [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Heqa'.
  unfold smrr_inv.
  apply update_memory_changes_only_memory in Heqa'.
  destruct Heqa' as [Hmc [Hproc Hcache]].
  rewrite <- Hproc.
  apply Hsmrr.
Qed.

Lemma update_memory_content_with_cache_content_preserves_smramc_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a
                                 (phys_to_hard a (cache_location_address (cache a) pa))
                                 (find_in_cache_location (cache a) pa)
    -> smramc_inv a'.
Proof.
  intros a a' pa.
  remember (cache_location_address (cache a) pa) as pa'.
  remember (find_in_cache_location (cache a) pa) as c'.
  remember (phys_to_hard a pa') as ha'.
  intros [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Heqa'.
  unfold smramc_inv.
  apply update_memory_changes_only_memory in Heqa'.
  destruct Heqa' as [Hmc [Hproc Hcache]].
  rewrite <- Hmc.
  apply Hsmramc.
Qed.

Lemma context_is_preserves:
  forall h h': Architecture Software,
    proc h = proc h'
    -> smm_context h = smm_context h'.
Proof.
  intros h h' Heqp.
  unfold smm_context.
  rewrite Heqp.
  reflexivity.
Qed.

Lemma update_memory_content_with_cache_content_preserves_ip_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a
                                 (phys_to_hard a (cache_location_address (cache a) pa))
                                 (find_in_cache_location (cache a) pa)
    -> ip_inv a'.
Proof.
  intros a a' pa.
  remember (cache_location_address (cache a) pa) as pa'.
  remember (find_in_cache_location (cache a) pa) as c'.
  remember (phys_to_hard a pa') as ha'.
  intros [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Heqa'.
  apply update_memory_changes_only_memory in Heqa'.
  destruct Heqa' as [Hmc [Hproc Hcache]].
  unfold ip_inv in *.
  rewrite <- Hproc.
  rewrite <- (context_is_preserves a a' Hproc).
  apply Hip.
Qed.

Lemma update_memory_content_with_cache_content_preserves_smbase_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a
                                 (phys_to_hard a (cache_location_address (cache a) pa))
                                 (find_in_cache_location (cache a) pa)
    -> smbase_inv a'.
Proof.
  intros a a' pa.
  remember (cache_location_address (cache a) pa) as pa'.
  remember (find_in_cache_location (cache a) pa) as c'.
  remember (phys_to_hard a pa') as ha'.
  intros [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Heqa'.
  apply update_memory_changes_only_memory in Heqa'.
  destruct Heqa' as [Hmc [Hproc Hcache]].
  unfold smbase_inv in *.
  rewrite <- Hproc.
  apply Hsmbase.
Qed.

Lemma update_memory_content_with_cache_content_preserves_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a
                                 (phys_to_hard a (cache_location_address (cache a) pa))
                                 (find_in_cache_location (cache a) pa)
    -> inv a'.
Proof.
  intros a a' pa.
  intros Hinv Heqa'.
  unfold inv.
  split; [| split; [| split; [| split; [| split]]]]; [
      eapply (update_memory_content_with_cache_content_preserves_smramc_inv a a' pa)
    | eapply (update_memory_content_with_cache_content_preserves_smram_code_inv a a' pa)
    | eapply (update_memory_content_with_cache_content_preserves_smrr_inv a a' pa)
    | eapply (update_memory_content_with_cache_content_preserves_cache_clean_inv a a' pa)
    | eapply (update_memory_content_with_cache_content_preserves_ip_inv a a' pa)
    | eapply (update_memory_content_with_cache_content_preserves_smbase_inv a a' pa) ]; trivial.
Qed.

Lemma update_memory_content_with_context_preserves_smram_code_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a (phys_to_hard a pa) (smm_context a)
    -> smram_code_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hclean [Hsmrr [Hip Hsmbase]]]]] Heqa'.
  unfold smram_code_inv.
  intros pa' Hinside'.
  unfold update_memory_content in Heqa'.
  unfold update_in_memory in Heqa'.
  unfold find_memory_content, find_in_memory.
  rewrite Heqa'.
  simpl.
  unfold phys_to_hard, translate_physical_address.
  destruct is_inside_smram_dec as [Hinside|Houtside].
  + destruct can_access_smram_dec.
    * assert (smm_context a = smm).
      unfold can_access_smram in c.
      destruct c as [Hsmm|Hfalse].
      unfold smm_context.
      destruct is_in_smm_dec; try reflexivity.
      unfold is_in_smm in n.
      apply n in Hsmm.
      destruct Hsmm.
      unfold smramc_inv in Hsmramc.
      unfold smramc_is_locked in Hsmramc.
      unfold smramc_is_ro in Hsmramc.
      apply (lock_is_close (smramc (memory_controller a))) in Hsmramc.
      rewrite Hsmramc in Hfalse.
      discriminate.
      rewrite H.
      destruct (eq_dec pa pa').
      apply eq_equal in e.
      rewrite e.
      apply add_1.
      rewrite <- add_2.
      apply Hsmram.
      exact Hinside'.
      intro Hfalse.
      apply hardware_dram_cast in Hfalse.
      apply n in Hfalse.
      exact Hfalse.
    * rewrite <- add_2.
      apply Hsmram.
      exact Hinside'.
      intro H.
      apply eq_sym in H.
      assert (~ eq (dram pa') (vga pa)).
      apply (neq_dram_vga_cast pa' pa).
      apply H0 in H.
      exact H.
  + assert (~ eq pa pa') as Hneqpapa'.
    apply (pa1_not_in_interval_pa2_in_interval_pa1_neq_pa2 pa pa' smram_space Houtside Hinside').
    rewrite <- (add_2 (memory a) (dram pa) (dram pa')); [ apply Hsmram; apply Hinside'|].
    intro Hfalse.
    apply hardware_dram_cast in Hfalse.
    apply Hneqpapa' in Hfalse.
    exact Hfalse.
Qed.

Lemma update_memory_content_with_context_preserves_smramc_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a (phys_to_hard a pa) (smm_context a)
    -> smramc_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Heqa'.
  apply update_memory_changes_only_memory in Heqa' as [Hmc [Hproc Hother]].
  unfold smramc_inv.
  rewrite <- Hmc.
  exact Hsmramc.
Qed.

Lemma update_memory_content_with_context_preserves_smbase_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a (phys_to_hard a pa) (smm_context a)
    -> smbase_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Heqa'.
  apply update_memory_changes_only_memory in Heqa' as [Hmc [Hproc Hother]].
  unfold smbase_inv.
  rewrite <- Hproc.
  exact Hsmbase.
Qed.

Lemma update_memory_content_with_context_preserves_cache_clean_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a (phys_to_hard a pa) (smm_context a)
    -> cache_clean_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean Hip]]]] Heqa'.
  apply update_memory_changes_only_memory in Heqa' as [Hmc [Hproc Hother]].
  unfold cache_clean_inv.
  unfold find_cache_content.
  rewrite <- Hother.
  exact Hclean.
Qed.

Lemma update_memory_content_with_context_preserves_smrr_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a (phys_to_hard a pa) (smm_context a)
    -> smrr_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean Hip]]]] Heqa'.
  apply update_memory_changes_only_memory in Heqa' as [Hmc [Hproc Hother]].
  unfold smrr_inv.
  rewrite <- Hproc.
  exact Hsmrr.
Qed.

Lemma update_memory_content_with_context_preserves_ip_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a (phys_to_hard a pa) (smm_context a)
    -> ip_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Heqa'.
  apply update_memory_changes_only_memory in Heqa' as [Hmc [Hproc Hother]].
  unfold ip_inv.
  rewrite <- Hproc.
  rewrite <- (context_is_preserves a a' Hproc).
  exact Hip.
Qed.

Lemma update_memory_content_with_context_preserves_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a (phys_to_hard a pa) (smm_context a)
    -> inv a'.
Proof.
  intros a a' pa.
  intros Hinv Heqa'.
  unfold inv.
  split; [| split; [| split; [| split; [| split]]]]; [
      eapply (update_memory_content_with_context_preserves_smramc_inv a a' pa)
    | eapply (update_memory_content_with_context_preserves_smram_code_inv a a' pa)
    | eapply (update_memory_content_with_context_preserves_smrr_inv a a' pa)
    | eapply (update_memory_content_with_context_preserves_cache_clean_inv a a' pa)
    | eapply (update_memory_content_with_context_preserves_ip_inv a a' pa)
    | eapply (update_memory_content_with_context_preserves_smbase_inv a a' pa) ]; trivial.
Qed.

Lemma load_in_cache_from_memory_preserves_smram_code_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = load_in_cache_from_memory a pa
    -> smram_code_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Heqa'.
  assert (inv a) as Hinv.
  split; [ exact Hsmramc
         | split; [ exact Hsmram
                  | split ; [ exact Hsmrr
                            | split ; [ exact Hclean
                                      | split; [ exact Hip
                                               | exact Hsmbase ]]]]].
  unfold load_in_cache_from_memory in Heqa'.
  destruct (cache_location_is_dirty_dec (cache a) pa) as [Hdirty|Hndirty].
  + remember (update_memory_content a
                                    (phys_to_hard a (cache_location_address (cache a) pa))
                                    (find_in_cache_location (cache a) pa)) as ax.
    assert (inv ax).
    apply (update_memory_content_with_cache_content_preserves_inv a ax pa); trivial.
    apply update_cache_changes_only_cache in Heqa'.
    destruct Heqa' as [Hproc' [Hmc' Hmem']].
    unfold smram_code_inv, find_memory_content.
    rewrite <- Hmem'.
    destruct H as [Hsmramcx [Hsmramx Hrest]].
    exact Hsmramx.
  + apply update_cache_changes_only_cache in Heqa'.
    destruct Heqa' as [Hproc' [Hmc' Hmem']].
    unfold smram_code_inv, find_memory_content.
    rewrite <- Hmem'.
    exact Hsmram.
Qed.

Lemma load_in_cache_from_memory_preserves_cache_clean_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = load_in_cache_from_memory a pa
    -> cache_clean_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hin_smm Heqa'.
  assert (inv a) as Hinv.
  split; [ exact Hsmramc
         | split; [ exact Hsmram
                  | split ; [ exact Hsmrr
                            | split ; [ exact Hclean
                                      | split; [ exact Hip
                                               | exact Hsmbase ]]]]].
  unfold load_in_cache_from_memory in Heqa'.
  destruct (cache_location_is_dirty_dec (cache a) pa) as [Hdirty|Hndirty].
  + remember (update_memory_content a
                                    (phys_to_hard a (cache_location_address (cache a) pa))
                                    (find_in_cache_location (cache a) pa)) as ax.
    assert (inv ax).
    apply (update_memory_content_with_cache_content_preserves_inv a ax pa); trivial.
    unfold cache_clean_inv, find_cache_content.
    intros pa' Hinside' Hcache_hit.
    remember (find_memory_content a (phys_to_hard a pa)) as c'.
    unfold update_cache_content in Heqa'.
    rewrite Heqa'; simpl.
    unfold global_update_in_cache.
    destruct (cache_hit_dec (cache ax) pa) as [Hcache_hit_pa|Hnot_cache_hit_pa].
    * unfold update_in_cache, find_in_cache.
      destruct (eq_dec pa pa') as [Heqpapa'|Hneqpapa'].
      - apply eq_equal in Heqpapa'.
        rewrite Heqpapa'.
        assert (cache_hit
                  (add_in_map (cache ax) (phys_to_index pa')
                              {| dirty := true; content := c'; tag := pa' |}) pa') as Hcache_hit_add.
        unfold cache_hit.
        rewrite add_1.
        apply eq_refl.
        destruct (cache_hit_dec
                  (add_in_map (cache ax) (phys_to_index pa')
                              {| dirty := true; content := c'; tag := pa' |}) pa');
          [| intuition].
        rewrite add_1.
        simpl.
        rewrite Heqpapa' in Heqc'.
        unfold phys_to_hard, translate_physical_address in Heqc'.
        destruct (is_inside_smram_dec pa') as [Hinside|_H]; [| intuition ].
        assert (is_in_smm (proc a)); [
            rewrite <- Heqpapa' in Hinside;
            apply (Hin_smm Hinside) |].
        destruct (can_access_smram_dec (memory_controller a) (in_smm (proc a))) as [Hcan|Hcannot]; [
          |  unfold can_access_smram in Hcannot;
            intuition ].
        rewrite Hsmram in Heqc'; [| exact Hinside ].
        rewrite Heqc'.
        reflexivity.
      - destruct (eq_dec (phys_to_index pa) (phys_to_index pa')) as [Heqi|Hneqi].
        assert (cache_hit (cache a') pa); [
            rewrite Heqa';
            simpl;
            apply global_update_in_cache_cache_hit |].
        assert (~ cache_hit (cache a') pa'); [
            apply (cache_hit_same_index_cache_miss (cache a') pa); trivial
          | intuition ].
        assert (cache_hit
                  (add_in_map (cache ax) (phys_to_index pa)
                              {| dirty := true; content := c'; tag := pa |}) pa').
        unfold cache_hit.
        rewrite <- add_2; [| exact Hneqi ].
        rewrite Heqa' in Hcache_hit.
        simpl in Hcache_hit.
        unfold cache_hit, global_update_in_cache in Hcache_hit.
        destruct (cache_hit_dec (cache ax) pa) as [Hcache_hit_x_pa|Hncache_hit_x_pa].
        unfold update_in_cache in Hcache_hit.
        rewrite <- add_2 in Hcache_hit; [| exact Hneqi ].
        exact Hcache_hit.
        apply Hncache_hit_x_pa in Hcache_hit_pa.
        destruct Hcache_hit_pa.
        destruct (cache_hit_dec
                    (add_in_map (cache ax) (phys_to_index pa)
                                {| dirty := true; content := c'; tag := pa |}) pa') as [Hcache_add|Hncache_add].
        rewrite <- add_2.
        unfold cache_clean_inv in Hclean.
        destruct H as [Hsmramcx [Hsmramx [Hsmrrx [Hcleanx Hipx]]]].
        assert (cache_hit (cache ax) pa') as Hcache_hit_x_pa'; [
            apply (cache_hit_is_preserve_by_non_conflicted_update (cache ax)
                                                                  (cache a')
                                                                  pa
                                                                  pa'
                                                                  c'); [
            exact Hneqi |
            rewrite Heqa'; simpl; reflexivity |
            exact Hcache_hit ] |].
        assert (find_cache_content ax pa' = Some (content (find_in_map (cache ax) (phys_to_index pa')))) as Hfind.
        unfold find_cache_content, find_in_cache.
        destruct (cache_hit_dec (cache ax) pa') as [_H|_H]; [ reflexivity | intuition ].
        rewrite <- Hfind.
        apply (Hcleanx pa' Hinside' Hcache_hit_x_pa').
        exact Hneqi.
        apply Hncache_add in H0.
        destruct H0.
    * destruct (eq_dec (phys_to_index pa) (phys_to_index pa')) as [Heqi|Hneqi].
      - assert (cache a'=global_update_in_cache (cache ax) pa c') as Heqcache'; [
          rewrite Heqa';
          simpl;
          reflexivity |].
        assert (cache_hit (global_update_in_cache (cache ax) pa c') pa); [
            apply (global_update_in_cache_cache_hit (cache ax) pa) |].
        rewrite <- Heqcache' in H0.
        destruct (eq_dec pa pa') as [Heq|Hneq].
        (* case addr_eq *)
        apply eq_equal in Heq.
        rewrite Heq in Heqc'.
        unfold smram_code_inv in Hsmram.
        assert (is_inside_smram pa'); try exact Hinside'.
        rewrite <- Heq in Hinside'.
        apply Hin_smm in Hinside'.
        unfold is_in_smm in Hinside'.
        unfold phys_to_hard, translate_physical_address in Heqc'.
        rewrite <- Heq in Heqc'.
        destruct (is_inside_smram_dec pa).
        rewrite Hinside' in Heqc'.
        destruct (can_access_smram_dec (memory_controller a) true).
        rewrite Hsmram in Heqc'; try trivial.
        rewrite Heqc'.
        unfold find_in_cache, load_in_cache.
        rewrite <- Heq.
        destruct cache_hit_dec.
        rewrite add_1.
        simpl.
        reflexivity.
        unfold cache_hit in n.
        rewrite add_1 in n.
        simpl in n.
        unfold not in n.
        assert (eq pa pa) by (apply eq_refl).
        apply n in H2.
        destruct H2.
        unfold can_access_smram in n.
        apply not_or_and in n.
        destruct n as [G1 G2].
        intuition.
        rewrite <- Heq in H1.
        intuition.
        (* case ~ addr_eq *)
        apply (global_update_not_cache_hit (cache ax) (cache a') pa pa' c') in Heqcache'; try intuition.
      - unfold find_in_cache, load_in_cache.
        destruct cache_hit_dec.
        rewrite <- add_2.
        destruct H as [Hsmramcx [Hsmramx [Hsmrrx [Hcleanx Hipx]]]].
        assert (cache_hit (cache ax) pa') as Hcache_hit_before; [
            apply (cache_hit_is_preserve_by_non_conflicted_update (cache ax)
                                                                  (cache a')
                                                                  pa
                                                                  pa'
                                                                  c'); [
              exact Hneqi
            | rewrite Heqa'; reflexivity
            | exact Hcache_hit ] |].
        unfold cache_clean_inv in Hcleanx.
        assert ((if cache_hit_dec (cache ax) pa'
                 then Some (content (find_in_map (cache ax) (phys_to_index pa')))
                 else None) = Some smm).
        apply (Hcleanx _ Hinside' Hcache_hit_before).
        destruct cache_hit_dec; [ | intuition ].
        rewrite H.
        reflexivity.
        exact Hneqi.
        destruct H as [Hsmramcx [Hsmramx [Hsmrrx Hcleanx]]].
        assert (cache_hit (cache ax) pa') as Hcache_hit_before; [
            apply (cache_hit_is_preserve_by_non_conflicted_update (cache ax) (cache a') pa pa' c'); [
              exact Hneqi
            | rewrite Heqa'; reflexivity
            | exact Hcache_hit ] |].
        exfalso.
        apply n.
        unfold cache_hit.
        rewrite <- add_2.
        exact Hcache_hit_before.
        exact Hneqi.
  + unfold cache_clean_inv.
    intros pa' Hinside' Hcache_hit'.
    remember (find_memory_content a (phys_to_hard a pa)) as c.
    unfold phys_to_hard, translate_physical_address in Heqc.
    destruct is_inside_smram_dec.
    * assert (is_in_smm (proc a)).
      apply Hin_smm.
      exact i.
      assert (can_access_smram (memory_controller a) (in_smm (proc a))).
      unfold can_access_smram.
      left.
      exact H.
      destruct can_access_smram_dec; [| intuition ].
      rewrite Hsmram in Heqc ; [| exact i ].
      rewrite Heqc in Heqa'.
      unfold update_cache_content in Heqa'.
      remember (global_update_in_cache (cache a) pa smm) as cache'.
      unfold global_update_in_cache in Heqcache'.
      destruct (cache_hit_dec (cache a) pa).
      rewrite Heqa'; rewrite Heqcache'.
      unfold find_cache_content, find_in_cache, update_cache_content, update_in_cache.
      simpl.
      destruct (eq_dec pa pa') as [eq|neq].
      apply eq_equal in eq.
      rewrite eq.
      assert (cache_hit
                (add_in_map (cache a) (phys_to_index pa')
                                      {| dirty := true; content := smm; tag := pa' |}) pa').
      unfold cache_hit.
      rewrite add_1.
      apply eq_refl.
      destruct cache_hit_dec; [| intuition ].
      rewrite add_1; reflexivity.
      remember (add_in_map (cache a)
                                     (phys_to_index pa)
                                     {| dirty := true; content := smm; tag := pa |}) as cachex.
      assert (cachex = cache'); [ rewrite Heqcache';
                                  rewrite Heqcachex;
                                  reflexivity |].
      rewrite H1 in *.
      assert (cache' = cache a').
      rewrite Heqa'; rewrite Heqcache'; reflexivity.
      rewrite H2.
      destruct (cache_hit_dec (cache a') pa') as [Hcache_hit_pa'|_H]; [| try intuition ].
      destruct (eq_dec (phys_to_index pa) (phys_to_index pa')) as [Heqi|Hneqi].
      assert (~ cache_hit (cache a') pa'); [| try intuition ].
      rewrite Heqa'.
      rewrite Heqcache'.
      simpl.
      unfold cache_hit, update_in_cache.
      apply eq_equal in Heqi.
      rewrite <- Heqi.
      rewrite add_1.
      intro Hnot.
      apply eq_sym in Hnot.
      apply neq in Hnot.
      exact Hnot.
      rewrite Heqa'.
      rewrite Heqcache'.
      simpl.
      unfold cache_hit, update_in_cache.
      rewrite <- add_2 with (k:=phys_to_index pa)
                            (v:={| dirty := true; content := smm; tag := pa |}); [
        | exact Hneqi].
      unfold cache_clean_inv in Hclean.
      assert (cache_hit (cache a) pa').
      (**********************)
      rewrite <- H2 in Hcache_hit_pa'.
      rewrite Heqcache' in Hcache_hit_pa'.
      unfold update_in_cache in Hcache_hit_pa'.
      unfold cache_hit in Hcache_hit_pa'.
      rewrite <- add_2 in Hcache_hit_pa'; [| exact Hneqi ].
      exact Hcache_hit_pa'.
      (**********************)
      assert (find_cache_content a pa' = Some (content (find_in_map (cache a) (phys_to_index pa')))).
      unfold find_cache_content.
      unfold find_in_cache.
      destruct (cache_hit_dec (cache a) pa') as [_H|_H]; [ | try intuition ].
      reflexivity.
      rewrite <- H4.
      rewrite Hclean; [
          reflexivity
        | exact Hinside'
        | exact H3 ].
      rewrite Heqa'; rewrite Heqcache'.
      unfold find_cache_content, find_in_cache, load_in_cache, update_in_cache.
      destruct (eq_dec pa pa') as [Heq|Hneq].
      apply eq_equal in Heq.
      rewrite Heq.
      assert (cache_hit
                (add_in_map (cache a) (phys_to_index pa')
                                      {| dirty := false; content := smm; tag := pa' |}) pa').
      unfold cache_hit.
      rewrite add_1.
      apply eq_refl.
      destruct cache_hit_dec; [| intuition ].
      simpl.
      rewrite add_1; reflexivity.
      remember (add_in_map (cache a)
                                     (phys_to_index pa)
                                     {| dirty := false; content := smm; tag := pa |}) as cachex.
      assert (cachex = cache'); [ rewrite Heqcache';
                                  rewrite Heqcachex;
                                  reflexivity |].
      rewrite H1 in *.
      assert (cache' = cache a').
      rewrite Heqa'; rewrite Heqcache'; reflexivity.
      rewrite H2.
      destruct (cache_hit_dec (cache a') pa') as [Hcache_hit_pa'|_H]; [| try intuition ].
      destruct (eq_dec (phys_to_index pa) (phys_to_index pa')) as [Heqi|Hneqi].
      assert (~ cache_hit (cache a') pa').
      rewrite Heqa'.
      rewrite Heqcache'.
      simpl.
      unfold cache_hit, load_in_cache.
      apply eq_equal in Heqi.
      rewrite <- Heqi.
      rewrite add_1.
      intro Hnot.
      apply eq_sym in Hnot.
      apply Hneq in Hnot.
      exact Hnot.
      simpl.
      destruct (cache_hit_dec (cache a') pa') as [_H|_H]; intuition.
      simpl.
      destruct (cache_hit_dec (cache a') pa') as [_H|_H]; intuition.
      rewrite  Heqa'.
      rewrite Heqcachex.
      simpl.
      rewrite <- add_2 with (k:=phys_to_index pa)
                            (v:={| dirty := false; content := smm; tag := pa |}); [
        | exact Hneqi ].
      unfold cache_clean_inv in Hclean.
      assert (cache_hit (cache a) pa') as Hcache_hit_in_a_pa'.
      (**********************)
      rewrite <- H2 in Hcache_hit_pa'.
      rewrite Heqcache' in Hcache_hit_pa'.
      unfold load_in_cache in Hcache_hit_pa'.
      unfold cache_hit in Hcache_hit_pa'.
      rewrite <- add_2 in Hcache_hit_pa'; [| exact Hneqi ].
      exact Hcache_hit_pa'.
      (**********************)
      assert (find_cache_content a pa' = Some (content (find_in_map (cache a) (phys_to_index pa')))) as Hfind.
      unfold find_cache_content.
      unfold find_in_cache.
      destruct (cache_hit_dec (cache a) pa'); [ | try intuition ].
      reflexivity.
      rewrite <- Hfind.
      rewrite Hclean; [
          reflexivity
        | exact Hinside'
        | exact Hcache_hit_in_a_pa' ].
    * assert (~ eq pa pa'); [
        apply or_not_and;
        left;
        apply (x1_not_in_interval_x2_in_interval_x1_neq_x2 _ _ _ n Hinside') |].
      destruct (eq_dec (phys_to_index pa) (phys_to_index pa')) as [Heqi|Hneqi].
      - assert (~ cache_hit (cache a') pa') as Hncache_hit_pa'; [| intuition ].
        rewrite Heqa'.
        unfold update_cache_content, cache_hit, global_update_in_cache; simpl.
        destruct (cache_hit_dec (cache a) pa).
        unfold update_in_cache.
        apply eq_equal in Heqi.
        rewrite <- Heqi.
        rewrite add_1.
        simpl.
        intro Hnot.
        apply addr_eq_sym in Hnot.
        apply H in Hnot.
        exact Hnot.
        unfold load_in_cache.
        apply eq_equal in Heqi.
        rewrite <- Heqi.
        rewrite add_1.
        simpl.
        intro Hnot.
        apply addr_eq_sym in Hnot.
        apply H in Hnot.
        exact Hnot.
      - assert (cache_hit (cache a) pa').
        rewrite Heqa' in Hcache_hit'.
        unfold cache_hit, update_cache_content in Hcache_hit'.
        simpl in Hcache_hit'.
        unfold global_update_in_cache in Hcache_hit'.
        destruct (cache_hit_dec (cache a) pa) as [_H|_H]; [
            unfold update_in_cache in Hcache_hit';
            rewrite <- add_2 in Hcache_hit'; [| exact Hneqi ];
            exact Hcache_hit' |
            unfold load_in_cache in Hcache_hit' ;
              rewrite <- add_2 in Hcache_hit'; [| exact Hneqi ] ;
              exact Hcache_hit' ].
        assert (find_cache_content a' pa' = find_cache_content a pa').
        unfold find_cache_content.
        unfold find_in_cache.
        do 2 (destruct cache_hit_dec; [| intuition ]).
        rewrite Heqa'.
        unfold update_cache_content, global_update_in_cache, load_in_cache, update_in_cache; simpl.
        destruct cache_hit_dec;
          (rewrite <- add_2; [ reflexivity | exact Hneqi ]).
        rewrite H1.
        rewrite Hclean; [
            reflexivity
          | exact Hinside'
          | exact H0 ].
Qed.

Lemma load_in_cache_from_memory_preserves_smrr_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = load_in_cache_from_memory a pa
    -> smrr_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hin_smm Heqa'.
  apply load_in_cache_from_memory_changes_only_mem_and_cache in Heqa' as [Hproc Hother].
  unfold smrr_inv.
  rewrite <- Hproc.
  exact Hsmrr.
Qed.

Lemma load_in_cache_from_memory_preserves_smramc_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = load_in_cache_from_memory a pa
    -> smramc_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hin_smm Heqa'.
  apply load_in_cache_from_memory_changes_only_mem_and_cache in Heqa' as [Hproc Hother].
  unfold smramc_inv.
  rewrite <- Hother.
  exact Hsmramc.
Qed.

Lemma load_in_cache_from_memory_preserves_smbase_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = load_in_cache_from_memory a pa
    -> smbase_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hin_smm Heqa'.
  apply load_in_cache_from_memory_changes_only_mem_and_cache in Heqa' as [Hproc Hother].
  unfold smbase_inv.
  rewrite <- Hproc.
  exact Hsmbase.
Qed.

Lemma load_in_cache_from_memory_preserves_ip_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = load_in_cache_from_memory a pa
    -> ip_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hin_smm Heqa'.
  apply load_in_cache_from_memory_changes_only_mem_and_cache in Heqa' as [Hproc Hother].
  unfold ip_inv.
  rewrite <- Hproc.
  rewrite <- (context_is_preserves a a' Hproc).
  exact Hip.
Qed.

Lemma load_in_cache_from_memory_preserves_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = load_in_cache_from_memory a pa
    -> inv a'.
Proof.
  intros a a' pa.
  intros Hinv Hsmm Heqa'.
  unfold inv.
  split; [| split; [| split; [| split; [| split]]]]; [
      eapply (load_in_cache_from_memory_preserves_smramc_inv a a' pa)
    | eapply (load_in_cache_from_memory_preserves_smram_code_inv a a' pa)
    | eapply (load_in_cache_from_memory_preserves_smrr_inv a a' pa)
    | eapply (load_in_cache_from_memory_preserves_cache_clean_inv a a' pa)
    | eapply (load_in_cache_from_memory_preserves_ip_inv a a' pa)
    | eapply (load_in_cache_from_memory_preserves_smbase_inv a a' pa) ]; trivial.
Qed.

Lemma update_cache_content_with_context_preserves_smramc_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = update_cache_content a pa (smm_context a)
    -> smramc_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hin_smm Heqa'.
  apply update_cache_changes_only_cache in Heqa' as [Hproc [Hmc Hother]].
  unfold smramc_inv.
  rewrite <- Hmc.
  exact Hsmramc.
Qed.

Lemma update_cache_content_with_context_preserves_smrr_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = update_cache_content a pa (smm_context a)
    -> smrr_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean Hsmbase]]]] Hin_smm Heqa'.
  apply update_cache_changes_only_cache in Heqa' as [Hproc [Hmc Hother]].
  unfold smrr_inv.
  rewrite <- Hproc.
  exact Hsmrr.
Qed.

Lemma update_cache_content_with_context_preserves_smram_code_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = update_cache_content a pa (smm_context a)
    -> smram_code_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hin_smm Heqa'.
  apply update_cache_changes_only_cache in Heqa' as [Hproc [Hmc Hmem]].
  unfold smram_code_inv.
  unfold find_memory_content.
  rewrite <- Hmem.
  exact Hsmram.
Qed.

Lemma update_cache_content_with_context_preserves_ip_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = update_cache_content a pa (smm_context a)
    -> ip_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hin_smm Heqa'.
  apply update_cache_changes_only_cache in Heqa' as [Hproc [Hmc Hmem]].
  unfold ip_inv.
  rewrite <- Hproc.
  rewrite <- (context_is_preserves a a' Hproc).
  exact Hip.
Qed.

Lemma update_cache_content_with_context_preserves_smbase_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = update_cache_content a pa (smm_context a)
    -> smbase_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hin_smm Heqa'.
  apply update_cache_changes_only_cache in Heqa' as [Hproc [Hmc Hmem]].
  unfold smbase_inv.
  rewrite <- Hproc.
  exact Hsmbase.
Qed.

Lemma update_cache_content_with_context_preserves_cache_clean_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = update_cache_content a pa (smm_context a)
    -> cache_clean_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hin_smm Heqa'.
  unfold cache_clean_inv.
  intros pa' Hinside' Hcache_hit'.
  unfold update_cache_content in Heqa'.
  unfold global_update_in_cache in Heqa'.
  destruct (cache_hit_dec (cache a) pa).
  + unfold update_in_cache in Heqa'.
    unfold find_cache_content.
    unfold find_in_cache.
    destruct cache_hit_dec; [| intuition ].
    rewrite Heqa'; simpl.
    destruct (eq_dec pa pa') as [Heq|Hneq].
    * apply eq_equal in Heq.
      rewrite <- Heq.
      rewrite add_1.
      simpl.
      rewrite <- Heq in Hinside'.
      apply Hin_smm in Hinside'.
      unfold smm_context.
      destruct is_in_smm_dec.
      reflexivity.
      apply n in Hinside'.
      destruct Hinside'.
    * destruct (eq_dec (phys_to_index pa) (phys_to_index pa')) as [Heqi|Hneqi].
      - assert (~ cache_hit (cache a') pa'); [| intuition ].
        assert (cache_hit (cache a') pa) as Hcache_hit_pa.
        unfold cache_hit.
        rewrite Heqa'.
        simpl.
        rewrite add_1.
        simpl.
        apply addr_eq_refl.
        apply (cache_hit_same_index_cache_miss (cache a') pa pa' Hcache_hit_pa Hneq Heqi).
      - rewrite <- add_2; [| exact Hneqi ].
        assert (cache_hit (cache a) pa').
        apply (cache_hit_is_preserve_by_non_conflicted_update (cache a)
                                                              (cache a')
                                                              pa pa'
                                                              (smm_context a)
                                                              Hneqi).
        rewrite Heqa'.
        simpl.
        unfold global_update_in_cache.
        destruct cache_hit_dec as [_H|Hncache_hit] ; [
          unfold update_in_cache;
          reflexivity
        | apply Hncache_hit in c;
          destruct c;
          exact c0 ].
        exact Hcache_hit'.
        assert (find_cache_content a pa' = Some (content (find_in_map (cache a) (phys_to_index pa')))) as Hfind.
        unfold find_cache_content, find_in_cache.
        destruct cache_hit_dec as [_H|Hncache_hit]; [ reflexivity |].
        apply Hncache_hit in H; destruct H.
        rewrite <- Hfind.
        rewrite Hclean; [
            reflexivity |
            exact Hinside' |
            exact H ].
  + unfold load_in_cache in Heqa'.
    unfold find_cache_content.
    unfold find_in_cache.
    destruct cache_hit_dec; [| intuition ].
    rewrite Heqa'; simpl.
    destruct (eq_dec pa pa') as [Heqpa|Hneqpa].
    * apply eq_equal in Heqpa.
      rewrite <- Heqpa.
      rewrite add_1.
      simpl.
      rewrite <- Heqpa in Hinside'.
      apply Hin_smm in Hinside'.
      unfold smm_context.
      destruct is_in_smm_dec.
      reflexivity.
      apply n0 in Hinside'.
      destruct Hinside'.
    * destruct (eq_dec (phys_to_index pa) (phys_to_index pa')) as [Heqi|Hneqi].
      - assert (~ cache_hit (cache a') pa'); [| intuition ].
        assert (cache_hit (cache a') pa).
        unfold cache_hit.
        rewrite Heqa'.
        simpl.
        rewrite add_1.
        simpl.
        apply addr_eq_refl.
        apply (cache_hit_same_index_cache_miss (cache a') pa pa' H Hneqpa Heqi).
      - rewrite <- add_2; [| exact Hneqi ].
        assert (cache_hit (cache a) pa').
        apply (cache_hit_is_preserve_by_non_conflicted_update (cache a)
                                                              (cache a')
                                                              pa pa'
                                                              (smm_context a)
                                                              Hneqi).
        rewrite Heqa'.
        simpl.
        unfold global_update_in_cache.
        destruct cache_hit_dec; [ intuition |].
        unfold load_in_cache.
        reflexivity.
        exact c.
        assert (find_cache_content a pa' = Some (content (find_in_map (cache a) (phys_to_index pa')))).
        unfold find_cache_content, find_in_cache.
        destruct cache_hit_dec.
        reflexivity.
        apply n0 in H; destruct H.
        rewrite <- H0.
        rewrite Hclean; [
            reflexivity |
            exact Hinside' |
            exact H ].
Qed.

Lemma update_cache_content_with_context_preserves_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = update_cache_content a pa (smm_context a)
    -> inv a'.
Proof.
  intros a a' pa.
  intros Hinv Hsmm Heqa'.
  unfold inv.
  split; [| split; [| split; [| split; [| split]]]]; [
      eapply (update_cache_content_with_context_preserves_smramc_inv a a' pa)
    | eapply (update_cache_content_with_context_preserves_smram_code_inv a a' pa)
    | eapply (update_cache_content_with_context_preserves_smrr_inv a a' pa)
    | eapply (update_cache_content_with_context_preserves_cache_clean_inv a a' pa)
    | eapply (update_cache_content_with_context_preserves_ip_inv a a' pa)
    | eapply (update_cache_content_with_context_preserves_smbase_inv a a' pa) ]; trivial.
Qed.

Lemma load_then_update_cache_with_context_preserves_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = update_cache_content (load_in_cache_from_memory a pa) pa (smm_context a)
    -> inv a'.
Proof.
  intros a a'' pa Hinv Hin_smm Heqa''.
  remember (load_in_cache_from_memory a pa) as a'.
  assert (inv a') as Hinv'.
  apply (load_in_cache_from_memory_preserves_inv a a' pa Hinv Hin_smm Heqa').
  assert (proc a = proc a').
  apply load_in_cache_from_memory_changes_only_mem_and_cache in Heqa' as [Hproc _H].
  exact Hproc.
  rewrite H in Hin_smm.
  rewrite (context_is_preserves a a' H) in Heqa''.
  apply (update_cache_content_with_context_preserves_inv a' a'' pa Hinv' Hin_smm Heqa'').
Qed.
