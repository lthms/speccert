Require Import SpecCert.Address.
Require Import SpecCert.Cache.
Require Import SpecCert.Interval.
Require Import SpecCert.Memory.
Require Import SpecCert.x86.

Require Import SpecCert.Smm.Software.
Require Import SpecCert.Smm.Delta.Invariant.

Require Import Coq.Logic.Classical_Prop.

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
  destruct (is_inside_smram_dec pa').
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
    destruct (hardware_addr_eq_dec ha (dram addr)).
    * apply hardware_addr_eq_eq in h.
      rewrite h.
      rewrite update_ha_in_memory_is_ha.
      trivial.
    * Print update_ha_in_memory_changes_only_ha.
      rewrite <- (update_ha_in_memory_changes_only_ha a ha (dram addr) smm); [
      | trivial
      ].
      apply Hsmram; trivial.
  + unfold smram_code_inv.
    intros addr Haddr.
    unfold phys_to_hard, translate_physical_address in Heqha.
    destruct (is_inside_smram_dec pa'); [ intuition |].
    rewrite Heqha in *.
    rewrite Heqa'.
    assert (~ hardware_addr_eq (dram pa') (dram addr)).
    * unfold not; intro Hfalse.
      unfold hardware_addr_eq in Hfalse.
      destruct Hfalse as [_ Heq].
      simpl in Heq.
      assert (~ addr_eq pa' addr).
      unfold is_inside_smram in *.
      apply x1_not_in_interval_x2_in_interval_x1_neq_x2 with (i:=smram_space); trivial.
      intuition.
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
    -> a' = update_memory_content a (phys_to_hard a pa) (context (proc a))
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
  destruct is_inside_smram_dec.
  + destruct can_access_smram_dec.
    * assert (context (proc a) = smm).
      unfold can_access_smram in c.
      destruct c as [Hsmm|Hfalse].
      unfold context.
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
      destruct (addr_eq_dec pa pa').
      apply addr_eq_eq in a0.
      rewrite a0.
      apply _HardAddrMap.add_1.
      rewrite <- _HardAddrMap.add_2.
      apply Hsmram.
      exact Hinside'.
      unfold hardware_addr_eq.
      intuition.
    * rewrite <- _HardAddrMap.add_2.
      apply Hsmram.
      exact Hinside'.
      unfold hardware_addr_eq.
      unfold is_same_memory.
      intuition.
  + assert (~ addr_eq pa pa').
    apply x1_not_in_interval_x2_in_interval_x1_neq_x2 with (i:=smram_space).
    exact n.
    exact Hinside'.
    rewrite <- _HardAddrMap.add_2.
    apply Hsmram.
    apply Hinside'.
    unfold hardware_addr_eq.
    unfold hardware_address.
    intuition.
Qed.

Lemma update_memory_content_with_context_preserves_smramc_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a (phys_to_hard a pa) (context (proc a))
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
    -> a' = update_memory_content a (phys_to_hard a pa) (context (proc a))
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
    -> a' = update_memory_content a (phys_to_hard a pa) (context (proc a))
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
    -> a' = update_memory_content a (phys_to_hard a pa) (context (proc a))
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
    -> a' = update_memory_content a (phys_to_hard a pa) (context (proc a))
    -> ip_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Heqa'.
  apply update_memory_changes_only_memory in Heqa' as [Hmc [Hproc Hother]].
  unfold ip_inv.
  rewrite <- Hproc.
  exact Hip.
Qed.

Lemma update_memory_content_with_context_preserves_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a
    -> a' = update_memory_content a (phys_to_hard a pa) (context (proc a))
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
  destruct (cache_location_is_dirty_dec (cache a) pa).
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
  destruct (cache_location_is_dirty_dec (cache a) pa).
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
      destruct (addr_eq_dec pa pa').
      - apply addr_eq_eq in a0.
        rewrite a0.
        assert (cache_hit 
                  (_IndexMap.add_in_map (cache ax) (phys_to_index pa')
                                        {| dirty := true; content := c'; tag := pa' |}) pa').
        unfold cache_hit.
        rewrite _IndexMap.add_1.
        simpl.
        apply addr_eq_refl.
        destruct (cache_hit_dec
                  (_IndexMap.add_in_map (cache ax) (phys_to_index pa')
                                        {| dirty := true; content := c'; tag := pa' |}) pa');
          [| intuition].
        rewrite _IndexMap.add_1.
        simpl.
        rewrite a0 in Heqc'.
        unfold phys_to_hard, translate_physical_address in Heqc'.
        destruct (is_inside_smram_dec pa'); [| intuition ].
        assert (is_in_smm (proc a)); [
            rewrite <- a0 in i;
            apply (Hin_smm i) |].
        destruct (can_access_smram_dec (memory_controller a) (in_smm (proc a))); [
          |  unfold can_access_smram in n;
            intuition ].
        rewrite Hsmram in Heqc'; [| exact i ].
        rewrite Heqc'.
        reflexivity.
      - destruct (index_dec (phys_to_index pa) (phys_to_index pa')).
        assert (cache_hit (cache a') pa); [
            rewrite Heqa';
            simpl;
            apply global_update_in_cache_cache_hit |].
        assert (~ cache_hit (cache a') pa'); [
            apply (cache_hit_same_index_cache_miss (cache a') pa); trivial
          | intuition ].
        assert (cache_hit 
                  (_IndexMap.add_in_map (cache ax) (phys_to_index pa)
                                        {| dirty := true; content := c'; tag := pa |}) pa').
        unfold cache_hit.
        rewrite <- _IndexMap.add_2; [| exact n0 ].
        rewrite Heqa' in Hcache_hit.
        simpl in Hcache_hit.
        unfold cache_hit, global_update_in_cache in Hcache_hit.
        destruct (cache_hit_dec (cache ax) pa).
        unfold update_in_cache in Hcache_hit.
        rewrite <- _IndexMap.add_2 in Hcache_hit; [| exact n0 ].
        exact Hcache_hit.
        apply n1 in Hcache_hit_pa.
        destruct Hcache_hit_pa.
        destruct (cache_hit_dec
                    (_IndexMap.add_in_map (cache ax) (phys_to_index pa)
                                          {| dirty := true; content := c'; tag := pa |}) pa').
        rewrite <- _IndexMap.add_2.
        unfold cache_clean_inv in Hclean.
        destruct H as [Hsmramcx [Hsmramx [Hsmrrx [Hcleanx Hipx]]]].
        assert (cache_hit (cache ax) pa'); [
            apply (cache_hit_is_preserve_by_non_conflicted_update (cache ax)
                                                                  (cache a')
                                                                  pa
                                                                  pa'
                                                                  c'); [
            exact n0 |
            rewrite Heqa'; simpl; reflexivity |
            exact Hcache_hit ] |].
        assert (find_cache_content ax pa' = Some (content (_IndexMap.find_in_map (cache ax) (phys_to_index pa')))).
        unfold find_cache_content, find_in_cache.
        destruct (cache_hit_dec (cache ax) pa'); [ reflexivity | intuition ].
        rewrite <- H1.
        apply (Hcleanx pa' Hinside' H).
        exact n0.
        apply n1 in H0.
        destruct H0.
    * destruct (index_dec (phys_to_index pa) (phys_to_index pa')).
      - assert (cache a'=global_update_in_cache (cache ax) pa c') as Heqcache'; [
          rewrite Heqa';
          simpl;
          reflexivity |].
        assert (cache_hit (global_update_in_cache (cache ax) pa c') pa); [
            apply (global_update_in_cache_cache_hit (cache ax) pa) |].
        rewrite <- Heqcache' in H0.
        destruct (addr_eq_dec pa pa').
        (* case addr_eq *)
        apply addr_eq_eq in a0.
        rewrite a0 in Heqc'.
        unfold smram_code_inv in Hsmram.
        assert (is_inside_smram pa'); try exact Hinside'.
        rewrite <- a0 in Hinside'.
        apply Hin_smm in Hinside'.
        unfold is_in_smm in Hinside'.
        unfold phys_to_hard, translate_physical_address in Heqc'.
        rewrite <- a0 in Heqc'.
        destruct (is_inside_smram_dec pa).
        rewrite Hinside' in Heqc'.
        destruct (can_access_smram_dec (memory_controller a) true).
        rewrite Hsmram in Heqc'; try trivial.
        rewrite Heqc'.
        unfold find_in_cache, load_in_cache.
        rewrite <- a0.
        destruct cache_hit_dec.
        rewrite _IndexMap.add_1.
        simpl.
        reflexivity.
        unfold cache_hit in n.
        rewrite _IndexMap.add_1 in n.
        simpl in n.
        unfold not in n.
        assert (addr_eq pa pa). apply addr_eq_refl.
        apply n in H2. destruct H2.
        unfold can_access_smram in n.
        apply not_or_and in n.
        destruct n as [G1 G2].
        intuition.
        rewrite <- a0 in H1.
        intuition.
        (* case ~ addr_eq *)
        apply (global_update_not_cache_hit (cache ax) (cache a') pa pa' c') in Heqcache'; try intuition.
      - unfold find_in_cache, load_in_cache.
        destruct cache_hit_dec.
        rewrite <- _IndexMap.add_2.
        destruct H as [Hsmramcx [Hsmramx [Hsmrrx [Hcleanx Hipx]]]].
        assert (cache_hit (cache ax) pa') as Hcache_hit_before; [
            apply (cache_hit_is_preserve_by_non_conflicted_update (cache ax)
                                                                  (cache a')
                                                                  pa
                                                                  pa'
                                                                  c'); [
              exact n
            | rewrite Heqa'; reflexivity
            | exact Hcache_hit ] |].
        unfold cache_clean_inv in Hcleanx.
        assert ((if cache_hit_dec (cache ax) pa'
                 then Some (content (_IndexMap.find_in_map (cache ax) (phys_to_index pa')))
                 else None) = Some smm).
        apply (Hcleanx _ Hinside' Hcache_hit_before).
        destruct cache_hit_dec; [ | intuition ].
        rewrite H.
        reflexivity.
        exact n.
        destruct H as [Hsmramcx [Hsmramx [Hsmrrx Hcleanx]]].
        assert (cache_hit (cache ax) pa') as Hcache_hit_before; [
            apply (cache_hit_is_preserve_by_non_conflicted_update (cache ax) (cache a') pa pa' c'); [
              exact n
            | rewrite Heqa'; reflexivity
            | exact Hcache_hit ] |].
        exfalso.
        apply n0.
        unfold cache_hit.
        rewrite <- _IndexMap.add_2.
        exact Hcache_hit_before.
        exact n.
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
      destruct (addr_eq_dec pa pa').
      apply addr_eq_eq in a0.
      rewrite a0.
      assert (cache_hit 
                (_IndexMap.add_in_map (cache a) (phys_to_index pa')
                                      {| dirty := true; content := smm; tag := pa' |}) pa').
      unfold cache_hit.
      rewrite _IndexMap.add_1.
      simpl.
      apply addr_eq_refl.
      destruct cache_hit_dec; [| intuition ].
      rewrite _IndexMap.add_1; reflexivity.
      remember (_IndexMap.add_in_map (cache a)
                                     (phys_to_index pa)
                                     {| dirty := true; content := smm; tag := pa |}) as cachex.
      assert (cachex = cache'); [ rewrite Heqcache';
                                  rewrite Heqcachex;
                                  reflexivity |].
      rewrite H1 in *.
      assert (cache' = cache a').
      rewrite Heqa'; rewrite Heqcache'; reflexivity.
      rewrite H2.
      destruct (cache_hit_dec (cache a') pa'); [| try intuition ].
      destruct (index_dec (phys_to_index pa) (phys_to_index pa')).
      assert (~ cache_hit (cache a') pa'); [| try intuition ].
      rewrite Heqa'.
      rewrite Heqcache'.
      simpl.
      unfold cache_hit, update_in_cache.
      apply index_eq_eq in i0.
      rewrite <- i0.
      rewrite _IndexMap.add_1.
      simpl.
      intro Hnot.
      apply addr_eq_sym in Hnot.
      apply n0 in Hnot.
      exact Hnot.
      rewrite Heqa'.
      rewrite Heqcache'.
      simpl.
      unfold cache_hit, update_in_cache.
      rewrite <- _IndexMap.add_2 with (k:=phys_to_index pa)
                                     (c:={| dirty := true; content := smm; tag := pa |}); [
        | exact n1].
      unfold cache_clean_inv in Hclean.
      assert (cache_hit (cache a) pa').
      (**********************)
      rewrite <- H2 in c2.
      rewrite Heqcache' in c2.
      unfold update_in_cache in c2.
      unfold cache_hit in c2.
      rewrite <- _IndexMap.add_2 in c2; [| exact n1 ].
      exact c2.
      (**********************)
      assert (find_cache_content a pa' = Some (content (_IndexMap.find_in_map (cache a) (phys_to_index pa')))).
      unfold find_cache_content.
      unfold find_in_cache.
      destruct (cache_hit_dec (cache a) pa'); [ | try intuition ].
      reflexivity.
      rewrite <- H4.
      rewrite Hclean; [
          reflexivity
        | exact Hinside'
        | exact H3 ].
      
      rewrite Heqa'; rewrite Heqcache'.
      unfold find_cache_content, find_in_cache, load_in_cache, update_in_cache.
      simpl.
      destruct (addr_eq_dec pa pa').
      apply addr_eq_eq in a0.
      rewrite a0.
      assert (cache_hit 
                (_IndexMap.add_in_map (cache a) (phys_to_index pa')
                                      {| dirty := false; content := smm; tag := pa' |}) pa').
      unfold cache_hit.
      rewrite _IndexMap.add_1.
      simpl.
      apply addr_eq_refl.
      destruct cache_hit_dec; [| intuition ].
      rewrite _IndexMap.add_1; reflexivity.
      remember (_IndexMap.add_in_map (cache a)
                                     (phys_to_index pa)
                                     {| dirty := false; content := smm; tag := pa |}) as cachex.
      assert (cachex = cache'); [ rewrite Heqcache';
                                  rewrite Heqcachex;
                                  reflexivity |].
      rewrite H1 in *.
      assert (cache' = cache a').
      rewrite Heqa'; rewrite Heqcache'; reflexivity.
      rewrite H2.
      destruct (cache_hit_dec (cache a') pa'); [| try intuition ].
      destruct (index_dec (phys_to_index pa) (phys_to_index pa')).
      assert (~ cache_hit (cache a') pa'); [| try intuition ].
      rewrite Heqa'.
      rewrite Heqcache'.
      simpl.
      unfold cache_hit, load_in_cache.
      apply index_eq_eq in i0.
      rewrite <- i0.
      rewrite _IndexMap.add_1.
      simpl.
      intro Hnot.
      apply addr_eq_sym in Hnot.
      apply n1 in Hnot.
      exact Hnot.
      rewrite Heqa'.
      rewrite Heqcache'.
      simpl.
      unfold cache_hit, load_in_cache.
      rewrite <- _IndexMap.add_2 with (k:=phys_to_index pa)
                                     (c:={| dirty := false; content := smm; tag := pa |}); [
        | exact n2].
      unfold cache_clean_inv in Hclean.
      assert (cache_hit (cache a) pa').
      (**********************)
      rewrite <- H2 in c1.
      rewrite Heqcache' in c1.
      unfold load_in_cache in c1.
      unfold cache_hit in c1.
      rewrite <- _IndexMap.add_2 in c1; [| exact n2 ].
      exact c1.
      (**********************)
      assert (find_cache_content a pa' = Some (content (_IndexMap.find_in_map (cache a) (phys_to_index pa')))).
      unfold find_cache_content.
      unfold find_in_cache.
      destruct (cache_hit_dec (cache a) pa'); [ | try intuition ].
      reflexivity.
      rewrite <- H4.
      rewrite Hclean; [
          reflexivity
        | exact Hinside'
        | exact H3 ].
    * assert (~ addr_eq pa pa'); [
        apply (x1_not_in_interval_x2_in_interval_x1_neq_x2 _ _ _ n0 Hinside') |].
      destruct (index_dec (phys_to_index pa) (phys_to_index pa')).
      - assert (~ cache_hit (cache a') pa'); [| intuition ].
        rewrite Heqa'.
        unfold update_cache_content, cache_hit, global_update_in_cache; simpl.
        destruct (cache_hit_dec (cache a) pa).
        unfold update_in_cache.
        apply index_eq_eq in i.
        rewrite <- i.
        rewrite _IndexMap.add_1.
        simpl.
        intro Hnot.
        apply addr_eq_sym in Hnot.
        apply H in Hnot. exact Hnot.
        unfold load_in_cache.
        apply index_eq_eq in i.
        rewrite <- i.
        rewrite _IndexMap.add_1.
        simpl.
        intro Hnot.
        apply addr_eq_sym in Hnot.
        apply H in Hnot. exact Hnot.
      - assert (cache_hit (cache a) pa').
        rewrite Heqa' in Hcache_hit'.
        unfold cache_hit, update_cache_content in Hcache_hit'.
        simpl in Hcache_hit'.
        unfold global_update_in_cache in Hcache_hit'.
        destruct (cache_hit_dec (cache a) pa); [
            unfold update_in_cache in Hcache_hit';
            rewrite <- _IndexMap.add_2 in Hcache_hit'; [| exact n1 ];
            exact Hcache_hit' |
            unfold load_in_cache in Hcache_hit' ;
              rewrite <- _IndexMap.add_2 in Hcache_hit'; [| exact n1 ] ;
              exact Hcache_hit' ].
        assert (find_cache_content a' pa' = find_cache_content a pa').
        unfold find_cache_content.
        unfold find_in_cache.
        do 2 (destruct cache_hit_dec; [| intuition ]).
        rewrite Heqa'.
        unfold update_cache_content, global_update_in_cache, load_in_cache, update_in_cache; simpl.
        destruct cache_hit_dec;
          (rewrite <- _IndexMap.add_2; [ reflexivity | exact n1 ]).
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
    -> a' = update_cache_content a pa (context (proc a))
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
    -> a' = update_cache_content a pa (context (proc a))
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
    -> a' = update_cache_content a pa (context (proc a))
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
    -> a' = update_cache_content a pa (context (proc a))
    -> ip_inv a'.
Proof.
  intros a a' pa [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hin_smm Heqa'.
  apply update_cache_changes_only_cache in Heqa' as [Hproc [Hmc Hmem]].
  unfold ip_inv.
  rewrite <- Hproc.
  exact Hip.
Qed.

Lemma update_cache_content_with_context_preserves_smbase_inv:
  forall a a' :Architecture Software,
  forall pa   :PhysicalAddress,
    inv a -> (is_inside_smram pa -> is_in_smm (proc a))
    -> a' = update_cache_content a pa (context (proc a))
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
    -> a' = update_cache_content a pa (context (proc a))
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
    destruct (addr_eq_dec pa pa').
    * apply addr_eq_eq in a0.
      rewrite <- a0.
      rewrite _IndexMap.add_1.
      simpl.
      rewrite <- a0 in Hinside'.
      apply Hin_smm in Hinside'.
      unfold context.
      destruct is_in_smm_dec.
      reflexivity.
      apply n in Hinside'.
      destruct Hinside'.
    * destruct (index_dec (phys_to_index pa) (phys_to_index pa')).
      - assert (~ cache_hit (cache a') pa'); [| intuition ].
        assert (cache_hit (cache a') pa).
        unfold cache_hit.
        rewrite Heqa'.
        simpl.
        rewrite _IndexMap.add_1.
        simpl.
        apply addr_eq_refl.
        apply (cache_hit_same_index_cache_miss (cache a') pa pa' H n i).
      - rewrite <- _IndexMap.add_2; [| exact n0 ].
        assert (cache_hit (cache a) pa').
        apply (cache_hit_is_preserve_by_non_conflicted_update (cache a)
                                                              (cache a')
                                                              pa pa'
                                                              (context (proc a))
                                                              n0).
        rewrite Heqa'.
        simpl.
        unfold global_update_in_cache.
        destruct cache_hit_dec; [| intuition ].
        unfold update_in_cache.
        reflexivity.
        apply n1 in c.
        destruct c.
        exact c0.
        assert (find_cache_content a pa' = Some (content (_IndexMap.find_in_map (cache a) (phys_to_index pa')))).
        unfold find_cache_content, find_in_cache.
        destruct cache_hit_dec.
        reflexivity.
        apply n1 in H; destruct H.
        rewrite <- H0.
        rewrite Hclean; [
            reflexivity |
            exact Hinside' |
            exact H ].
  + unfold load_in_cache in Heqa'.
    unfold find_cache_content.
    unfold find_in_cache.
    destruct cache_hit_dec; [| intuition ].
    rewrite Heqa'; simpl.
    destruct (addr_eq_dec pa pa').
    * apply addr_eq_eq in a0.
      rewrite <- a0.
      rewrite _IndexMap.add_1.
      simpl.
      rewrite <- a0 in Hinside'.
      apply Hin_smm in Hinside'.
      unfold context.
      destruct is_in_smm_dec.
      reflexivity.
      apply n0 in Hinside'.
      destruct Hinside'.
    * destruct (index_dec (phys_to_index pa) (phys_to_index pa')).
      - assert (~ cache_hit (cache a') pa'); [| intuition ].
        assert (cache_hit (cache a') pa).
        unfold cache_hit.
        rewrite Heqa'.
        simpl.
        rewrite _IndexMap.add_1.
        simpl.
        apply addr_eq_refl.
        apply (cache_hit_same_index_cache_miss (cache a') pa pa' H n0 i).
      - rewrite <- _IndexMap.add_2; [| exact n1 ].
        assert (cache_hit (cache a) pa').
        apply (cache_hit_is_preserve_by_non_conflicted_update (cache a)
                                                              (cache a')
                                                              pa pa'
                                                              (context (proc a))
                                                              n1).
        rewrite Heqa'.
        simpl.
        unfold global_update_in_cache.
        destruct cache_hit_dec; [ intuition |].
        unfold load_in_cache.
        reflexivity.
        exact c.
        assert (find_cache_content a pa' = Some (content (_IndexMap.find_in_map (cache a) (phys_to_index pa')))).
        unfold find_cache_content, find_in_cache.
        destruct cache_hit_dec.
        reflexivity.
        apply n2 in H; destruct H.
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
    -> a' = update_cache_content a pa (context (proc a))
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
    -> a' = update_cache_content (load_in_cache_from_memory a pa) pa (context (proc a))
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
  rewrite H in Heqa''.
  apply (update_cache_content_with_context_preserves_inv a' a'' pa Hinv' Hin_smm Heqa'').
Qed.