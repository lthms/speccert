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

Lemma update_memory_content_with_cache_content_preserves_smram_code_inv
      (a a': Architecture Software)
      (pa:   PhysicalAddress)
  : let cont := find_in_cache_location (cache a) pa
    in inv a
       -> a' = update_memory_content a
                                     (phys_to_hard a (cache_location_address (cache a) pa))
                                     cont
       -> smram_code_inv a'.
Proof.
  simpl.
  remember (cache_location_address (cache a) pa) as pa'.
  remember (find_in_cache_location (cache a) pa) as c'.
  remember (phys_to_hard a pa') as ha.
  intros [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Heqa'.
  destruct (is_inside_smram_dec pa') as [Hinside|Houtside].
  + rewrite (cache_location_cache_location (cache a) pa pa') in Heqc'; [
    | apply x86_cache_is_well_formed
    | trivial
    ].
    symmetry in Heqc'.
    apply find_in_cache_cache_location in Heqc'; [
      | apply x86_cache_is_well_formed ].
    assert (cache_hit (cache a) pa') as Hhit.
    rewrite Heqpa';
      apply cache_hit_cache_location_address;
      apply x86_cache_is_well_formed.
    rewrite <- cache_hit_cache_location_cache_find in Heqc'; [
      | trivial
      ].
    unfold cache_clean_inv in *.
    unfold find_cache_content in Hclean.
    induction c' as [v s].
    assert (s = smm).
    apply (Hclean pa' v s Hinside Hhit Heqc').
    unfold smram_code_inv.
    intros addr val s' Hinside' Hfind.
    rewrite H in Heqa'.
    destruct (eq_dec ha (dram addr)) as [Heq|Hneq].
    * apply eq_equal in Heq.
      rewrite Heqa' in Hfind.
      rewrite Heq in Hfind.
      rewrite update_ha_in_memory_is_ha in Hfind.
      inversion Hfind.
      reflexivity.
    * rewrite Heqa' in Hfind.
      unfold find_memory_content, find_in_memory, update_memory_content, update_in_memory in Hfind.
      simpl in Hfind.
      rewrite <- add_2 in Hfind; [| exact Hneq].
      unfold smram_code_inv in Hsmram.
      apply (Hsmram addr val s' Hinside' Hfind).
  + unfold smram_code_inv.
    intros addr val s Haddr.
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

Lemma update_memory_content_with_cache_content_preserves_cache_clean_inv
      (a a':  Architecture Software)
      (pa:    PhysicalAddress)
      (Hinv:  inv a)
      (Heqa': a' = update_memory_content a
                                         (phys_to_hard a (cache_location_address (cache a) pa))
                                         (find_in_cache_location (cache a) pa))
  : cache_clean_inv a'.
Proof.
  remember (cache_location_address (cache a) pa) as pa'.
  remember (find_in_cache_location (cache a) pa) as c'.
  remember (phys_to_hard a pa') as ha'.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
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

Lemma update_memory_content_with_context_preserves_smram_code_inv
      (a a':   Architecture Software)
      (pa:     PhysicalAddress)
      (val:    Value)
      (Hinv:   inv a)
      (Heqa': a' = update_memory_content a (phys_to_hard a pa) (val, smm_context a))
    : smram_code_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hclean [Hsmrr [Hip Hsmbase]]]]].
  unfold smram_code_inv.
  intros pa' val' s Hinside' Hfind.
  unfold update_memory_content in Heqa'.
  unfold update_in_memory in Heqa'.
  unfold find_memory_content, find_in_memory.
  rewrite Heqa' in Hfind.
  unfold find_memory_content, find_in_memory in Hfind.
  simpl in Hfind.
  unfold phys_to_hard, translate_physical_address in Hfind.
  destruct is_inside_smram_dec as [Hinside|Houtside].
  + destruct can_access_smram_dec as [Hcan|Hcannot].
    * assert (smm_context a = smm) as Hcontext.
      - unfold can_access_smram in Hcan.
        destruct Hcan as [Hsmm|Hfalse].
        unfold smm_context.
        destruct is_in_smm_dec as [Hin|Hnotin]; try reflexivity.
        unfold is_in_smm in Hnotin.
        apply Hnotin in Hsmm.
        destruct Hsmm.
        unfold smramc_inv in Hsmramc.
        unfold smramc_is_locked in Hsmramc.
        unfold smramc_is_ro in Hsmramc.
        apply (lock_is_close (smramc (memory_controller a))) in Hsmramc.
        rewrite Hsmramc in Hfalse.
        discriminate.
      - rewrite Hcontext in Hfind.
        destruct (eq_dec pa pa').
        apply eq_equal in e.
        rewrite e in Hfind.
        rewrite add_1 in Hfind.
        inversion Hfind.
        reflexivity.
        rewrite <- add_2 in Hfind.
        unfold smram_code_inv in Hsmram.
        apply (Hsmram pa' val' s Hinside' Hfind).
        intro Hfalse.
        apply hardware_dram_cast in Hfalse.
        apply n in Hfalse.
        exact Hfalse.
    * rewrite <- add_2 in Hfind.
      apply (Hsmram pa' val' s Hinside' Hfind).
      intro H.
      apply eq_sym in H.
      assert (~ eq (dram pa') (vga pa)).
      apply (neq_dram_vga_cast pa' pa).
      apply H0 in H.
      exact H.
  + assert (~ eq pa pa') as Hneqpapa'.
    apply (pa1_not_in_interval_pa2_in_interval_pa1_neq_pa2 pa pa' smram_space Houtside Hinside').
    rewrite <- (add_2 (memory a) (dram pa) (dram pa')) in Hfind.
    * apply (Hsmram pa' val' s Hinside' Hfind).
    * intro Hfalse.
      apply hardware_dram_cast in Hfalse.
      apply Hneqpapa' in Hfalse.
      exact Hfalse.
Qed.

Lemma update_memory_content_with_context_preserves_smramc_inv
      (a a':  Architecture Software)
      (pa:    PhysicalAddress)
      (val:   Value)
      (Hinv:  inv a)
      (Heqa': a' = update_memory_content a (phys_to_hard a pa) (val, smm_context a))
  : smramc_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  apply update_memory_changes_only_memory in Heqa' as [Hmc [Hproc Hother]].
  unfold smramc_inv.
  rewrite <- Hmc.
  exact Hsmramc.
Qed.

Lemma update_memory_content_with_context_preserves_smbase_inv
      (a a':  Architecture Software)
      (pa:    PhysicalAddress)
      (val:   Value)
      (Hinv:  inv a)
      (Heqa': a' = update_memory_content a (phys_to_hard a pa) (val, smm_context a))
  : smbase_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  apply update_memory_changes_only_memory in Heqa' as [Hmc [Hproc Hother]].
  unfold smbase_inv.
  rewrite <- Hproc.
  exact Hsmbase.
Qed.

Lemma update_memory_content_with_context_preserves_cache_clean_inv
      (a a':  Architecture Software)
      (pa:    PhysicalAddress)
      (val:   Value)
      (Hinv:  inv a)
      (Heqa': a' = update_memory_content a (phys_to_hard a pa) (val, smm_context a))
  : cache_clean_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean Hip]]]].
  apply update_memory_changes_only_memory in Heqa' as [Hmc [Hproc Hother]].
  unfold cache_clean_inv.
  unfold find_cache_content.
  rewrite <- Hother.
  exact Hclean.
Qed.

Lemma update_memory_content_with_context_preserves_smrr_inv
      (a a':  Architecture Software)
      (pa:    PhysicalAddress)
      (val:   Value)
      (Hinv:  inv a)
      (Heqa': a' = update_memory_content a (phys_to_hard a pa) (val, smm_context a))
  : smrr_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean Hip]]]].
  apply update_memory_changes_only_memory in Heqa' as [Hmc [Hproc Hother]].
  unfold smrr_inv.
  rewrite <- Hproc.
  exact Hsmrr.
Qed.

Lemma update_memory_content_with_context_preserves_ip_inv
      (a a':  Architecture Software)
      (pa:    PhysicalAddress)
      (val:   Value)
      (Hinv:  inv a)
      (Heqa': a' = update_memory_content a (phys_to_hard a pa) (val, smm_context a))
  : ip_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  apply update_memory_changes_only_memory in Heqa' as [Hmc [Hproc Hother]].
  unfold ip_inv.
  rewrite <- Hproc.
  rewrite <- (context_is_preserves a a' Hproc).
  exact Hip.
Qed.

Lemma update_memory_content_with_context_preserves_inv
      (a a':  Architecture Software)
      (pa:    PhysicalAddress)
      (val:   Value)
      (Hinv:  inv a)
      (Heqa': a' = update_memory_content a (phys_to_hard a pa) (val, smm_context a))
  : inv a'.
Proof.
  unfold inv.
  split; [| split; [| split; [| split; [| split]]]]; [
      eapply (update_memory_content_with_context_preserves_smramc_inv a a' pa val)
    | eapply (update_memory_content_with_context_preserves_smram_code_inv a a' pa val)
    | eapply (update_memory_content_with_context_preserves_smrr_inv a a' pa val)
    | eapply (update_memory_content_with_context_preserves_cache_clean_inv a a' pa val)
    | eapply (update_memory_content_with_context_preserves_ip_inv a a' pa val)
    | eapply (update_memory_content_with_context_preserves_smbase_inv a a' pa val) ]; trivial.
Qed.

Lemma load_in_cache_from_memory_preserves_smram_code_inv
      (a a':    Architecture Software)
      (pa:      PhysicalAddress)
      (Hinv:    inv a)
      (Heqa':   a' = load_in_cache_from_memory a pa)
  : smram_code_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
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

Lemma update_cache_with_memory_cache_clean_inv
      (a a':  Architecture Software)
      (pa:    PhysicalAddress)
      (Hinv:  inv a)
      (Hin_smm: (is_inside_smram pa -> is_in_smm (proc a)))
      (Heqa': a' = update_cache_content a pa (find_memory_content a (phys_to_hard a pa)))
  : cache_clean_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  unfold cache_clean_inv, find_cache_content.
  intros pa' v' s Hinside' Hcache_hit Hfind.
  remember (find_memory_content a (phys_to_hard a pa)) as c'.
  unfold update_cache_content in Heqa'.
  rewrite Heqa' in Hfind.
  simpl in Hfind.
  unfold global_update_in_cache in Hfind.
  destruct (cache_hit_dec (cache a) pa) as [Hcache_hit_pa|Hnot_cache_hit_pa].
  * unfold update_in_cache, find_in_cache in Hfind.
    destruct (eq_dec pa pa') as [Heqpapa'|Hneqpapa'].
    - apply eq_equal in Heqpapa'.
      rewrite Heqpapa' in Hfind.
      assert (cache_hit
                (add_in_map (cache a) (phys_to_index pa')
                            {| dirty := true; content := c'; tag := pa' |}) pa') as Hcache_hit_add.
      unfold cache_hit.
      rewrite add_1.
      apply eq_refl.
      destruct (cache_hit_dec
                (add_in_map (cache a) (phys_to_index pa')
                            {| dirty := true; content := c'; tag := pa' |}) pa');
        [| intuition].
      rewrite add_1 in Hfind.
      simpl in Hfind.
      rewrite Heqpapa' in Heqc'.
      unfold phys_to_hard, translate_physical_address in Heqc'.
      destruct (is_inside_smram_dec pa') as [Hinside|_H]; [| intuition ].
      assert (is_in_smm (proc a)); [
          rewrite <- Heqpapa' in Hinside;
          apply (Hin_smm Hinside) |].
      destruct (can_access_smram_dec (memory_controller a) (in_smm (proc a))) as [Hcan|Hcannot]; [
        |  unfold can_access_smram in Hcannot;
          intuition ].
      destruct c'.
      apply (Hsmram pa' v s Hinside).
      rewrite <- Heqc'.
      inversion Hfind.
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
                (add_in_map (cache a) (phys_to_index pa)
                            {| dirty := true; content := c'; tag := pa |}) pa').
      unfold cache_hit.
      rewrite <- add_2; [| exact Hneqi ].
      rewrite Heqa' in Hcache_hit.
      simpl in Hcache_hit.
      unfold cache_hit, global_update_in_cache in Hcache_hit.
      destruct (cache_hit_dec (cache a) pa) as [Hcache_hit_x_pa|Hncache_hit_x_pa].
      unfold update_in_cache in Hcache_hit.
      rewrite <- add_2 in Hcache_hit; [| exact Hneqi ].
      exact Hcache_hit.
      apply Hncache_hit_x_pa in Hcache_hit_pa.
      destruct Hcache_hit_pa.
      destruct (cache_hit_dec
                  (add_in_map (cache a) (phys_to_index pa)
                              {| dirty := true; content := c'; tag := pa |}) pa') as [Hcache_add|Hncache_add].
      rewrite <- add_2 in Hfind.
      unfold cache_clean_inv in Hclean.
      assert (cache_hit (cache a) pa') as Hcache_hit_x_pa'; [
          apply (cache_hit_is_preserve_by_non_conflicted_update (cache a)
                                                                (cache a')
                                                                pa
                                                                pa'
                                                                c'); [
          exact Hneqi |
          rewrite Heqa'; simpl; reflexivity |
          exact Hcache_hit ] |].
      assert (find_cache_content a pa' = Some (content (find_in_map (cache a) (phys_to_index pa')))) as Hfind'.
      unfold find_cache_content, find_in_cache.
      destruct (cache_hit_dec (cache a) pa') as [_H|_H]; [ reflexivity | intuition ].
      apply (Hclean pa' v' s Hinside' Hcache_hit_x_pa').
      inversion Hfind.
      exact Hfind'.
      exact Hneqi.
      discriminate Hfind.
  * destruct (eq_dec (phys_to_index pa) (phys_to_index pa')) as [Heqi|Hneqi].
    - assert (cache a'=global_update_in_cache (cache a) pa c') as Heqcache'; [
        rewrite Heqa';
        simpl;
        reflexivity |].
      assert (cache_hit (global_update_in_cache (cache a) pa c') pa); [
          apply (global_update_in_cache_cache_hit (cache a) pa) |].
      rewrite <- Heqcache' in H.
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
      destruct c' as [v l].
      assert (l = smm).
      apply (Hsmram pa v l i).
      symmetry; exact Heqc'.
      rewrite H1 in *.
      unfold find_in_cache, load_in_cache in Hfind.
      rewrite <- Heq in Hfind.
      destruct cache_hit_dec.
      rewrite add_1 in Hfind.
      simpl in Hfind.
      inversion Hfind.
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
      rewrite <- Heq in H0.
      intuition.
      (* case ~ addr_eq *)
      apply (global_update_not_cache_hit (cache a) (cache a') pa pa' c') in Heqcache'; try intuition.
    - unfold find_in_cache, load_in_cache in Hfind.
      destruct cache_hit_dec.
      rewrite <- add_2 in Hfind.
      assert (cache_hit (cache a) pa') as Hcache_hit_before; [
          apply (cache_hit_is_preserve_by_non_conflicted_update (cache a)
                                                                (cache a')
                                                                pa
                                                                pa'
                                                                c'); [
            exact Hneqi
          | rewrite Heqa'; reflexivity
          | exact Hcache_hit ] |].
      unfold cache_clean_inv in Hclean.
      inversion Hfind.
      apply (Hclean pa' v' s Hinside' Hcache_hit_before).
      unfold find_cache_content.
      unfold find_in_cache.
      destruct cache_hit_dec; intuition.
      exact Hneqi.
      discriminate Hfind.
Qed.

Lemma load_in_cache_from_memory_preserves_cache_clean_inv
      (a a':  Architecture Software)
      (pa:    PhysicalAddress)
      (Hinv:  inv a)
      (Hin_smm: (is_inside_smram pa -> is_in_smm (proc a)))
      (Heqa': a' = load_in_cache_from_memory a pa)
  : cache_clean_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
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
    assert (inv ax) as Hinvx.
    apply (update_memory_content_with_cache_content_preserves_inv a ax pa); trivial.
    apply (update_cache_with_memory_cache_clean_inv ax a' pa Hinvx);
      destruct Hinvx as [Hsmramcx [Hsmramx [Hsmrrx [Hcleanx [Hipx Hsmbasex]]]]].
    - apply update_memory_changes_only_memory in Heqax.
      destruct Heqax as [_Hmc [Hproc _Hcache]].
      rewrite <- Hproc.
      exact Hin_smm.
    - exact Heqa'.
  + apply (update_cache_with_memory_cache_clean_inv a a' pa Hinv Hin_smm Heqa').
Qed.

Lemma load_in_cache_from_memory_preserves_smrr_inv
      (a a':    Architecture Software)
      (pa:      PhysicalAddress)
      (Hinv:    inv a)
      (Hin_smm: is_inside_smram pa -> is_in_smm (proc a))
      (Heqa':   a' = load_in_cache_from_memory a pa)
  : smrr_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  apply load_in_cache_from_memory_changes_only_mem_and_cache in Heqa' as [Hproc Hother].
  unfold smrr_inv.
  rewrite <- Hproc.
  exact Hsmrr.
Qed.

Lemma load_in_cache_from_memory_preserves_smramc_inv
      (a a':    Architecture Software)
      (pa:      PhysicalAddress)
      (Hinv:    inv a)
      (Hin_smm: is_inside_smram pa -> is_in_smm (proc a))
      (Heqa':   a' = load_in_cache_from_memory a pa)
  : smramc_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  apply load_in_cache_from_memory_changes_only_mem_and_cache in Heqa' as [Hproc Hother].
  unfold smramc_inv.
  rewrite <- Hother.
  exact Hsmramc.
Qed.

Lemma load_in_cache_from_memory_preserves_smbase_inv
      (a a':    Architecture Software)
      (pa:      PhysicalAddress)
      (Hinv:    inv a)
      (Hin_smm: is_inside_smram pa -> is_in_smm (proc a))
      (Heqa':   a' = load_in_cache_from_memory a pa)
  : smbase_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  apply load_in_cache_from_memory_changes_only_mem_and_cache in Heqa' as [Hproc Hother].
  unfold smbase_inv.
  rewrite <- Hproc.
  exact Hsmbase.
Qed.

Lemma load_in_cache_from_memory_preserves_ip_inv
      (a a':    Architecture Software)
      (pa:      PhysicalAddress)
      (Hinv:    inv a)
      (Hin_smm: is_inside_smram pa -> is_in_smm (proc a))
      (Heqa':   a' = load_in_cache_from_memory a pa)
  : ip_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  apply load_in_cache_from_memory_changes_only_mem_and_cache in Heqa' as [Hproc Hother].
  unfold ip_inv.
  rewrite <- Hproc.
  rewrite <- (context_is_preserves a a' Hproc).
  exact Hip.
Qed.

Lemma load_in_cache_from_memory_preserves_inv
      (a a':    Architecture Software)
      (pa:      PhysicalAddress)
      (Hinv:    inv a)
      (Hin_smm: is_inside_smram pa -> is_in_smm (proc a))
      (Heqa':   a' = load_in_cache_from_memory a pa)
  : inv a'.
Proof.
  unfold inv.
  split; [| split; [| split; [| split; [| split]]]]; [
      eapply (load_in_cache_from_memory_preserves_smramc_inv a a' pa)
    | eapply (load_in_cache_from_memory_preserves_smram_code_inv a a' pa)
    | eapply (load_in_cache_from_memory_preserves_smrr_inv a a' pa)
    | eapply (load_in_cache_from_memory_preserves_cache_clean_inv a a' pa)
    | eapply (load_in_cache_from_memory_preserves_ip_inv a a' pa)
    | eapply (load_in_cache_from_memory_preserves_smbase_inv a a' pa) ]; trivial.
Qed.

Lemma update_cache_content_with_context_preserves_smramc_inv
      (a a':    Architecture Software)
      (pa:      PhysicalAddress)
      (val:     Value)
      (Hinv:    inv a)
      (Hin_smm: is_inside_smram pa -> is_in_smm (proc a))
      (Heqa':   a' = update_cache_content a pa (val, (smm_context a)))
  : smramc_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  apply update_cache_changes_only_cache in Heqa' as [Hproc [Hmc Hother]].
  unfold smramc_inv.
  rewrite <- Hmc.
  exact Hsmramc.
Qed.

Lemma update_cache_content_with_context_preserves_smrr_inv
      (a a':    Architecture Software)
      (pa:      PhysicalAddress)
      (val:     Value)
      (Hinv:    inv a)
      (Hin_smm: is_inside_smram pa -> is_in_smm (proc a))
      (Heqa':   a' = update_cache_content a pa (val, (smm_context a)))
  : smrr_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  apply update_cache_changes_only_cache in Heqa' as [Hproc [Hmc Hother]].
  unfold smrr_inv.
  rewrite <- Hproc.
  exact Hsmrr.
Qed.

Lemma update_cache_content_with_context_preserves_smram_code_inv
      (a a':    Architecture Software)
      (pa:      PhysicalAddress)
      (val:     Value)
      (Hinv:    inv a)
      (Hin_smm: is_inside_smram pa -> is_in_smm (proc a))
      (Heqa':   a' = update_cache_content a pa (val, (smm_context a)))
  : smram_code_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  apply update_cache_changes_only_cache in Heqa' as [Hproc [Hmc Hmem]].
  unfold smram_code_inv.
  unfold find_memory_content.
  rewrite <- Hmem.
  exact Hsmram.
Qed.

Lemma update_cache_content_with_context_preserves_ip_inv
      (a a':    Architecture Software)
      (pa:      PhysicalAddress)
      (val:     Value)
      (Hinv:    inv a)
      (Hin_smm: is_inside_smram pa -> is_in_smm (proc a))
      (Heqa':   a' = update_cache_content a pa (val, (smm_context a)))
  : ip_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  apply update_cache_changes_only_cache in Heqa' as [Hproc [Hmc Hmem]].
  unfold ip_inv.
  rewrite <- Hproc.
  rewrite <- (context_is_preserves a a' Hproc).
  exact Hip.
Qed.

Lemma update_cache_content_with_context_preserves_smbase_inv
      (a a':    Architecture Software)
      (pa:      PhysicalAddress)
      (val:     Value)
      (Hinv:    inv a)
      (Hin_smm: is_inside_smram pa -> is_in_smm (proc a))
      (Heqa':   a' = update_cache_content a pa (val, (smm_context a)))
  : smbase_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  apply update_cache_changes_only_cache in Heqa' as [Hproc [Hmc Hmem]].
  unfold smbase_inv.
  rewrite <- Hproc.
  exact Hsmbase.
Qed.

Lemma update_cache_content_with_context_preserves_cache_clean_inv
      (a a':    Architecture Software)
      (pa:      PhysicalAddress)
      (val:     Value)
      (Hinv:    inv a)
      (Hin_smm: is_inside_smram pa -> is_in_smm (proc a))
      (Heqa':   a' = update_cache_content a pa (val, (smm_context a)))
  : cache_clean_inv a'.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  unfold cache_clean_inv.
  intros pa' val' s' Hinside' Hcache_hit' Hfind'.
  assert (cache a' = global_update_in_cache (cache a) pa (val, smm_context a))
    as Heqcache
      by (rewrite Heqa'; reflexivity).
  unfold global_update_in_cache in Heqcache.
  destruct (cache_hit_dec (cache a) pa).
  + unfold update_in_cache in Heqcache.
    unfold find_cache_content in Hfind'.
    unfold find_in_cache in Hfind'.
    destruct cache_hit_dec; [| intuition ].
    rewrite Heqa' in Hfind'; simpl.
    destruct (eq_dec pa pa') as [Heq|Hneq].
    * apply eq_equal in Heq.
      rewrite <- Heq in Hfind'.
      unfold update_cache_content, global_update_in_cache in Hfind'.
      simpl in Hfind'.
      destruct cache_hit_dec; [| intuition ].
      unfold update_in_cache in Hfind'.
      rewrite add_1 in Hfind'.
      simpl in Hfind'.
      inversion Hfind'.
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
        unfold update_cache_content, global_update_in_cache, update_in_cache.
        simpl.
        destruct cache_hit_dec; [| intuition ].
        rewrite add_1.
        simpl.
        apply addr_eq_refl.
        apply (cache_hit_same_index_cache_miss (cache a') pa pa' Hcache_hit_pa Hneq Heqi).
      - simpl in Hfind'.
        unfold global_update_in_cache, update_in_cache in Hfind'.
        destruct cache_hit_dec; [| intuition].
        rewrite <- add_2 in Hfind' ; [| exact Hneqi ].
        assert (cache_hit (cache a) pa').
        apply (cache_hit_is_preserve_by_non_conflicted_update (cache a)
                                                              (cache a')
                                                              pa pa'
                                                              (val, smm_context a)
                                                              Hneqi).
        rewrite Heqa'.
        simpl.
        reflexivity.
        exact Hcache_hit'.
        inversion Hfind'.
        unfold cache_clean_inv in Hclean.
        apply (Hclean pa' val' s' Hinside' H).
        unfold find_cache_content, find_in_cache.
        destruct cache_hit_dec; [| intuition].
        rewrite H1.
        reflexivity.
  + unfold load_in_cache in Heqcache.
    unfold find_cache_content in Hfind'.
    unfold find_in_cache in Hfind'.
    destruct cache_hit_dec; [| intuition ].
    rewrite Heqa' in Hfind'; simpl in Hfind'.
    inversion Hfind'.
    destruct (eq_dec pa pa') as [Heqpa|Hneqpa].
    * apply eq_equal in Heqpa.
      rewrite <- Heqpa in H0.
      unfold global_update_in_cache in H0.
      destruct cache_hit_dec; [intuition|].
      unfold load_in_cache in H0.
      rewrite add_1 in H0.
      simpl in H0.
      inversion H0.
      rewrite <- Heqpa in Hinside'.
      apply Hin_smm in Hinside'.
      unfold smm_context.
      destruct is_in_smm_dec.
      reflexivity.
      apply n1 in Hinside'.
      destruct Hinside'.
    * destruct (eq_dec (phys_to_index pa) (phys_to_index pa')) as [Heqi|Hneqi].
      - assert (~ cache_hit (cache a') pa'); [| intuition ].
        assert (cache_hit (cache a') pa).
        unfold cache_hit.
        rewrite Heqa'.
        unfold update_cache_content, global_update_in_cache, load_in_cache.
        simpl.
        destruct cache_hit_dec; [intuition|].
        rewrite add_1.
        simpl.
        apply addr_eq_refl.
        apply (cache_hit_same_index_cache_miss (cache a') pa pa' H Hneqpa Heqi).
      - unfold update_cache_content, global_update_in_cache, load_in_cache in H0.
        destruct cache_hit_dec; [intuition|].
        rewrite <- add_2 in H0; [| exact Hneqi ].
        assert (cache_hit (cache a) pa').
        apply (cache_hit_is_preserve_by_non_conflicted_update (cache a)
                                                              (cache a')
                                                              pa pa'
                                                              (val, smm_context a)
                                                              Hneqi).
        rewrite Heqa'.
        simpl.
        reflexivity.
        exact Hcache_hit'.
        unfold cache_clean_inv in Hclean.
        apply (Hclean pa' val' s' Hinside' H).
        unfold find_cache_content, find_in_cache.
        destruct cache_hit_dec; [|intuition].
        rewrite H0.
        reflexivity.
Qed.

Lemma update_cache_content_with_context_preserves_inv
      (a a':    Architecture Software)
      (pa:      PhysicalAddress)
      (val:     Value)
      (Hinv:    inv a)
      (Hin_smm: is_inside_smram pa -> is_in_smm (proc a))
      (Heqa':   a' = update_cache_content a pa (val, (smm_context a)))
  : inv a'.
Proof.
  unfold inv.
  split; [| split; [| split; [| split; [| split]]]]; [
      eapply (update_cache_content_with_context_preserves_smramc_inv a a' pa val)
    | eapply (update_cache_content_with_context_preserves_smram_code_inv a a' pa val)
    | eapply (update_cache_content_with_context_preserves_smrr_inv a a' pa val)
    | eapply (update_cache_content_with_context_preserves_cache_clean_inv a a' pa val)
    | eapply (update_cache_content_with_context_preserves_ip_inv a a' pa val)
    | eapply (update_cache_content_with_context_preserves_smbase_inv a a' pa val) ]; trivial.
Qed.

Lemma load_then_update_cache_with_context_preserves_inv
      (a a'':   Architecture Software)
      (pa:      PhysicalAddress)
      (val:     Value)
      (Hinv:    inv a)
      (Hin_smm: is_inside_smram pa -> is_in_smm (proc a))
      (Heqa'':  a'' = update_cache_content (load_in_cache_from_memory a pa) pa (val, smm_context a))
  : inv a''.
Proof.
  remember (load_in_cache_from_memory a pa) as a'.
  assert (inv a')
    as Hinv'
      by (apply (load_in_cache_from_memory_preserves_inv a a' pa Hinv Hin_smm Heqa')).
  assert (proc a = proc a').
  apply load_in_cache_from_memory_changes_only_mem_and_cache in Heqa' as [Hproc _H].
  exact Hproc.
  rewrite H in Hin_smm.
  rewrite (context_is_preserves a a' H) in Heqa''.
  apply (update_cache_content_with_context_preserves_inv a' a'' pa val Hinv' Hin_smm Heqa'').
Qed.
