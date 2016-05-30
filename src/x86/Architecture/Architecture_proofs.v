Require Import SpecCert.x86.Architecture.ProcessorUnit.
Require Import SpecCert.x86.Architecture.MemoryController.
Require Import SpecCert.x86.Architecture.Architecture_rec.
Require Import SpecCert.x86.Architecture.Architecture_func.
Require Import SpecCert.Memory.
Require Import SpecCert.Address.
Require Import SpecCert.Cache.

Lemma update_proc_changes_only_proc {S :Set}:
  forall a a':Architecture S,
  forall p   :ProcessorUnit,
    a' = update_proc a p
    -> memory_controller a = memory_controller a'
      /\ memory a = memory a'
      /\ cache a = cache a'.
Proof.
  intros a a' p Hupdate.
  unfold update_proc in Hupdate.
  rewrite Hupdate.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma update_proc_is_proc {S :Set}:
  forall a a' :Architecture S,
  forall p    :ProcessorUnit,
    a' = update_proc a p -> proc a' = p.
Proof.
  intros a a' p Hupdate.
  rewrite Hupdate.
  unfold proc, update_proc.
  reflexivity.
Qed.

Lemma update_memory_controller_changes_only_memory_controller {S :Set}:
  forall a a':Architecture S,
  forall mc:MemoryController,
    a' = update_memory_controller a mc
    -> proc a = proc a'
      /\ memory a = memory a'
      /\ cache a = cache a'.
Proof.
  intros a a' p Hupdate.
  unfold update_memory_controller in Hupdate.
  rewrite Hupdate.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma update_memory_controller_is_memory_controller {S :Set}:
  forall a a' :Architecture S,
  forall mc   :MemoryController,
    a' = update_memory_controller a mc
    -> memory_controller a' = mc.
Proof.
  intros a a' mc Hupdate.
  rewrite Hupdate.
  unfold memory_controller, update_memory_controller.
  reflexivity.
Qed.

Lemma update_memory_changes_only_memory {S :Set}:
  forall a a' :Architecture S,
  forall ha   :HardwareAddress,
  forall c    :S,
    a' = update_memory_content a ha c
    -> memory_controller a = memory_controller a'
      /\ proc a = proc a'
      /\ cache a = cache a'.
Proof.
  intros a a' ha c Hupdate; repeat split;
  unfold update_memory_content in Hupdate;
  rewrite Hupdate;
  unfold memory_controller, proc; reflexivity.
Qed.

Lemma update_ha_in_memory_changes_only_ha {S :Set}:
  forall a      :Architecture S,
  forall ha ha' :HardwareAddress,
  forall c      :S,
    ~ hardware_addr_eq ha ha'
    -> find_memory_content a ha' = find_memory_content (update_memory_content a ha c) ha'.
Proof.
  intros a ha ha' c Hdiff.
  apply update_memory_2.
  trivial.
Qed.

Lemma update_ha_in_memory_is_ha {S :Set}:
  forall a  :Architecture S,
  forall ha :HardwareAddress,
  forall c:S,
    find_memory_content (update_memory_content a ha c) ha = c.
Proof.
  intros a ha c.
  unfold find_memory_content.
  apply update_memory_1.
Qed.

Lemma update_cache_content_is_find {S :Set}:
  forall a  :Architecture S,
  forall pa :PhysicalAddress,
  forall c  :S,
        find_cache_content (update_cache_content a pa c) pa = Some c.
Proof.
  intros a pa c.
  unfold find_cache_content, update_cache_content.
  simpl.
  apply update_is_find_in_cache.
Qed.

Lemma update_cache_changes_only_cache {S :Set}:
  forall a a' :Architecture S,
  forall pa   :PhysicalAddress,
  forall c    :S,
    a' = update_cache_content a pa c
    -> proc a = proc a'
      /\ memory_controller a = memory_controller a'
      /\ memory a = memory a'.
Proof.
  intros a a' pa c Hupdate.
  unfold update_cache_content in Hupdate.
  rewrite Hupdate.
  simpl.
  intuition.
Qed.

Lemma update_ha_in_memory_changes_only_memory {S :Set}:
  forall a a' :Architecture S,
  forall ha   :HardwareAddress,
  forall c    :S,
    a' = update_memory_content a ha c
    -> proc a = proc a'
      /\ memory_controller a = memory_controller a'
      /\ cache a = cache a'.
Proof.
  intros a a' ha c Hupdate.
  unfold update_memory_content in Hupdate.
  rewrite Hupdate.
  simpl.
  intuition.
Qed.

Lemma load_in_cache_from_memory_changes_only_mem_and_cache {S :Set}:
  forall a a' :Architecture S,
  forall pa   :PhysicalAddress,
    a' = load_in_cache_from_memory a pa
    -> proc a = proc a'
      /\ memory_controller a = memory_controller a'.
Proof.
  intros a a' pa Hload.
  unfold load_in_cache_from_memory in Hload.
  destruct (cache_location_is_dirty_dec (cache a) pa).
  + apply update_cache_changes_only_cache in Hload.
    destruct Hload as [Hproc [Hmc Hmem]].
    remember (update_memory_content a
                                    (phys_to_hard a (cache_location_address (cache a) pa))
                                    (find_in_cache_location (cache a) pa))
      as a'' eqn:Ha''.
    apply update_ha_in_memory_changes_only_memory in Ha''.
    destruct Ha'' as [Hproc' [Hmc' Hcache']].
    rewrite <- Hproc' in Hproc.
    rewrite <- Hmc' in Hmc.
    intuition.
  + apply update_cache_changes_only_cache in Hload.
    destruct Hload as [Hproc [Hmc Hmem]].
    intuition.
Qed.

Lemma update_cache_content_changes_only_index {S:Set}:
  forall pa pa' :PhysicalAddress,
  forall a      :Architecture S,
  forall c      :S,
    ~ index_eq (phys_to_index pa) (phys_to_index pa')
    -> find_cache_content (update_cache_content a pa c) pa'
      = find_cache_content a pa'.
Proof.
  intros pa pa' a c Hneq.
  unfold find_cache_content, update_cache_content.
  unfold find_in_cache.
  unfold global_update_in_cache.
  unfold update_in_cache.
  unfold load_in_cache.
  simpl.
  repeat destruct cache_hit_dec.
  rewrite <- _IndexMap.add_2; trivial.
  assert (~ cache_hit 
            (_IndexMap.add_in_map (cache a) (phys_to_index pa)
                                  {| dirty := true; content := c; tag := pa |}) pa'
         ); [
    | intuition
    ].
  clear c0.
  unfold not; intro Hhit'.
  unfold cache_hit in Hhit'.
  rewrite <- _IndexMap.add_2 with (k:=phys_to_index pa)
                                   (c:=
                                      {|
                                        dirty := true;
                                        content := c;
                                        tag := pa
                                      |}
                                   )
    in Hhit'.
  unfold cache_hit in n.
  intuition.
  trivial.
  rewrite <- _IndexMap.add_2; trivial.
  assert (~ cache_hit 
            (_IndexMap.add_in_map (cache a) (phys_to_index pa)
                                  {| dirty := false; content := c; tag := pa |}) pa'
         ); [
    | intuition
    ].
  clear c0.
  unfold not; intro Hhit'.
  unfold cache_hit in Hhit'.
  rewrite <- _IndexMap.add_2 with (k:=phys_to_index pa)
                                   (c:=
                                      {|
                                        dirty := false;
                                        content := c;
                                        tag := pa
                                      |}
                                   )
    in Hhit'.
  unfold cache_hit in n.
  intuition.
  trivial.
  assert (cache_hit 
            (_IndexMap.add_in_map (cache a) (phys_to_index pa)
                                  {| dirty := true; content := c; tag := pa |}) pa'
         ); [
    | intuition
    ].
  unfold cache_hit.
  rewrite <- _IndexMap.add_2.
  unfold cache_hit in c1.
  apply addr_eq_eq in c1.
  rewrite <- c1.
  apply addr_eq_refl.
  trivial.
  reflexivity.
  assert (cache_hit 
            (_IndexMap.add_in_map (cache a) (phys_to_index pa)
                                  {| dirty := false; content := c; tag := pa |}) pa'
         ); [
    | intuition
    ].
  unfold cache_hit.
  rewrite <- _IndexMap.add_2.
  unfold cache_hit in c0.
  apply addr_eq_eq in c0.
  rewrite <- c0.
  apply addr_eq_refl.
  trivial.
  reflexivity.
Qed.

Lemma update_same_index_is_find_in_cache {S :Set}:
  forall a      :Architecture S,
  forall pa pa' :PhysicalAddress,
  forall c      :S,
    index_eq (phys_to_index pa) (phys_to_index pa')
    -> find_cache_location_content (update_cache_content a pa c) pa' = c.
Proof.
  intros a pa pa' c Heq.
  unfold find_cache_location_content, update_cache_content.
  simpl.
  apply index_eq_eq in Heq.
  unfold find_in_cache_location, global_update_in_cache.
  repeat destruct cache_hit_dec.
  + unfold update_in_cache.
    rewrite Heq.
    rewrite _IndexMap.add_1.
    simpl.
    reflexivity.
  + unfold load_in_cache.
    rewrite Heq.
    rewrite _IndexMap.add_1.
    simpl.
    reflexivity.
Qed.