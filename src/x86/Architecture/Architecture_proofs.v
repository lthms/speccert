Require Import SpecCert.Address.
Require Import SpecCert.Cache.
Require Import SpecCert.Equality.
Require Import SpecCert.Map.
Require Import SpecCert.Memory.
Require Import SpecCert.x86.Architecture.Architecture_func.
Require Import SpecCert.x86.Architecture.Architecture_rec.
Require Import SpecCert.x86.Architecture.MemoryController.
Require Import SpecCert.x86.Architecture.ProcessorUnit.
Require Import SpecCert.x86.Value.

Lemma update_proc_changes_only_proc
      {Label: Type}
      (a a':  Architecture Label)
      (p:     ProcessorUnit)
      (Heqa': a' = update_proc a p)
  : memory_controller a = memory_controller a'
    /\ memory a = memory a'
    /\ cache a = cache a'.
Proof.
  unfold update_proc in Heqa'.
  rewrite Heqa'.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma update_proc_is_proc
      {Label: Type}
      (a a':  Architecture Label)
      (p:     ProcessorUnit)
      (Heqa': a' = update_proc a p)
  : proc a' = p.
Proof.
  rewrite Heqa'.
  unfold proc, update_proc.
  reflexivity.
Qed.

Lemma update_memory_controller_changes_only_memory_controller
      {Label: Type}
      (a a':  Architecture Label)
      (mc:    MemoryController)
      (Heqa': a' = update_memory_controller a mc)
  : proc a = proc a'
    /\ memory a = memory a'
    /\ cache a = cache a'.
Proof.
  unfold update_memory_controller in Heqa'.
  rewrite Heqa'.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma update_memory_controller_is_memory_controller
      {Label: Type}
      (a a':  Architecture Label)
      (mc:    MemoryController)
      (Heqa': a' = update_memory_controller a mc)
  : memory_controller a' = mc.
Proof.
  rewrite Heqa'.
  unfold memory_controller, update_memory_controller.
  reflexivity.
Qed.

Lemma update_memory_changes_only_memory
      {Label: Type}
      (a a':  Architecture Label)
      (ha:    HardwareAddress)
      (c:     (Value*Label))
      (Heqa': a' = update_memory_content a ha c)
  : memory_controller a = memory_controller a'
    /\ proc a = proc a'
    /\ cache a = cache a'.
Proof.
  repeat split;
    unfold update_memory_content in Heqa';
    rewrite Heqa';
    unfold memory_controller, proc; reflexivity.
Qed.

Lemma update_ha_in_memory_changes_only_ha
      {Label: Type}
      (a:     Architecture Label)
      (ha ha': HardwareAddress)
      (c:      (Value*Label))
      (Hdiff:  ~ eq ha ha')
  : find_memory_content a ha' = find_memory_content (update_memory_content a ha c) ha'.
Proof.
  apply update_memory_2.
  trivial.
Qed.

Lemma update_ha_in_memory_is_ha
      {Label: Type}
      (a:     Architecture Label)
      (ha:    HardwareAddress)
      (c:      (Value*Label))
  : find_memory_content (update_memory_content a ha c) ha = c.
Proof.
  unfold find_memory_content.
  apply update_memory_1.
Qed.

Lemma update_cache_content_is_find
      {Label: Type}
      (a:     Architecture Label)
      (pa:    PhysicalAddress)
      (c:      (Value*Label))
  : find_cache_content (update_cache_content a pa c) pa = Some c.
Proof.
  unfold find_cache_content, update_cache_content.
  simpl.
  apply update_is_find_in_cache.
Qed.

Lemma update_cache_changes_only_cache
      {Label: Type}
      (a a':  Architecture Label)
      (pa:    PhysicalAddress)
      (c:      (Value*Label))
      (Heqa': a' = update_cache_content a pa c)
  : proc a = proc a'
    /\ memory_controller a = memory_controller a'
    /\ memory a = memory a'.
Proof.
  unfold update_cache_content in Heqa'.
  rewrite Heqa'.
  simpl.
  intuition.
Qed.

Lemma update_ha_in_memory_changes_only_memory
      {Label: Type}
      (a a':  Architecture Label)
      (ha:    HardwareAddress)
      (c:      (Value*Label))
      (Heqa': a' = update_memory_content a ha c)
  : proc a = proc a'
    /\ memory_controller a = memory_controller a'
    /\ cache a = cache a'.
Proof.
  unfold update_memory_content in Heqa'.
  rewrite Heqa'.
  simpl.
  intuition.
Qed.

Lemma load_in_cache_from_memory_changes_only_mem_and_cache
      {Label: Type}
      (a a':  Architecture Label)
      (pa:    PhysicalAddress)
      (Heqa': a' = load_in_cache_from_memory a pa)
  : proc a = proc a'
    /\ memory_controller a = memory_controller a'.
Proof.
  unfold load_in_cache_from_memory in Heqa'.
  destruct (cache_location_is_dirty_dec (cache a) pa).
  + apply update_cache_changes_only_cache in Heqa'.
    destruct Heqa' as [Hproc [Hmc Hmem]].
    remember (update_memory_content a
                                    (phys_to_hard a (cache_location_address (cache a) pa))
                                    (find_in_cache_location (cache a) pa))
      as a'' eqn:Ha''.
    apply update_ha_in_memory_changes_only_memory in Ha''.
    destruct Ha'' as [Hproc' [Hmc' Hcache']].
    rewrite <- Hproc' in Hproc.
    rewrite <- Hmc' in Hmc.
    intuition.
  + apply update_cache_changes_only_cache in Heqa'.
    destruct Heqa' as [Hproc [Hmc Hmem]].
    intuition.
Qed.

Lemma update_cache_content_changes_only_index
      {Label:  Type}
      (a:      Architecture Label)
      (pa pa': PhysicalAddress)
      (c:      (Value*Label))
      (Hneq:   ~ eq (phys_to_index pa) (phys_to_index pa'))
  : find_cache_content (update_cache_content a pa c) pa'
    = find_cache_content a pa'.
Proof.
  unfold find_cache_content, update_cache_content.
  unfold find_in_cache.
  unfold global_update_in_cache.
  unfold update_in_cache.
  unfold load_in_cache.
  simpl.
  repeat destruct cache_hit_dec.
  rewrite <- add_2; trivial.
  assert (~ cache_hit
            (add_in_map (cache a) (phys_to_index pa)
                                  {| dirty := true; content := c; tag := pa |}) pa'
         ); [
    | intuition
    ].
  clear c0.
  unfold not; intro Hhit'.
  unfold cache_hit in Hhit'.
  rewrite <- add_2 with (k:=phys_to_index pa)
                                   (v:=
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
  rewrite <- add_2; trivial.
  assert (~ cache_hit
            (add_in_map (cache a) (phys_to_index pa)
                                  {| dirty := false; content := c; tag := pa |}) pa'
         ); [
    | intuition
    ].
  unfold not; intro Hhit'.
  unfold cache_hit in Hhit'.
  rewrite <- add_2 with (k:=phys_to_index pa)
                                   (v:=
                                      {|
                                        dirty := false;
                                        content := c;
                                        tag := pa
                                      |}
                                   )
    in Hhit'.
  intuition.
  trivial.
  assert (cache_hit
            (add_in_map (cache a) (phys_to_index pa)
                                  {| dirty := true; content := c; tag := pa |}) pa'
         ); [
    | intuition
    ].
  unfold cache_hit.
  rewrite <- add_2.
  unfold cache_hit in c1.
  apply eq_equal in c1.
  rewrite <- c1.
  apply eq_refl.
  trivial.
  reflexivity.
  assert (cache_hit
            (add_in_map (cache a) (phys_to_index pa)
                                  {| dirty := false; content := c; tag := pa |}) pa'
         ); [
    | intuition
    ].
  unfold cache_hit.
  rewrite <- add_2.
  unfold cache_hit in c0.
  apply eq_equal in c0.
  rewrite <- c0.
  apply eq_refl.
  trivial.
  reflexivity.
Qed.

Lemma update_same_index_is_find_in_cache
      {Label:  Type}
      (a:      Architecture Label)
      (pa pa': PhysicalAddress)
      (c:      (Value*Label))
      (Heq:    eq (phys_to_index pa) (phys_to_index pa'))
  : find_cache_location_content (update_cache_content a pa c) pa' = c.
Proof.
  unfold find_cache_location_content, update_cache_content.
  simpl.
  apply eq_equal in Heq.
  unfold find_in_cache_location, global_update_in_cache.
  repeat destruct cache_hit_dec.
  + unfold update_in_cache.
    rewrite Heq.
    rewrite add_1.
    simpl.
    reflexivity.
  + unfold load_in_cache.
    rewrite Heq.
    rewrite add_1.
    simpl.
    reflexivity.
Qed.