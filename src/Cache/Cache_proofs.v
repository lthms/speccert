Require Import SpecCert.Cache.Cache_def.
Require Import SpecCert.Cache.Cache_prop.
Require Import SpecCert.Cache.Cache_func.
Require Import SpecCert.Address.
Require Import SpecCert.Map.
Require Import SpecCert.Equality.

Lemma update_in_cache_cache_hit
      {S:      Type}
      (cache : Cache S)
      (pa:     PhysicalAddress)
      (owner:  S)
      (h:      cache_hit cache pa)
  : cache_hit (update_in_cache cache pa owner h) pa.
Proof.
  unfold cache_hit.
  unfold update_in_cache.
  rewrite add_1.
  apply eq_refl.
Qed.

Lemma load_in_cache_cache_hit
      {S:     Type}
      (cache: Cache S)
      (pa:    PhysicalAddress)
      (owner: S)
      (h:     ~cache_hit cache pa)
  : cache_hit (load_in_cache cache pa owner h) pa.
Proof.
  unfold cache_hit.
  unfold load_in_cache.
  rewrite add_1.
  apply eq_refl.
Qed.

Lemma global_update_in_cache_cache_hit
      {S:     Type}
      (cache: Cache S)
      (pa:    PhysicalAddress)
      (owner: S)
  : cache_hit (global_update_in_cache cache pa owner) pa.
Proof.
  unfold global_update_in_cache.
  destruct (cache_hit_dec cache pa).
  + apply update_in_cache_cache_hit.
  + apply load_in_cache_cache_hit.
Qed.

Lemma update_is_find_in_cache
      {S:     Set}
      (cache: Cache S)
      (pa:    PhysicalAddress)
      (cont: S)
  : find_in_cache (global_update_in_cache cache pa cont) pa = Some cont.
Proof.
  unfold find_in_cache, global_update_in_cache.
  destruct (cache_hit_dec cache pa).
  + destruct cache_hit_dec.
    * unfold update_in_cache.
      rewrite (add_1 cache (phys_to_index pa) ({| dirty := true
                                                ; content := cont
                                                ; tag := pa |})).
      reflexivity.
    * exfalso.
      unfold not in n.
      assert (cache_hit (update_in_cache cache pa cont c) pa) by (apply update_in_cache_cache_hit).
      apply n in H.
      trivial.
  + destruct cache_hit_dec.
    * unfold load_in_cache.
      rewrite add_1.
      simpl.
      reflexivity.
    * exfalso.
      unfold not in n0.
      assert (cache_hit (load_in_cache cache pa cont n) pa) by (apply load_in_cache_cache_hit).
      apply n0 in H.
      trivial.
Qed.

Lemma same_index_cache_hit_same_address
      {S:      Set}
      (pa pa': PhysicalAddress)
      (cache:  Cache S)
  : eq (phys_to_index pa) (phys_to_index pa')
    -> cache_hit cache pa
    -> cache_hit cache pa'
    -> eq pa pa'.
Proof.
  intros Heq Hhit Hhit'.
  apply equal_eq.
  apply eq_equal in Heq.
  unfold cache_hit in *.
  rewrite Heq in Hhit.
  case_eq (find_in_map cache (phys_to_index pa')).
  intros.
  rewrite H in Hhit.
  rewrite H in Hhit'.
  apply eq_equal in Hhit.
  apply eq_equal in Hhit'.
  rewrite Hhit.
  rewrite Hhit'.
  reflexivity.
Qed.

Lemma cache_hit_is_preserve_by_non_conflicted_update
      {S:            Set}
      (cache cache': Cache S)
      (pa pa':       PhysicalAddress)
      (c:            S)
  : ~eq (phys_to_index pa) (phys_to_index pa')
    -> cache' = global_update_in_cache cache pa c
    -> cache_hit cache' pa'
    -> cache_hit cache pa'.
Proof.
  intros Hind Hup Hhit.
  unfold global_update_in_cache in Hup.
  unfold cache_hit.
  destruct cache_hit_dec.
  + unfold update_in_cache in Hup.
    rewrite (add_2 cache
                   (phys_to_index pa)
                   (phys_to_index pa')
                   ({| dirty := true
                     ; content := c
                     ; tag := pa |})).
    * rewrite <- Hup.
      trivial.
    * trivial.
  + unfold load_in_cache in Hup.
    rewrite (add_2 cache
                   (phys_to_index pa)
                   (phys_to_index pa')
                   ({| dirty := false
                     ; content := c
                     ; tag := pa |})).
    * rewrite <- Hup.
      trivial.
    * trivial.
Qed.

Lemma global_update_not_cache_preserve
      {S:            Set}
      (cache cache': Cache S)
      (pa pa':       PhysicalAddress)
      (c:            S)
  : ~cache_hit cache pa'
    -> ~eq pa pa'
    -> ~eq (phys_to_index pa) (phys_to_index pa')
    -> cache' = global_update_in_cache cache pa c
    -> ~cache_hit cache' pa'.
Proof.
  intros Hhit Haddr Hind Heq.
  unfold not; intro Hhit'.
  unfold global_update_in_cache in Heq.
  destruct cache_hit_dec in Heq.
  + unfold update_in_cache in Heq.
    rewrite Heq in Hhit'.
    unfold cache_hit in Hhit'.
    remember (
        find_in_map
          (add_in_map cache
                      (phys_to_index pa)
                      {| dirty := true; content := c; tag := pa |})
          (phys_to_index pa')
      ) as cc.
    rewrite <- (add_2 cache
                      (phys_to_index pa)
                      (phys_to_index pa')
                      ({| dirty := true
                        ; content := c
                        ; tag := pa
                        |})) in Heqcc.
    rewrite Heqcc in Hhit'.
    unfold cache_hit in Hhit.
    intuition.
    trivial.
  + unfold load_in_cache in Heq.
    rewrite Heq in Hhit'.
    unfold cache_hit in Hhit'.
    remember (
        find_in_map
          (add_in_map cache
                      (phys_to_index pa)
                      {| dirty := false; content := c; tag := pa |})
          (phys_to_index pa')
      ) as cc.
    rewrite <- (add_2 cache
                      (phys_to_index pa)
                      (phys_to_index pa')
                      ({| dirty := false
                        ; content := c
                        ; tag := pa |}))
      in Heqcc.
    rewrite Heqcc in Hhit'.
    unfold cache_hit in Hhit.
    intuition.
    trivial.
Qed.

Lemma global_update_not_cache_hit {S :Set}:
  forall cache cache' :Cache S,
  forall pa pa'       :PhysicalAddress,
  forall o            :S,
    ~ eq pa pa'
    -> eq (phys_to_index pa) (phys_to_index pa')
    -> cache' = global_update_in_cache cache pa o
    -> ~cache_hit cache' pa'.
Proof.
  intros cache cache' pa pa' c Hdiff Heq Hc.
  unfold not; intro Hexf.
  rewrite Hc in Hexf.
  apply eq_equal in Heq.
  unfold global_update_in_cache in Hexf.
  destruct cache_hit_dec.
  + unfold update_in_cache in Hexf.
    rewrite Heq in Hexf.
    unfold cache_hit in Hexf.
    remember (find_in_map
                (add_in_map cache
                            (phys_to_index pa')
                            {| dirty := true; content := c; tag := pa |})
                (phys_to_index pa')
             ) as cache''.
    rewrite add_1 in Heqcache''.
    rewrite Heqcache'' in Hexf.
    simpl in Hexf.
    apply addr_eq_sym in Hexf.
    apply Hdiff in Hexf.
    exact Hexf.
  + unfold load_in_cache in Hexf.
    rewrite Heq in Hexf.
    unfold cache_hit in Hexf.
    remember (find_in_map
                (add_in_map cache
                            (phys_to_index pa')
                            {| dirty := false; content := c; tag := pa |})
                (phys_to_index pa')
             ) as cache''.
    rewrite add_1 in Heqcache''.
    rewrite Heqcache'' in Hexf.
    apply eq_sym in Hexf.
    apply Hdiff in Hexf.
    exact Hexf.
Qed.

Lemma cache_stays_well_formed {S :Set}:
  forall cache cache' :Cache S,
  forall pa           :PhysicalAddress,
  forall o            :S,
    cache_is_well_formed cache
    -> cache' = global_update_in_cache cache pa o
    -> cache_is_well_formed cache'.
Proof.
  unfold cache_is_well_formed, global_update_in_cache.
  intros cache cache' pa c Hwf Hup pa'.
  destruct cache_hit_dec;
    [
      unfold update_in_cache in Hup
    | unfold load_in_cache in Hup
    ];
    destruct (eq_dec (phys_to_index pa) (phys_to_index pa')).
  + rewrite Hup.
    remember (phys_to_index pa') as i'.
    remember (find_in_map
                (add_in_map cache
                            (phys_to_index pa)
                            {| dirty := true; content := c; tag := pa |}) i')
      as cc.
    apply eq_equal in e.
    rewrite e in Heqcc.
    rewrite add_1 in Heqcc.
    rewrite Heqcc.
    simpl.
    rewrite e.
    trivial.
  + rewrite Hup.
    remember (phys_to_index pa') as i'.
    remember (find_in_map
                (add_in_map cache
                            (phys_to_index pa)
                            {| dirty := true; content := c; tag := pa |}) i')
      as cc.
    rewrite Heqi' in Heqcc.
    rewrite <- (add_2 cache
                      (phys_to_index pa)
                      (phys_to_index pa')
                      ({| dirty := true
                        ; content := c
                        ; tag := pa |}))
      in Heqcc; trivial.
    rewrite Heqcc.
    rewrite <- Hwf with (pa:= pa').
    trivial.
    rewrite <- Heqi'.
    trivial.
  + rewrite Hup.
    remember (phys_to_index pa') as i'.
    remember (find_in_map
                (add_in_map cache
                               (phys_to_index pa)
                               {| dirty := false; content := c; tag := pa |}) i')
      as cc.
    apply eq_equal in e.
    rewrite <- e in Heqcc.
    rewrite add_1 in Heqcc.
    rewrite Heqcc.
    simpl.
    symmetry.
    trivial.
  + rewrite Hup.
    remember (phys_to_index pa') as i'.
    remember (find_in_map
                (add_in_map cache
                            (phys_to_index pa)
                            {| dirty := false; content := c; tag := pa |}) i')
      as cc.
    rewrite Heqi' in Heqcc.
    rewrite <- (add_2 cache
                      (phys_to_index pa)
                      (phys_to_index pa')
                      {| dirty := false
                       ; content := c
                       ; tag := pa |})
      in Heqcc; trivial.
    rewrite Heqcc.
    rewrite <- Hwf with (pa:= pa').
    trivial.
    rewrite <- Heqi'.
    trivial.
Qed.

Lemma same_tag_means_same_index {S :Set}:
  forall cache  :Cache S,
  forall pa pa' :PhysicalAddress,
    cache_is_well_formed cache
    -> tag (find_in_map cache (phys_to_index pa))
      = tag (find_in_map cache (phys_to_index pa'))
    -> (phys_to_index pa) = (phys_to_index pa').
Proof.
  intros cache pa pa' Hwf Heq.
  unfold cache_is_well_formed in Hwf.
  rewrite Hwf with (pa:=pa').
  rewrite <- Heq.
  rewrite <- Hwf with (pa:=pa); reflexivity.
Qed.

Lemma same_index_implies_same_tag {S :Set}:
  forall cache  :Cache S,
  forall pa pa' :PhysicalAddress,
    phys_to_index pa = phys_to_index pa'
    -> tag (find_in_map cache (phys_to_index pa))
      = tag (find_in_map cache (phys_to_index pa')).
Proof.
  intros cache pa pa' Hphys.
  rewrite Hphys.
  trivial.
Qed.

Lemma cache_hit_cache_location_address {S :Set}:
  forall cache :Cache S,
  forall pa    :PhysicalAddress,
    cache_is_well_formed cache
    -> cache_hit cache (cache_location_address cache pa).
Proof.
  unfold cache_hit, cache_location_address.
  intros cache pa Hwf.
  rewrite <- Hwf with (pa:=pa).
  apply equal_eq.
  reflexivity.
Qed.

Lemma find_in_cache_cache_location {S :Set}:
  forall cache :Cache S,
  forall pa    :PhysicalAddress,
  forall o:S,
    cache_is_well_formed cache
    -> find_in_cache_location cache pa = o
    -> find_in_cache cache (cache_location_address cache pa) = Some o.
Proof.
  unfold find_in_cache_location, find_in_cache, cache_location_address.
  intros cache pa c Hwf Hcont.
  assert (cache_is_well_formed cache); trivial.
  apply (cache_hit_cache_location_address cache pa) in H.
  destruct cache_hit_dec; try intuition.
  remember (
      tag (find_in_map cache (phys_to_index pa))
    ) as pa'.
  remember (
      phys_to_index pa'
    ) as i'.
  rewrite Heqpa' in Heqi'.
  rewrite <- Hwf with (pa:=pa) in Heqi'.
  rewrite Heqi'.
  rewrite Hcont.
  reflexivity.
Qed.

Lemma cache_hit_cache_location_cache_find {S :Set}:
  forall cache :Cache S,
  forall pa    :PhysicalAddress,
    cache_hit cache pa
    -> pa = cache_location_address cache pa.
Proof.
  intros cache pa Hhit.
  unfold cache_location_address.
  unfold cache_hit.
  unfold cache_hit in Hhit.
  apply eq_equal in Hhit.
  rewrite <- Hhit.
  reflexivity.
Qed.

Lemma cache_location_cache_location {S:Set}:
  forall cache  :Cache S,
  forall pa pa' :PhysicalAddress,
    cache_is_well_formed cache
    -> pa' = cache_location_address cache pa
    -> find_in_cache_location cache pa = find_in_cache_location cache pa'.
Proof.
  intros cache pa pa' Hwf Hrewrite.
  rewrite Hrewrite.
  assert (cache_hit cache (cache_location_address cache pa)).
  apply cache_hit_cache_location_address.
  apply Hwf.
  unfold find_in_cache_location.
  unfold cache_location_address.
  rewrite <- Hwf.
  reflexivity.
Qed.

Lemma cache_hit_same_index_cache_miss {S :Set}:
  forall c      :Cache S,
  forall pa pa' : PhysicalAddress,
    cache_hit c pa
    -> ~ eq pa pa'
    -> eq (phys_to_index pa) (phys_to_index pa')
    -> ~ cache_hit c pa'.
Proof.
  intros c pa pa' Hcache_hit Haddr Hindex Hcache_hit'.
  unfold cache_hit in *.
  apply Haddr.
  apply eq_equal in Hcache_hit.
  apply eq_equal in Hcache_hit'.
  apply eq_equal in Hindex.
  rewrite Hindex in *.
  rewrite <- Hcache_hit in Hcache_hit'.
  symmetry in Hcache_hit'.
  apply equal_eq in Hcache_hit'.
  exact Hcache_hit'.
Qed.
