Require Import SpecCert.Cache.Cache_def.
Require Import SpecCert.Cache.Cache_prop.
Require Import SpecCert.Address.

Definition load_in_cache
           {S     :Set}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           (owner :S)
           (h      : ~cache_hit cache pa)
           :Cache S :=
  let o' := {| dirty   := false
             ; content := owner
             ; tag     := pa |} in
  _IndexMap.add_in_map cache (phys_to_index pa) o'.

Definition update_in_cache
           {S     :Set}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           (owner :S)
           (h     :cache_hit cache pa)
           :Cache S :=
  let o' := {| dirty := true
             ; content := owner
             ; tag := pa |} in
  _IndexMap.add_in_map cache (phys_to_index pa) o'.

Program Definition global_update_in_cache
           {S     :Set}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           (owner :S)
           :Cache S :=
  if cache_hit_dec cache pa then
    update_in_cache cache pa owner _
  else
    load_in_cache cache pa owner _.

Definition find_in_cache
           {S     :Set}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           :option S :=
  if cache_hit_dec cache pa then
    Some (content (_IndexMap.find_in_map cache (phys_to_index pa)))
  else
    None.

Definition find_in_cache_location
           {S     :Set}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           :S :=
  content (_IndexMap.find_in_map cache (phys_to_index pa)).

Definition cache_location_address
           {S     :Set}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           :PhysicalAddress :=
  tag (_IndexMap.find_in_map cache (phys_to_index pa)).