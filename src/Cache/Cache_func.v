Require Import SpecCert.Cache.Cache_def.
Require Import SpecCert.Cache.Cache_prop.
Require Import SpecCert.Address.
Require Import SpecCert.Map.

Definition load_in_cache
           {S     :Type}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           (owner :S)
           (h      : ~cache_hit cache pa)
           :Cache S :=
  let o' := {| dirty   := false
             ; content := owner
             ; tag     := pa |} in
  add_in_map cache (phys_to_index pa) o'.

Definition update_in_cache
           {S     :Type}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           (owner :S)
           (h     :cache_hit cache pa)
           :Cache S :=
  let o' := {| dirty := true
             ; content := owner
             ; tag := pa |} in
  add_in_map cache (phys_to_index pa) o'.

Program Definition global_update_in_cache
           {S     :Type}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           (owner :S)
           :Cache S :=
  if cache_hit_dec cache pa then
    update_in_cache cache pa owner _
  else
    load_in_cache cache pa owner _.

Definition find_in_cache
           {S     :Type}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           :option S :=
  if cache_hit_dec cache pa then
    Some (content (find_in_map cache (phys_to_index pa)))
  else
    None.

Definition find_in_cache_location
           {S     :Type}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           :S :=
  content (find_in_map cache (phys_to_index pa)).

Definition cache_location_address
           {S     :Type}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           :PhysicalAddress :=
  tag (find_in_map cache (phys_to_index pa)).