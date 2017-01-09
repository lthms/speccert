Require Import Coq.Bool.Bool.

Require Import SpecCert.Equality.
Require Import SpecCert.Cache.Cache_def.
Require Import SpecCert.Address.
Require Import SpecCert.Utils.
Require Import SpecCert.Map.

Definition cache_hit
           {S     :Type}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           :Prop :=
  eq pa (tag (find_in_map cache (phys_to_index pa))).

Definition cache_hit_dec
           {S     :Type}
           (cache :Cache S)
           (pa:PhysicalAddress)
           : { cache_hit cache pa } + { ~ cache_hit cache pa } :=
  eq_dec pa (tag (find_in_map cache (phys_to_index pa))).

Definition cache_location_is_dirty
           {S     :Type}
           (cache :Cache S)
           (pa    :PhysicalAddress) :=
  dirty (find_in_map cache (phys_to_index pa)) = true.

Definition cache_location_is_dirty_dec
           {S     :Type}
           (cache :Cache S)
           (pa    :PhysicalAddress)
  : { cache_location_is_dirty cache pa } + { ~ cache_location_is_dirty cache pa } :=
  bool_dec (dirty (find_in_map cache (phys_to_index pa))) true.

Definition cache_is_well_formed
           {S     :Type}
           (cache :Cache S) :=
  forall pa:PhysicalAddress,
    phys_to_index pa = phys_to_index (tag (find_in_map cache (phys_to_index pa))).