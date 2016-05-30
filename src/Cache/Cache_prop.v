Require Import Coq.Bool.Bool.

Require Import SpecCert.Cache.Cache_def.
Require Import SpecCert.Address.
Require Import SpecCert.Utils.

Definition cache_hit
           {S     :Set}
           (cache :Cache S)
           (pa    :PhysicalAddress)
           :Prop :=
  addr_eq pa (tag (_IndexMap.find_in_map cache (phys_to_index pa))).

Definition cache_hit_dec
           {S     :Set}
           (cache :Cache S)
           (pa:PhysicalAddress)
           : {cache_hit cache pa}+{~ cache_hit cache pa}.
refine (
    decide_dec (addr_eq_dec pa
                            (tag
                               (_IndexMap.find_in_map cache
                                               (phys_to_index pa)
                               )
                            )
               )
  ).
+ unfold cache_hit.
  induction (_IndexMap.find_in_map cache (phys_to_index pa))
    as [dirty cont tag].
  simpl in a.
  trivial.
+ unfold cache_hit.
  induction (_IndexMap.find_in_map cache (phys_to_index pa))
    as [dirty cont tag].
  simpl in n.
  trivial.
Defined.

Definition cache_location_is_dirty
           {S     :Set}
           (cache :Cache S)
           (pa    :PhysicalAddress) :=
  dirty (_IndexMap.find_in_map cache (phys_to_index pa)) = true.

Definition cache_location_is_dirty_dec
           {S     :Set}
           (cache :Cache S)
           (pa    :PhysicalAddress)
  : {cache_location_is_dirty cache pa}+{~ cache_location_is_dirty cache pa}.
refine (
    decide_dec (
        bool_dec
          (dirty
             (_IndexMap.find_in_map cache (phys_to_index pa))
          )
          true
      )
  );
unfold cache_location_is_dirty;
trivial.
Defined.

Definition cache_is_well_formed
           {S     :Set}
           (cache :Cache S) :=
  forall pa:PhysicalAddress,
    phys_to_index pa = phys_to_index (tag (_IndexMap.find_in_map cache (phys_to_index pa))).