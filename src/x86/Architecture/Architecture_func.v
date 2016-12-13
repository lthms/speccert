Require Import SpecCert.x86.Architecture.ProcessorUnit.
Require Import SpecCert.x86.Architecture.MemoryController.
Require Import SpecCert.x86.Architecture.Architecture_rec.
Require Import SpecCert.x86.Value.
Require Import SpecCert.Memory.
Require Import SpecCert.Address.
Require Import SpecCert.Cache.

Program Definition update_proc
        {Label: Type}
        (a:     Architecture Label)
        (p':    ProcessorUnit) :=
  {| proc              := p'
   ; memory_controller := (memory_controller a)
   ; memory            := (memory a)
   ; cache             := (cache a)
   |}.
Next Obligation.
  apply (x86_cache_is_well_formed a).
Qed.

Program Definition update_memory_controller
        {Label: Type}
        (a:     Architecture Label)
        (m':    MemoryController) :=
  {| proc              := (proc a)
   ; memory_controller := m'
   ; memory            := (memory a)
   ; cache             := (cache a)
   |}.
Next Obligation.
  apply (x86_cache_is_well_formed a).
Qed.

Program Definition update_memory_content
        {Label: Type}
        (a:     Architecture Label)
        (ha:    HardwareAddress)
        (c:     (Value*Label)) :=
  {| proc              := (proc a)
   ; memory_controller := (memory_controller a)
   ; memory            := (update_in_memory (memory a) ha c)
   ; cache             := (cache a)
   |}.
Next Obligation.
  apply (x86_cache_is_well_formed a).
Qed.

Definition find_memory_content
           {Label: Type}
           (a:     Architecture Label)
           (ha:    HardwareAddress)
  : (Value * Label) :=
  find_in_memory (memory a) ha.

Definition phys_to_hard
           {Label: Type}
           (a:     Architecture Label)
           (pa:    PhysicalAddress)
  : HardwareAddress :=
  let smiact := in_smm (proc a) in
  translate_physical_address (memory_controller a) smiact pa.

Definition find_cache_content
           {Label: Type}
           (a:     Architecture Label)
           (pa:    PhysicalAddress)
  : option (Value * Label) :=
  find_in_cache (cache a) pa.

Definition find_cache_location_content
           {Label: Type}
           (a:  Architecture Label)
           (pa: PhysicalAddress)
  : (Value * Label) :=
  find_in_cache_location (cache a) pa.

Program Definition update_cache_content
        {Label: Type}
        (a:     Architecture Label)
        (pa:    PhysicalAddress)
        (c:     (Value*Label)) :=
  {| proc              := (proc a)
   ; memory_controller := (memory_controller a)
   ; memory            := (memory a)
   ; cache             := global_update_in_cache (cache a) pa c
   |}.
Next Obligation.
  remember (global_update_in_cache (cache a) pa (v, l)) as cache'.
  apply (cache_stays_well_formed (cache a) cache' pa  (v, l) (x86_cache_is_well_formed a) Heqcache').
Qed.

Definition load_in_cache_from_memory
           {Label: Type}
           (a:     Architecture Label)
           (pa:    PhysicalAddress) :=
  let a' := if cache_location_is_dirty_dec (cache a) pa
            then let pa' := cache_location_address (cache a) pa in
                 let ha := phys_to_hard a pa' in
                 let cont := find_in_cache_location (cache a) pa in
                 update_memory_content a ha cont
            else a in
  let cont' := find_memory_content a' (phys_to_hard a' pa) in
  update_cache_content a' pa cont'.

Definition find_address_content
           {Label: Type}
           (a:     Architecture Label)
           (pa:    PhysicalAddress)
  : option (Value*Label) :=
  match (resolve_cache_strategy (proc a) pa) with
  | Uncachable => Some (find_memory_content a (phys_to_hard a pa))
  | SmrrHit    => None
  | _          => if cache_hit_dec (cache a) pa
                 then Some (find_in_cache_location (cache a) pa)
                 else Some (find_memory_content a (phys_to_hard a pa))
  end.