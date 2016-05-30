Require Import SpecCert.x86.Architecture.ProcessorUnit.
Require Import SpecCert.x86.Architecture.MemoryController.
Require Import SpecCert.x86.Architecture.Architecture_rec.
Require Import SpecCert.Memory.
Require Import SpecCert.Address.
Require Import SpecCert.Cache.

Definition update_proc
           {S  :Set}
           (a  :Architecture S)
           (p' :ProcessorUnit) :=
  {| proc              := p'
   ; memory_controller := (memory_controller a)
   ; memory            := (memory a)
   ; cache             := (cache a) |}.

Definition update_memory_controller
           {S  :Set}
           (a  :Architecture S)
           (m' :MemoryController) :=
  {| proc              := (proc a)
   ; memory_controller := m'
   ; memory            := (memory a)
   ; cache             := (cache a) |}.

Definition update_memory_content
           {S  :Set}
           (a  :Architecture S)
           (ha :HardwareAddress)
           (c  :S) :=
  {| proc              := (proc a)
   ; memory_controller := (memory_controller a)
   ; memory            := (update_in_memory (memory a) ha c)
   ; cache             := (cache a) |}.

Definition find_memory_content
           {S  :Set}
           (a  :Architecture S)
           (ha :HardwareAddress)
           :S :=
  find_in_memory (memory a) ha.

Definition phys_to_hard
           {S  :Set}
           (a  :Architecture S)
           (pa :PhysicalAddress)
           :HardwareAddress :=
  let smiact := in_smm (proc a) in
  translate_physical_address (memory_controller a) smiact pa.

Definition find_cache_content
           {S  :Set}
           (a  :Architecture S)
           (pa :PhysicalAddress)
           :option S :=
  find_in_cache (cache a) pa.

Definition find_cache_location_content
           {S  :Set}
           (a  :Architecture S)
           (pa :PhysicalAddress)
           :S :=
  find_in_cache_location (cache a) pa.

Definition update_cache_content
           {S  :Set}
           (a  :Architecture S)
           (pa :PhysicalAddress)
           (c  :S) :=
  {| proc              := (proc a)
   ; memory_controller := (memory_controller a)
   ; memory            := (memory a)
   ; cache             := global_update_in_cache (cache a) pa c |}.

Definition load_in_cache_from_memory
           {S  :Set}
           (a  :Architecture S)
           (pa :PhysicalAddress)
           :Architecture S :=
  let cont := find_in_cache_location (cache a) pa in
  let cont' := find_memory_content a (phys_to_hard a pa) in
  let a' := if cache_location_is_dirty_dec (cache a) pa
            then let pa' := cache_location_address (cache a) pa in
                 let ha := phys_to_hard a pa' in
                 update_memory_content a ha cont
            else a in
  update_cache_content a' pa cont'.

Definition find_address_content
           {S  :Set}
           (a  :Architecture S)
           (pa :PhysicalAddress)
           :option S :=
  match (resolve_cache_strategy (proc a) pa) with
  | Uncachable => Some (find_memory_content a (phys_to_hard a pa))
  | SmrrHit    => None
  | _          => if cache_hit_dec (cache a) pa
                 then Some (find_in_cache_location (cache a) pa)
                 else Some (find_memory_content a (phys_to_hard a pa))
  end.

(*
Definition context (p :ProcessorUnit) :=
  if is_in_smm_dec p
  then smm
  else ring0.
*)