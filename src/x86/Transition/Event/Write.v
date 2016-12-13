Require Import SpecCert.x86.Architecture.
Require Import SpecCert.Address.
Require Import SpecCert.Cache.
Require Import SpecCert.x86.Value.

Definition write_uncachable
           {Label:    Type}
           (a:        Architecture Label)
           (labelize: Architecture Label -> Label)
           (pa:       PhysicalAddress)
           (val:      Value) :=
  let lab := (labelize a) in
  let ha := phys_to_hard a pa in
  update_memory_content a ha (val,lab).

Definition write_writeback
           {Label:    Type}
           (a:        Architecture Label)
           (labelize: Architecture Label -> Label)
           (pa:       PhysicalAddress)
           (val:      Value) :=
  let lab := (labelize a) in
  let a' := if cache_hit_dec (cache a) pa
            then a
            else load_in_cache_from_memory a pa in
  update_cache_content a' pa (val,lab).

(* Intel, Chapter 11: Memory Cache Control
  "If the logical processor is not in SMM, write accesses are ignored (...)" *)
Definition write_smrrhit
           {Label:    Type}
           (a:        Architecture Label) :=
  a.

Definition write_post
           {Label:    Type}
           (labelize: Architecture Label -> Label)
           (pa:       PhysicalAddress)
           (val:      Value)
           (a a':Architecture Label) :=
  match resolve_cache_strategy (proc a) pa with
  | Uncachable => a' = write_uncachable a labelize pa val
  | WriteBack  => a' = write_writeback a labelize pa val
  | SmrrHit    => a' = write_smrrhit a
  end.