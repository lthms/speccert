Require Import SpecCert.x86.Architecture.
Require Import SpecCert.Address.
Require Import SpecCert.Cache.

Definition write_uncachable
           {S        :Set}
           (a        :Architecture S)
           (context  :Architecture S -> S)
           (pa       :PhysicalAddress) :=
  let current_context := (context a) in
  let ha := phys_to_hard a pa in
  update_memory_content a ha current_context.

Definition write_writeback
           {S        :Set}
           (a        :Architecture S)
           (context  :Architecture S -> S)
           (pa       :PhysicalAddress) :=
  let current_context := (context a) in
  let a' := if cache_hit_dec (cache a) pa
            then a
            else load_in_cache_from_memory a pa in
  update_cache_content a' pa current_context.

(* Intel, Chapter 11: Memory Cache Control
  "If the logical processor is not in SMM, write accesses are ignored (...)" *)
Definition write_smrrhit
           {S  :Set}
           (a  :Architecture S)
           (pa :PhysicalAddress) :=
  a.

Definition write_post
           {S       :Set}
           (context :Architecture S -> S)
           (pa      :PhysicalAddress) :=
  fun (a a':Architecture S) =>
    match resolve_cache_strategy (proc a) pa with
    | Uncachable => a' = write_uncachable a context pa
    | WriteBack  => a' = write_writeback a context pa
    | SmrrHit    => a' = write_smrrhit a pa
    end.