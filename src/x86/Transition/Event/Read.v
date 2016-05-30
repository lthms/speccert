Require Import SpecCert.x86.Architecture.
Require Import SpecCert.Address.
Require Import SpecCert.Cache.
Require Import SpecCert.Interval.

Definition read_uncachable_post
           {S :Set}
           (a :Architecture S)
           (pa:PhysicalAddress) :=
  a.

(* Intel, Chapter 11: Memory Cache Control
   "If the logical processor is not in SMM, (...) read
   access return a fixed value for each byte" *)
Definition read_smrrhit_post
           {S  :Set}
           (a  :Architecture S)
           (pa :PhysicalAddress) :=
  a.

Definition read_writeback_post
           {S  :Set}
           (a  :Architecture S)
           (pa :PhysicalAddress) :=
  if cache_hit_dec (cache a) pa
  then a
  else load_in_cache_from_memory a pa.

Definition read_post
           {S  :Set}
           (pa :PhysicalAddress) :=
  fun (a a':Architecture S) =>
    match resolve_cache_strategy (proc a) pa with
    | Uncachable => a' = read_uncachable_post a pa
    | WriteBack  => a' = read_writeback_post a pa
    | SmrrHit    => a' = read_smrrhit_post a pa
    end.

Definition exec_pre
           {S :Set}
           (o :S) :=
  fun (a :Architecture S) =>
    find_address_content a (ip (proc a)) = Some o.