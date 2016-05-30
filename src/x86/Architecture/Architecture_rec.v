Require Import SpecCert.x86.Architecture.ProcessorUnit.
Require Import SpecCert.x86.Architecture.MemoryController.
Require Import SpecCert.Address.
Require Import SpecCert.Memory.
Require Import SpecCert.Cache.

Record Architecture (S:Set) :=
  { proc: ProcessorUnit
  ; memory_controller: MemoryController
  ; memory: Memory S
  ; cache: Cache S }.

Arguments cache : default implicits.
Arguments memory : default implicits.
Arguments memory_controller : default implicits.
Arguments proc : default implicits.

(* This axiom is justified by the following lemma:
   `cache_stays_well_formed` (src/Cache/Cache_proofs.v).
   Indeed, we only use global_update_in_cache in order
   to modify the cache.

   Note that it could be added as invariant. In order to
   simplify the proof, we don't. But it could be a TODO.
 *)
Axiom hardware_ensures_cache_is_well_formed:
  forall S:Set, forall a:Architecture S,
    cache_is_well_formed (cache a).