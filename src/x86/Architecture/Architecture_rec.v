Require Import SpecCert.x86.Architecture.ProcessorUnit.
Require Import SpecCert.x86.Architecture.MemoryController.
Require Import SpecCert.Address.
Require Import SpecCert.Memory.
Require Import SpecCert.Cache.
Require Import SpecCert.x86.Value.

Record Architecture (Label: Type) :=
  { proc:              ProcessorUnit
  ; memory_controller: MemoryController
  ; memory:            Memory (Value * Label)
  ; cache:             Cache (Value * Label)
  ; x86_cache_is_well_formed:
                       cache_is_well_formed (cache)
  }.

Arguments cache:             default implicits.
Arguments memory:            default implicits.
Arguments memory_controller: default implicits.
Arguments proc:              default implicits.
Arguments x86_cache_is_well_formed:
                             default implicits.