Require Import SpecCert.Memory.Memory_def.
Require Import SpecCert.Memory.Memory_func.
Require Import SpecCert.Address.

Lemma update_memory_1 {S:Set}: forall m:Memory S, forall k:HardwareAddress, forall c:S,
        find_in_memory (update_in_memory m k c) k = c.
Proof.
  intros m k c.
  unfold find_in_memory, update_in_memory.
  apply _HardAddrMap.add_1.
Qed.

Lemma update_memory_2 {S:Set}: forall m:Memory S, forall k k':HardwareAddress, forall c:S,
        ~ addr_eq k k'
        -> find_in_memory m k' = find_in_memory (update_in_memory m k c) k'.
Proof.
  intros m k k' c.
  unfold find_in_memory, update_in_memory.
  apply _HardAddrMap.add_2.
Qed.
