Require Import SpecCert.Equality.
Require Import SpecCert.Memory.Memory_def.
Require Import SpecCert.Memory.Memory_func.
Require Import SpecCert.Address.
Require Import SpecCert.Map.

Lemma update_memory_1
      {S: Type}
      (m: Memory S)
      (k: HardwareAddress)
      (c: S)
  : find_in_memory (update_in_memory m k c) k = c.
Proof.
  unfold find_in_memory, update_in_memory.
  apply add_1.
Qed.

Lemma update_memory_2
      {S:    Type}
      (m:    Memory S)
      (k k': HardwareAddress)
      (c:    S)
      (neq:  ~ eq k k')
  : find_in_memory m k' = find_in_memory (update_in_memory m k c) k'.
Proof.
  unfold find_in_memory, update_in_memory.
  apply (add_2 m k k' c neq).
Qed.
