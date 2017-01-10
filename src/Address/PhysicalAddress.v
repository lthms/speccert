Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Require Import SpecCert.Address.AddressSpace.
Require Import SpecCert.Address.Address.
Require Import SpecCert.Interval.
Require Import SpecCert.Utils.
Require Import SpecCert.Equality.

(**
   Definition
 *)

Inductive MemoryMap :=
| mm: MemoryMap.

Lemma mm_singleton
      (m m': MemoryMap)
  : m = m'.
Proof.
  induction m; induction m'.
  reflexivity.
Qed.

Instance mmSingleton
  : Singleton MemoryMap := { singleton := mm_singleton }.

Instance memoryMapEq
  : Eq MemoryMap
  := singletonEq MemoryMap.

Definition PhysicalAddress := Address MemoryMap.

(**
   Properties
 *)

Definition is_inside_smram (pa:PhysicalAddress) :=
  is_inside_interval (address_offset pa) smram_space.

(**
   Decidable properties
 *)

Definition is_inside_smram_dec (pa:PhysicalAddress)
  : { is_inside_smram pa } + { ~ is_inside_smram pa } :=
  is_inside_interval_dec (address_offset pa) smram_space.

Definition phys_addr_eq_dec
           (pa pa': PhysicalAddress)
  : {addr_eq pa pa'}+{~ addr_eq pa pa'} :=
  addr_eq_dec pa pa'.