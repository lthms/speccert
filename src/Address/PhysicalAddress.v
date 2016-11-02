Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Require Import SpecCert.Address.AddressSpace.
Require Import SpecCert.Address.Address.
Require Import SpecCert.Interval.
Require Import SpecCert.Utils.

(**
   Definition
 *)

Inductive MemoryMap :=
| mm: MemoryMap.

Lemma memory_map_singleton: forall m m': MemoryMap, m = m'.
Proof.
  induction m; induction m'; reflexivity.
Qed.

Definition mm_eq: relation MemoryMap :=
  fun (m m': MemoryMap) => True.

Definition mm_eq_dec: forall (m m': MemoryMap), {m = m'}+{m <> m'}.
  decide equality.
Defined.

Lemma mm_eq_refl: forall m: MemoryMap, mm_eq m m.
Proof.
  unfold mm_eq; auto.
Qed.

Lemma mm_eq_sym: forall m m': MemoryMap, mm_eq m m' -> mm_eq m' m.
Proof.
  unfold mm_eq; auto.
Qed.

Lemma mm_eq_trans:
  forall (m m' m'': MemoryMap),
    mm_eq m m'
    -> mm_eq m' m''
    -> mm_eq m m''.
Proof.
  intros m m' m''; rewrite (memory_map_singleton m' m); rewrite (memory_map_singleton m'' m).
  trivial.
Qed.

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
  : {is_inside_smram pa}+{~is_inside_smram pa}.
refine (
  decide_dec(is_inside_interval_dec (address_offset pa) smram_space)
); unfold is_inside_smram; trivial.
Defined.

Definition phys_addr_eq_dec
           (pa pa': PhysicalAddress)
  : {addr_eq pa pa'}+{~ addr_eq pa pa'}.
refine (decide_dec (addr_eq_dec mm_eq_dec pa pa')); trivial.
Defined.