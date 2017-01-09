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

Lemma mm_singleton: forall m m': MemoryMap, m = m'.
Proof.
  induction m; induction m'; reflexivity.
Qed.

Definition mm_eq
           (m m': MemoryMap)
  : Prop :=
  m = m'.

Definition mm_eq_dec
           (m m': MemoryMap)
  : {mm_eq m m'}+{~ mm_eq m m'}.
  left.
  apply mm_singleton.
Defined.

Lemma mm_eq_refl
      (m: MemoryMap)
  : mm_eq m m.
Proof.
  unfold mm_eq; auto.
Qed.

Lemma mm_eq_sym
      (m m': MemoryMap)
  : mm_eq m m' -> mm_eq m' m.
Proof.
  unfold mm_eq; auto.
Qed.

Lemma mm_eq_trans
      (m m' m'': MemoryMap)
  : mm_eq m m'
    -> mm_eq m' m''
    -> mm_eq m m''.
Proof.
  rewrite (mm_singleton m' m); rewrite (mm_singleton m'' m).
  trivial.
Qed.

Lemma mm_eq_eq
      (m m': MemoryMap)
  : mm_eq m m' -> m = m'.
unfold mm_eq; auto.
Qed.

Lemma eq_mm_eq
      (m m': MemoryMap)
  : m = m' -> mm_eq m m'.
Proof.
  intro Heq.
  apply mm_singleton.
Qed.

Instance memoryMapEq : Eq MemoryMap :=
  { eq       := mm_eq
  ; eq_refl  := mm_eq_refl
  ; eq_sym   := mm_eq_sym
  ; eq_trans := mm_eq_trans
  ; eq_dec   := mm_eq_dec
  ; eq_equal := mm_eq_eq
  ; equal_eq := eq_mm_eq
  }.

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