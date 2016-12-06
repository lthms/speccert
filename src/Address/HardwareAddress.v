Require Import Coq.Bool.Sumbool.
Require Import Coq.Logic.Classical_Prop.

Require Export SpecCert.Address.Address.
Require Import SpecCert.Utils.
Require Import SpecCert.Equality.

(**
   Definition
 *)

Inductive HardwareComponent :=
| DRAM: HardwareComponent
| VGA:  HardwareComponent.

Definition hc_eq
           (h h': HardwareComponent)
  : Prop :=
  h = h'.

Definition hc_eq_dec
           (h h': HardwareComponent)
  : { hc_eq h h'} + { ~ hc_eq h h' }.
unfold hc_eq.
decide equality.
Qed.

Instance hcEq : Eq HardwareComponent :=
  { eq := hc_eq
  ; eq_dec := hc_eq_dec
  }.
+ unfold hc_eq; auto.
+ unfold hc_eq; auto.
+ unfold hc_eq; intros t t' t'' H1 H2; rewrite H1; rewrite H2; reflexivity.
+ unfold hc_eq; auto.
+ unfold hc_eq; auto.
Qed.

Definition HardwareAddress := Address HardwareComponent.

(**
   Functions
 *)

(* todo: should be a nat rather than an address *)
Definition dram
           {t: Type}
           (pa: Address t)
  : HardwareAddress :=
  match pa with
  | address _ n h => address DRAM n h
  end.

(* todo: should be a nat rather than an address *)
Definition vga
           {t: Type}
           (pa: Address t)
  : HardwareAddress :=
  match pa with
  | address _ n h => address VGA n h
  end.

(**
   Properties
 *)

Definition is_dram (ha:HardwareAddress) :=
  address_scope ha = DRAM.

Definition is_vga (ha:HardwareAddress) :=
  address_scope ha = VGA.

Definition is_same_memory (ha ha':HardwareAddress) :=
  (is_dram ha /\ is_dram ha') \/ (is_vga ha /\ is_vga ha').

(**
   Decidable Properties
 *)

Definition scope_eq_dec
           (c c': HardwareComponent)
  : {c = c'} + {c <> c'}.
decide equality.
Defined.

Definition hardware_addr_eq_dec
           (ha ha': HardwareAddress)
  : {addr_eq ha ha'}+{~ addr_eq ha ha'}.
refine (decide_dec (addr_eq_dec ha ha')); trivial.
Defined.

Definition is_dram_dec (ha:HardwareAddress)
  :{is_dram ha}+{~is_dram ha}.
refine (
    decide_dec (scope_eq_dec (address_scope ha) DRAM)); unfold is_dram;
  [ exact e
  | exact n ].
Defined.

Definition is_vga_dec (ha:HardwareAddress)
  :{is_vga ha}+{~is_vga ha}.
refine (
    decide_dec (scope_eq_dec (address_scope ha) VGA)); unfold is_dram;
  [ exact e
  | exact n ].
Defined.

Definition is_same_memory_dec (ha ha':HardwareAddress)
  : {is_same_memory ha ha'}+{~is_same_memory ha ha'}.
refine(
  decide_dec (
    sumbool_or _ _ _ _ (sumbool_and _ _ _ _ (is_dram_dec ha)
                                            (is_dram_dec ha')
                       )
                       (sumbool_and _ _ _ _ (is_vga_dec ha)
                                            (is_vga_dec ha')
                       )
  )
); unfold is_same_memory; trivial.
inversion a.
apply and_not_or; split; apply or_not_and; trivial.
Defined.