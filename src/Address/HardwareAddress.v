Require Import Coq.Bool.Sumbool.
Require Import Coq.Logic.Classical_Prop.

Require Export SpecCert.Address.Address.
Require Import SpecCert.Utils.

(**
   Definition
 *)

Inductive HardwareComponent :=
| DRAM: HardwareComponent
| VGA:  HardwareComponent.

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
refine (decide_dec (addr_eq_dec scope_eq_dec ha ha')); trivial.
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

(**
   Decidable Types
 *)
Module HCEq <: Eq with Definition A := HardwareComponent.
  Definition A := HardwareComponent.
  Definition eq_dec := scope_eq_dec.
End HCEq.

Module HardwareAddressDec := AddressDec HCEq.