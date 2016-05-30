Require Import Coq.Bool.Sumbool.
Require Import Coq.Logic.Classical_Prop.

Require Import SpecCert.Address.HardwareAddress_ind.
Require Import SpecCert.Address.HardwareAddress_prop.
Require Import SpecCert.Utils.

Definition is_dram_dec (ha:HardwareAddress)
  :{is_dram ha}+{~is_dram ha}.
refine (
  match ha with
  | dram _ => true_dec
  | _ => false_dec
  end
); unfold is_dram; intuition.
Defined.

Definition is_vga_dec (ha:HardwareAddress)
  :{is_vga ha}+{~is_vga ha}.
refine (
  match ha with
  | vga _ => true_dec
  | _ => false_dec
  end
); unfold is_vga; intuition.
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
