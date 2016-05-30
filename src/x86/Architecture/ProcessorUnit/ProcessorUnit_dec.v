Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Logic.Classical_Prop.

Require Import SpecCert.Utils.
Require Import SpecCert.x86.Architecture.ProcessorUnit.ProcessorUnit_rec.
Require Import SpecCert.x86.Architecture.ProcessorUnit.ProcessorUnit_prop.
Require Import SpecCert.Address.
Require Import SpecCert.Interval.

Definition interrupts_are_disabled_dec (p:ProcessorUnit)
  : {interrupts_are_disabled p}+{~interrupts_are_disabled p}.
refine (
  decide_dec (bool_dec (cli p) true)
); trivial.
Defined.

Definition interrupts_are_enabled_dec (p:ProcessorUnit)
  : {interrupts_are_enabled p}+{~interrupts_are_enabled p}.
refine (
  decide_dec (bool_dec (cli p) false)
  ); trivial.
Defined.

Definition will_process_interrupt_dec (p:ProcessorUnit)(i:Interrupt)
  : {will_process_interrupt p i}+{~will_process_interrupt p i}.
refine (
  decide_dec (sumbool_or _ _ _ _ (interrupt_eq_dec i SMI)
                                 (interrupts_are_enabled_dec p))
  ); unfold will_process_interrupt; trivial.
apply and_not_or; trivial.
Defined.

Definition is_in_smm_dec (p:ProcessorUnit): {is_in_smm p}+{~is_in_smm p}.
refine (
    decide_dec (bool_dec (in_smm p) true)
  ); trivial.
Defined.  

Definition is_inside_smrr_dec (p:ProcessorUnit)(pa:PhysicalAddress)
  :{is_inside_smrr p pa}+{~is_inside_smrr p pa}.
refine (
    decide_dec (is_inside_interval_dec (address_offset pa)
                                       (interval (smrr p))
               )
  ); intuition.
Defined.

Definition smrr_hit_dec
           (p:ProcessorUnit)
           (pa:PhysicalAddress)
  : {smrr_hit p pa} + {~ smrr_hit p pa}.
refine (
    decide_dec (sumbool_and _ _ _ _
                            (is_in_smm_dec p)
                            (is_inside_smrr_dec p pa)
               )
  ); trivial.
unfold smrr_hit.
apply or_not_and.
trivial.
Defined.