Require Import SpecCert.x86.Architecture.ProcessorUnit.ProcessorUnit_rec.
Require Import SpecCert.Address.
Require Import SpecCert.Interval.

Definition interrupts_are_disabled
           (p :ProcessorUnit) :=
  cli p = true.

Definition interrupts_are_enabled
           (p :ProcessorUnit) :=
  cli p = false.

Definition will_process_interrupt
           (p :ProcessorUnit)
           (i :Interrupt) :=
  i = SMI \/ interrupts_are_enabled p.

Definition is_in_smm
           (p :ProcessorUnit) :=
  (in_smm p) = true.

Definition is_inside_smrr
           (p  :ProcessorUnit)
           (pa :PhysicalAddress) :=
  is_inside_interval (address_offset pa) (interval (smrr p)).

Definition smrr_hit
           (p  :ProcessorUnit)
           (pa :PhysicalAddress) :=
  is_in_smm p /\ is_inside_smrr p pa.