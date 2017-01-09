Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Logic.Classical_Prop.

Require Import SpecCert.Utils.
Require Import SpecCert.x86.Architecture.ProcessorUnit.ProcessorUnit_rec.
Require Import SpecCert.x86.Architecture.ProcessorUnit.ProcessorUnit_prop.
Require Import SpecCert.Address.
Require Import SpecCert.Interval.

Definition interrupts_are_disabled_dec
           (p: ProcessorUnit)
  : { interrupts_are_disabled p } + { ~ interrupts_are_disabled p } :=
  bool_dec (cli p) true.

Definition interrupts_are_enabled_dec
           (p: ProcessorUnit)
  : { interrupts_are_enabled p } + { ~ interrupts_are_enabled p } :=
  bool_dec (cli p) false.

Program Definition will_process_interrupt_dec
        (p: ProcessorUnit)
        (i: Interrupt)
  : { will_process_interrupt p i } + { ~ will_process_interrupt p i } :=
  (interrupt_eq_dec i SMI) :|| (interrupts_are_enabled_dec p).
Next Obligation.
  unfold will_process_interrupt.
  intros [Hsmi|Henable].
  + apply H in Hsmi.
    exact Hsmi.
  + apply H0 in Henable.
    exact Henable.
Qed.

Definition is_in_smm_dec
           (p: ProcessorUnit)
  : { is_in_smm p } + { ~ is_in_smm p } :=
    bool_dec (in_smm p) true.

Definition is_inside_smrr_dec
           (p:  ProcessorUnit)
           (pa: PhysicalAddress)
  : { is_inside_smrr p pa } + { ~ is_inside_smrr p pa } :=
    is_inside_interval_dec (address_offset pa)
                           (interval (smrr p)).

Program Definition smrr_hit_dec
        (p:  ProcessorUnit)
        (pa: PhysicalAddress)
  : { smrr_hit p pa } + { ~ smrr_hit p pa } :=
  (is_in_smm_dec p) :&& (is_inside_smrr_dec p pa).
Next Obligation.
  unfold smrr_hit.
  split; [exact H|exact H0].
Qed.
Next Obligation.
  unfold smrr_hit.
  intros [Hsmm Hinside].
  destruct H as [H|H]; [ apply H in Hsmm;
                         exact Hsmm
                       | apply H in Hinside;
                         exact Hinside
                       ].
Qed.