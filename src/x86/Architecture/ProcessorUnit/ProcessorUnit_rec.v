Require Import SpecCert.Cache.
Require Import SpecCert.Interval.
Require Import SpecCert.Address.
Require Export SpecCert.x86.Architecture.ProcessorUnit.Interrupt.

Record Smrr :=
  {
    smm_strategy: Strategy;
    interval: Interval
  }.

(* Base on 5th Generation Intel Core family datasheet *)
Record ProcessorUnit :=
  {
    in_smm    :bool;
    cli       :bool;
    strategy  :Strategy;
    smrr      :Smrr;
    ip        :PhysicalAddress;
    smbase    :PhysicalAddress
  }.


Axiom smrr_is_in_space: forall a:ProcessorUnit,
    is_included_in (interval (smrr a)) address_space.