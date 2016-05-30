Require Import Coq.Sets.Ensembles.
Require Import Coq.Classes.RelationClasses.

Require Import SpecCert.LTS.
Require Import SpecCert.x86.Architecture.
Require Import SpecCert.x86.Event.
Require Import SpecCert.x86.Transition.
Require Import SpecCert.x86.SecureTransition.

Definition ComputingSystem
           (S :Set) :=
  LTS (Architecture S) (Event S).

Definition HardwarePlatform
           {S :Set} :=
  (ProcessorUnit -> S) -> ComputingSystem S.

Definition Execution
           (S :Set) :=
  Trace (Architecture S) (Event S).

(** * x86 Hardware Platform *)

Program Definition x86
        {S :Set}
        :HardwarePlatform :=
  fun context => {| domain := Full_set (Architecture S)
                ; transition := (Transition context) |}.
Next Obligation.
  repeat constructor.
Qed.
