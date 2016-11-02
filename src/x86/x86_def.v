Require Import Coq.Classes.RelationClasses.
Require Import Coq.Sets.Ensembles.

Require Import SpecCert.Formalism.
Require Import SpecCert.x86.Architecture.
Require Import SpecCert.x86.Event.
Require Import SpecCert.x86.Transition.

Definition x86CS
           (S: Set)
  := ComputingSystem (Architecture S) SoftwareEvent HardwareEvent.

Definition MINx86
           {S:       Set}
           (context: x86Context S)
  : x86CS S  :=
  {| precondition := x86_precondition
    ; postcondition := x86_postcondition context |}.
