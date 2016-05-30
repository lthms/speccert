Require Import Coq.Classes.RelationClasses.

Require Import SpecCert.x86.
Require Import SpecCert.Security.
Require Import SpecCert.LTS.

Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Behavior.
Require Import SpecCert.Smm.Software.

Definition software_inv_is_secure
           (ev:SoftwareEvent) :=
  forall a a' :Architecture Software,
    inv a
    -> smm_behavior a ev
    -> Transition context a (software ev) a'
    -> transition (x86Sec smm_security context) a (software ev) a'.

Definition inv_is_secure
           (ev:Event Software) :=
  forall a a' :Architecture Software,
    inv a
    -> Transition context a ev a'
    -> transition (x86Sec smm_security context) a ev a'.