Require Import Coq.Sets.Ensembles.
Require Import Coq.Program.Tactics.

Require Import SpecCert.Formalism.
Require Import SpecCert.Smm.Delta.Behavior.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Preserve.
Require Import SpecCert.Smm.Delta.Secure.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.x86.

Program Definition Delta
  : HSEMechanism Software (MINx86 smm_context) :=
  {| state_inv         := inv
   ; behavior          := smm_behavior
   ; TCB               := SmmTCB
   ; context           := smm_context |}.
Next Obligation.
  unfold software_only_prop in H1.
  destruct (software_dec ev).
  + apply (software_transitions_preserve_inv (exist _ ev _) h h' H H1 H0 H2).
  + assert ((fun ev : x86Event => ~ x86_software ev) ev) as Hmiss by exact n.
    apply (hardware_transitions_preserve_inv (exist _ ev Hmiss) h h' H H0 H2).
Qed.
Next Obligation.
  unfold smm_behavior, SmmTCB, In in *.
  intro Hsmm.
  apply H in Hsmm.
  destruct Hsmm.
Qed.
