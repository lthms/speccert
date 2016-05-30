Require Import SpecCert.LTS.
Require Import SpecCert.x86.
Require Import SpecCert.LTS.
Require Import SpecCert.Security.
Require Import SpecCert.Defender.

Require Import SpecCert.Smm.Software.
Require Import SpecCert.Smm.Delta.
Require Import SpecCert.Smm.Delta.Preserve.
Require Import SpecCert.Smm.Delta.Secure.

Lemma delta_lts_subsystem_of_x86Sec:
  subsystem (derive_computing_system Delta) (x86Sec smm_security context).
Proof.
  unfold subsystem.
  unfold derive_computing_system, x86Sec.
  simpl.
  unfold trans_cons, expand_software_trans.
  intros s s' l [[Htrans Hsmm] [Hinvs Hinvs']].
  split; [| try repeat constructor].
  split; [exact Htrans |].
  apply (invariant_permits_security l s s' Hinvs Htrans).
Qed.

Theorem delta_enforces_smm_security:
  defender_enforces_security context smm_security Delta.
Proof.
  apply x86Sec_subsystems_are_secure.
  apply delta_lts_subsystem_of_x86Sec.
Qed.