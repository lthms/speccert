Require Export SpecCert.Smm.Delta.Behavior.
Require Export SpecCert.Smm.Delta.Invariant.
Require Export SpecCert.Smm.Delta.Preserve.

Require Import SpecCert.LTS.
Require Import SpecCert.Defender.
Require Import SpecCert.Smm.Software.

Require Import Coq.Sets.Ensembles.

Program Definition Delta
                   :Defender Software :=
  {| safe_states       := inv
   ; software_context  := context
   ; software_behavior := smm_behavior |}.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  unfold closed_subsystem.
  do 2 (try split).
  + destruct H as [H _].
    exact H.
  + split; constructor.
  + unfold In in *.
    split.
    * unfold TransRestricted_LTS, Restricted_LTS, trans_cons in H1.
      simpl in H1.
      destruct H1 as [[Ht _] _].
      exact Ht.
    * unfold expand_software_trans.
      induction l as [hev|sev].
      trivial.
      unfold TransRestricted_LTS, Restricted_LTS, trans_cons in H1.
      simpl in H1.
      destruct H1 as [[_ Hsmm] _].
      exact Hsmm.
  + split; [exact H |].
    unfold TransRestricted_LTS, Restricted_LTS, trans_cons in *.
    simpl in *.
    destruct H1 as [[Htrans Hsmm] _].
    unfold In.
    induction l as [hev|sev].
    * apply (hardware_transitions_preserve_inv hev s s' H Htrans).
    * apply (software_transitions_preserve_inv sev s s' H Hsmm Htrans).
Qed.