Require Import SpecCert.Formalism.
Require Import SpecCert.Smm.Delta.Delta_def.
Require Import SpecCert.Smm.Delta.Preserve.
Require Import SpecCert.Smm.Delta.Secure.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.x86.

Theorem delta_is_sound: forall init last: Architecture Software,
    sound_mechanism (init:=init)(last:=last) Delta smm_secure.
Proof.
  unfold sound_mechanism.
  intros init last.
  induction r.
  + unfold sound_mechanism, compliant_run, behavior_enforced_step, smm_secure, software_execution_isolation.
    intros [Hinv Hbehave].
    inversion Hst as [Hpre Hpost].
    apply (invariant_permits_security ev init last Hinv Hpre Hpost).
  + intro Hcomp.
    apply compliant_run_unwrap in Hcomp.
    assert (state_inv Delta penultimate) as Hinv'; [apply (compliant_run_preserves_inv Delta r Hcomp)|].
    assert (smm_secure r) as Hsec; [apply IHr in Hcomp; exact Hcomp|].
    unfold smm_secure, software_execution_isolation.
    split.
    * exact Hsec.
    * inversion Hst as [Hpre Hpost].
      apply (invariant_permits_security ev penultimate last Hinv' Hpre Hpost).
Qed.