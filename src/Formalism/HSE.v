Require Import Coq.Sets.Ensembles.

Require Import SpecCert.Formalism.Security.
Require Import SpecCert.Formalism.Isolation.
Require Import SpecCert.Formalism.ComputingSystem.

Record HSEMechanism
       {H Es Eh: Type}
       (S:       Type)
       (C:       ComputingSystem H Es Eh) :=
  { state_inv: H -> Prop
  ; behavior:  H -> Es -> Prop
  ; TCB:       Ensemble S
  ; context:   HardwareSoftwareMapping H S
  ; behavior_preserves_state_inv:
      forall h h': H, forall ev: Event Es Eh,
          state_inv h
          -> match ev with
            | software es => behavior h es
            | _ => True
            end
          -> precondition C h ev
          -> postcondition C h ev h'
          -> state_inv h'
  ; behavior_only_restricts_TCB:
      forall x: S, forall h: H, forall es: Es,
            ~In S TCB x
            -> context h = x
            -> behavior h es }.

Arguments state_inv [H Es Eh S C] (_ _).
Arguments behavior [H Es Eh S C] (_ _ _).
Arguments TCB [H Es Eh S C] (_ _).
Arguments context [H Es Eh S C] (_ _).
Arguments behavior_preserves_state_inv [H Es Eh S C] (_ _ _ _ _ _ _ _).
Arguments behavior_only_restricts_TCB [H Es Eh S C] (_ _ _ _ _ _).

Definition behavior_enforced_step
           {H Es Eh: Type}
           {S:       Type}
           {C:       ComputingSystem H Es Eh}
           (D:       HSEMechanism S C)
           (init:    H)
           (ev:      Event Es Eh)
  : Prop :=
  match ev with
  | software es => behavior D init es
  | _           => True
  end.

Definition compliant_run
           {H Es Eh:   Type}
           {S:         Type}
           {C:         ComputingSystem H Es Eh}
           {init last: H}
           (D:         HSEMechanism S C)
           (r:         Run C init last)
  : Prop :=
  state_inv D init /\ always_true (behavior_enforced_step D) r.

Definition sound_mechanism
           {H Es Eh:   Type}
           {S:         Type}
           {C:         ComputingSystem H Es Eh}
           {init last: H}
           (D:         HSEMechanism S C)
           (Psec:      SecurityProperty C init last)
  : Prop :=
  forall r: Run C init last, compliant_run D r -> Psec r.

Lemma always_true_unwrap
      {St Es Eh S: Type}
      {C:          ComputingSystem St Es Eh}
      {i l p:      St}
      (prop:       St -> Event Es Eh -> Prop)
      (ev:         Event Es Eh)
      (Hst:        state_transformation C p ev l)
      (r:          Run C i p):
  always_true prop (sequence r ev Hst)
  -> always_true prop r.
Proof.
  intros Hal.
  inversion Hal as [Hprop Hal'].
  exact Hprop.
Qed.

Lemma compliant_run_unwrap
      {St Es Eh S: Type}
      {C:          ComputingSystem St Es Eh}
      {i l p:      St}
      (D:          HSEMechanism S C)
      (ev:         Event Es Eh)
      (Hst:        state_transformation C p ev l)
      (r:          Run C i p):
  compliant_run D (sequence r ev Hst)
  -> compliant_run D r.
Proof.
  intros Hal.
  inversion Hal as [Hprop Hal'].
  unfold compliant_run.
  split; [exact Hprop|].
  apply (always_true_unwrap (S:=S) (behavior_enforced_step D) ev Hst ) in Hal'.
  exact Hal'.
Qed.

Lemma compliant_run_preserves_inv
      {St Es Eh S: Type}
      {C:          ComputingSystem St Es Eh}
      {init last:  St}
      (D:          HSEMechanism S C)
      (r:          Run C init last):
    compliant_run D r -> state_inv D last.
Proof.
  induction r.
  + unfold compliant_run.
    intros [Hinv Hb].
    destruct Hst as [Hpre Hpost].
    apply (behavior_preserves_state_inv D init last ev Hinv Hb Hpre Hpost).
  + intros Hcomp.
    inversion Hcomp as [Hinv Hb].
    inversion Hb as [H1 H2].
    apply compliant_run_unwrap in Hcomp.
    apply IHr in Hcomp.
    destruct Hst as [Hpre Hpost].
    apply (behavior_preserves_state_inv D penultimate last ev Hcomp H2 Hpre Hpost).
Qed.