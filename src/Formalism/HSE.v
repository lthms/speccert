Require Import Program.
Require Import Coq.Sets.Ensembles.

Require Import SpecCert.Formalism.Security.
Require Import SpecCert.Formalism.Isolation.
Require Import SpecCert.Formalism.ComputingSystem.

Program Definition software_only_prop
        {H E: Type}
       `{Event E}
        (prop: H -> { e: E | software e } -> Prop)
        (h: H)
        (e: E)
  : Prop :=
  if software_dec e
  then prop h e
  else True.

Record HSEMechanism
       {H E: Type}
      `{Event E}
       (S:   Type)
       (C:   ComputingSystem H E) :=
  { state_inv: H -> Prop
  ; behavior:  H -> { e: E | software e } -> Prop
  ; TCB:       Ensemble S
  ; context:   HardwareSoftwareMapping H S
  ; preserves_state_inv:
      forall h h': H, forall ev: E,
          state_inv h
          -> precondition C h ev
          -> software_only_prop behavior h ev
          -> postcondition C h ev h'
          -> state_inv h'
  ; behavior_only_restricts_TCB:
      forall x: S, forall h: H, forall es: { e: E | software e },
            ~In S TCB x
            -> context h = x
            -> behavior h es }.

Arguments state_inv [H E _ S C] (_ _).
Arguments behavior [H E _ S C] (_ _ _).
Arguments TCB [H E _ S C] (_ _).
Arguments context [H E _ S C] (_ _).
Arguments preserves_state_inv [H E _ S C] (_ _ _ _ _ _ _ _).
Arguments behavior_only_restricts_TCB [H E _ S C] (_ _ _ _ _ _).

Program Definition behavior_enforced_step
           {H E S:   Type}
          `{Event E}
           {C:       ComputingSystem H E}
           (D:       HSEMechanism S C)
           (init:    H)
           (ev:      E)
  : Prop :=
  software_only_prop (behavior D) init ev.

Definition compliant_run
           {H E S:     Type}
          `{Event E}
           {C:         ComputingSystem H E}
           {init last: H}
           (D:         HSEMechanism S C)
           (r:         Run C init last)
  : Prop :=
  state_inv D init /\ always_true (behavior_enforced_step D) r.

Definition sound_mechanism
           {H E S  :   Type}
          `{Event E}
           {C:         ComputingSystem H E}
           {init last: H}
           (D:         HSEMechanism S C)
           (Psec:      SecurityProperty C init last)
  : Prop :=
  forall r: Run C init last, compliant_run D r -> Psec r.

Lemma always_true_unwrap
      {H E:   Type}
     `{Event E}
      {C:     ComputingSystem H E}
      {i l p: H}
      (prop:  H -> E -> Prop)
      (ev:    E)
      (Hst:   p -[C|ev]-> l)
      (r:     Run C i p):
  always_true prop (sequence r ev Hst)
  -> always_true prop r.
Proof.
  intros Hal.
  inversion Hal as [Hprop Hal'].
  exact Hprop.
Qed.

Lemma compliant_run_unwrap
      {H E S: Type}
     `{Event E}
      {C:     ComputingSystem H E}
      {i l p: H}
      (D:     HSEMechanism S C)
      (ev:    E)
      (Hst:   p -[C|ev]-> l)
      (r:     Run C i p):
  compliant_run D (sequence r ev Hst)
  -> compliant_run D r.
Proof.
  intros Hal.
  inversion Hal as [Hprop Hal'].
  unfold compliant_run.
  split; [exact Hprop|].
  apply (always_true_unwrap (behavior_enforced_step D) ev Hst) in Hal'.
  exact Hal'.
Qed.

Lemma compliant_run_preserves_inv
      {H E S:     Type}
     `{Event      E}
      {C:   ComputingSystem H E}
      {init last: H}
      (D:         HSEMechanism S C)
      (r:         Run C init last):
    compliant_run D r -> state_inv D last.
Proof.
  induction r.
  + unfold compliant_run.
    intros [Hinv Hb].
    destruct Hst as [Hpre Hpost].
    apply (preserves_state_inv D init last ev Hinv Hpre Hb Hpost).
  + intros Hcomp.
    inversion Hcomp as [Hinv Hb].
    inversion Hb as [H1 H2].
    apply compliant_run_unwrap in Hcomp.
    apply IHr in Hcomp.
    destruct Hst as [Hpre Hpost].
    apply (preserves_state_inv D penultimate last ev Hcomp Hpre H2 Hpost).
Qed.