(**
    Given H a set of hardware architecture states and E a set of events,
    a Computing System C is a pair of (precondition, postcondition) where
    precondition is a predicate on H x E and postcondition is a predicate
    on H x E x H.
**)
Inductive Event
          (Es Eh: Type)
  :=
  | software (es: Es): Event Es Eh
  | hardware (eh: Eh): Event Es Eh.

Arguments software [Es Eh] (es).
Arguments hardware [Es Eh] (eh).

Record ComputingSystem
       (H Es Eh: Type) :=
  { precondition: H -> Event Es Eh -> Prop
  ; postcondition: H -> Event Es Eh -> H -> Prop }.

Arguments precondition [H Es Eh] (_ _ _).
Arguments postcondition [H Es Eh] (_ _ _ _).

(**
    A Computing System C defines a semantics of events as state-transformers
**)
Definition state_transformation
           {H Es Eh: Type}
           (C:       ComputingSystem H Es Eh)
           (h:       H)
           (ev:      Event Es Eh)
           (h':      H)
  : Prop :=
  precondition C h ev /\ postcondition C h ev h'.

(**
    A Run of a Computing System C is a sequence of state-transformations
    of C.
**)
Inductive Run
          {H Es Eh:   Type}
          (C:         ComputingSystem H Es Eh)
          (init last: H)
  :=
  | step (ev:  Event Es Eh)
         (Hst: state_transformation C init ev last)
    : Run C init last
  | sequence {penultimate: H}
             (r':          Run C init penultimate)
             (ev:          Event Es Eh)
             (Hst:         state_transformation C penultimate ev last)
    : Run C init last.

Arguments step [H Es Eh C init last] (ev Hst).
Arguments sequence [H Es Eh C init last penultimate] (r' ev Hst).

Definition rinit
           {H Es Eh:   Type}
           {C:         ComputingSystem H Es Eh}
           {init last: H}
           (r:         Run C init last)
  : H :=
  init.

Definition rlast
           {H Es Eh:   Type}
           {C:         ComputingSystem H Es Eh}
           {init last: H}
           (r:         Run C init last)
  : H :=
  last.

Fixpoint always_true
         {H Es Eh:   Type}
         {C:         ComputingSystem H Es Eh}
         {init last: H}
         (prop:      H -> Event Es Eh -> Prop)
         (r:         Run C init last)
  : Prop :=
  match r with
  | step ev _        => prop init ev
  | sequence r' ev _ => always_true prop r' /\ prop (rlast r') ev
  end.