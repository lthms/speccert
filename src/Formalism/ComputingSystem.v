(**
    Given H a set of hardware architecture states and E a set of events,
    a Computing System C is a pair of (precondition, postcondition) where
    precondition is a predicate on H x E and postcondition is a predicate
    on H x E x H.
**)

Class Event (E: Type) :=
  { software : E -> Prop
  ; software_dec: forall (e: E), { software e } + { ~ software e } }.

Record ComputingSystem
       (Hw Ev:  Type)
      `{Event Ev}
  :=
  { precondition: Hw -> Ev -> Prop
  ; postcondition: Hw -> Ev -> Hw -> Prop }.

Arguments precondition [Hw Ev H] (_ _ _).
Arguments postcondition [Hw Ev H] (_ _ _ _).

(**
    A Computing System C defines a semantics of events as state-transformers
**)
Definition state_transformation
           {H E:     Type}
          `{Event E}
           (C:       ComputingSystem H E)
           (h:       H)
           (ev:      E)
           (h':      H)
  : Prop :=
  precondition C h ev /\ postcondition C h ev h'.

Notation "h -[ C | ev ]-> h'" := (state_transformation C h ev h') (at level 81).

(**
    A Run of a Computing System C is a sequence of state-transformations
    of C.
**)
Inductive Run
          {H E:       Type}
         `{evInst:    Event E}
          (C:         ComputingSystem H E)
          (init last: H)
  :=
  | step (ev:  E)
         (Hst: init -[C|ev]-> last)
    : Run C init last
  | sequence {penultimate: H}
             (r':          Run C init penultimate)
             (ev:          E)
             (Hst:         penultimate -[C|ev]-> last)
    : Run C init last.

Arguments step [H E evInst C init last] (ev Hst).
Arguments sequence [H E evInst C init last penultimate] (r' ev Hst).

Definition rinit
           {H E:       Type}
          `{Event E}
           {C:         ComputingSystem H E}
           {init last: H}
           (r:         Run C init last)
  : H :=
  init.

Definition rlast
           {H E:       Type}
          `{Event E}
           {C:         ComputingSystem H E}
           {init last: H}
           (r:         Run C init last)
  : H :=
  last.

Fixpoint always_true
         {H E:       Type}
        `{Event E}
         {C:         ComputingSystem H E}
         {init last: H}
         (prop:      H -> E -> Prop)
         (r:         Run C init last)
  : Prop :=
  match r with
  | step ev _        => prop init ev
  | sequence r' ev _ => always_true prop r' /\ prop (rlast r') ev
  end.