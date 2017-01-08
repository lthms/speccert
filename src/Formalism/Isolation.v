Require Import Coq.Sets.Ensembles.

Require Import SpecCert.Formalism.ComputingSystem.
Require Import SpecCert.Formalism.Security.

(**
    A hardware-software mapping is a function which maps a hardware state
    to the currently executed software.
**)
Definition HardwareSoftwareMapping
           (H S: Type)
  := H -> S.

Definition EventSoftwareMapping
           (H E S: Type)
  := H -> E -> option S.

Definition is
           {A: Type}
           (a: A)
           (o: option A)
  : Prop :=
  match o with
  | Some a' => a = a'
  | None    => False
  end.

Definition software_tampering
           {H E S: Type}
           (context:   HardwareSoftwareMapping H S)
           (fetched:   EventSoftwareMapping H E S)
           (h:         H)
           (ev:        E)
           (x y:       S)
  : Prop :=
  context h = x /\ is y (fetched h ev).

Definition software_step_isolation
           {H E S:   Type}
           (context: HardwareSoftwareMapping H S)
           (fetched: EventSoftwareMapping H E S)
           (T:       Ensemble S)
           (h:       H)
           (ev:      E)
  : Prop :=
  forall t u: S,
    In S T t
    -> ~ In S T u
    -> ~software_tampering context fetched h ev t u.

Definition software_execution_isolation
           {H E S:     Type}
          `{Event E}
           {init last: H}
           {C:         ComputingSystem H E}
           (context:   HardwareSoftwareMapping H S)
           (fetched:   EventSoftwareMapping H E S)
           (T:         Ensemble S)
           (r:         Run C init last)
  : Prop :=
  always_true (software_step_isolation context fetched T) r.