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
           (H Es Eh S: Type)
  := H -> Event Es Eh -> option S.

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
           {H Es Eh S: Type}
           (context:   HardwareSoftwareMapping H S)
           (fetched:   EventSoftwareMapping H Es Eh S)
           (h:         H)
           (ev:        Event Es Eh)
           (x y:       S)
  : Prop :=
  context h = x /\ is y (fetched h ev).

Definition software_step_isolation
           {H Es Eh S: Type}
           (context:   HardwareSoftwareMapping H S)
           (fetched:   EventSoftwareMapping H Es Eh S)
           (T:         Ensemble S)
           (h:         H)
           (ev:        Event Es Eh)
  : Prop :=
  forall t u: S, In S T t -> ~ In S T u -> ~software_tampering context fetched h ev t u.

Definition software_execution_isolation
           {H Es Eh S: Type}
           {init last: H}
           {C:         ComputingSystem H Es Eh}
           (context:   HardwareSoftwareMapping H S)
           (fetched:   EventSoftwareMapping H Es Eh S)
           (T:         Ensemble S)
           (r:         Run C init last)
  : Prop :=
  always_true (software_step_isolation context fetched T) r.