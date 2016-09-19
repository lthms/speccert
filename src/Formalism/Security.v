Require Import SpecCert.Formalism.ComputingSystem.

Definition SecurityProperty
           {H Es Eh:   Type}
           (C:         ComputingSystem H Es Eh)
           (init last: H)
  := Run C init last -> Prop.