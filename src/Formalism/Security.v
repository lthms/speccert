Require Import SpecCert.Formalism.ComputingSystem.

Definition SecurityProperty
           {H E:       Type}
          `{Event E}
           (C:         ComputingSystem H E)
           (init last: H)
  := Run C init last -> Prop.