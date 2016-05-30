Require Import SpecCert.LTS.
Require Import SpecCert.x86.

Require Import Coq.Sets.Ensembles.

Definition expand_software_trans
           {S                 :Set}
           (software_behavior :Architecture S -> SoftwareEvent -> Prop)
           :Architecture S -> Event S -> Prop :=
  fun a e => match e with
          | software se => software_behavior a se
          | hardware _ => True
          end.

Record Defender
       (S :Set) :=
  { safe_states       :Ensemble (Architecture S)
  ; software_behavior :Architecture S -> SoftwareEvent -> Prop
  ; software_context  :ProcessorUnit -> S
  ; safe_states_in    :Included (Architecture S) safe_states (domain (x86 software_context))
  ; valid_defender    :closed_subsystem (Restricted_LTS (x86 software_context)
                                                        safe_states
                                                        (expand_software_trans software_behavior)
                                                        safe_states_in)
                                        (TransRestricted_LTS (x86 software_context) (expand_software_trans software_behavior)) }.

Arguments safe_states : default implicits.
Arguments software_behavior : default implicits.
Arguments software_context : default implicits.
Arguments safe_states_in : default implicits.
Arguments valid_defender : default implicits.

Definition derive_computing_system
           {S   :Set}
           (def :Defender S)
           :ComputingSystem S
  := Restricted_LTS (x86 (software_context def))
                    (safe_states def)
                    (expand_software_trans (software_behavior def))
                    (safe_states_in def).

Definition defender_compliant_execution
           {S :Set}
           (def :Defender S)
           (p :Trace (Architecture S) (Event S))
           :Prop :=
  run_of (derive_computing_system def) p.