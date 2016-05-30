Require Import Coq.Classes.RelationClasses.

Require Import SpecCert.x86.Architecture.
Require Import SpecCert.x86.Event.

Definition dummy_secure {S :Set} :=
  fun (a:Architecture S) =>
    True.

Definition exec_sec
           {S       :Set}
           {lt      :S -> S -> Prop}
           (context :ProcessorUnit -> S)
           (policy  :StrictOrder lt)
           (o       :S):=
  fun (a:Architecture S) =>
    let current_context := context (proc a) in
    lt current_context o \/ current_context = o.

Definition secure_transition
           {S       :Set}
           {lt      :S -> S -> Prop}
           (context :ProcessorUnit -> S)
           (policy  :StrictOrder lt)
           (a       :Architecture S)
           (ev      :Event S) :=
  match ev with
  | hardware (Exec o) => exec_sec context policy o a
  | _ => dummy_secure a
  end.