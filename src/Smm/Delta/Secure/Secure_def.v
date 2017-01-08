Require Import Coq.Classes.RelationClasses.

Require Import SpecCert.Formalism.
Require Import SpecCert.Smm.Delta.Behavior.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.x86.

Definition fetched
           (h:  Architecture Software)
           (ev: x86Event)
  : option Software :=
  match ev with
  | Exec _ => option_map snd (find_address_content h (ip (proc h)))
  | _ => None
  end.

Definition SmmTCB
           (s: Software)
  : Prop :=
  s = smm.

Definition smm_secure
           {init last: Architecture Software}
           (r:         Run (MINx86 smm_context) init last)
  : Prop :=
  software_execution_isolation smm_context fetched SmmTCB r.

Program Definition software_inv_is_secure
           (ev: { ev: x86Event | x86_software ev }) :=
  forall a a' :Architecture Software,
    inv a
    -> smm_behavior a ev
    -> x86_precondition a ev
    -> x86_postcondition smm_context a ev a'
    -> software_step_isolation smm_context fetched SmmTCB a ev.

Definition inv_is_secure
           (ev: x86Event) :=
  forall a a' :Architecture Software,
    inv a
    -> x86_precondition a ev
    -> x86_postcondition smm_context a ev a'
    -> software_step_isolation smm_context fetched SmmTCB a ev.

Ltac trivial_inv_is_secure :=
  unfold inv_is_secure;
  intros a a' Hinv Hpre Hpost;
  unfold software_step_isolation;
  intros t u Htrusted Huntrusted;
  unfold software_tampering;
  unfold fetched;
  unfold is;
  intros [H H'];
  destruct H'.
