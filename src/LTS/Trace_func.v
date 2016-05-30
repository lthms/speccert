Require Import Coq.Sets.Ensembles.

Require Import SpecCert.LTS.LTS_rec.
Require Import SpecCert.LTS.LTS_prop.
Require Import SpecCert.LTS.Trace_ind.

Definition last {State Label:Type} (p:Trace State Label): State :=
  match p with
  | one_transition _ _ s' => s'
  | n_transition _ _ s' => s'
  end.

Fixpoint init {State Label:Type} (p:Trace State Label): State :=
  match p with
  | one_transition s _ _ => s
  | n_transition p _ _ => (init p)
  end.
