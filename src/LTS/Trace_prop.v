Require Import Coq.Sets.Ensembles.

Require Import SpecCert.LTS.LTS_rec.
Require Import SpecCert.LTS.LTS_prop.
Require Import SpecCert.LTS.Trace_ind.
Require Import SpecCert.LTS.Trace_func.

Fixpoint run_of {State Label:Type} (lts:LTS State Label)(p:Trace State Label) {struct p} :=
  match p with
  | one_transition s l s' => transition lts s l s'
  | n_transition p l s' => run_of lts p /\ (transition lts (last p) l s')
  end.
