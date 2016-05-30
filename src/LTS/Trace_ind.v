Require Import Coq.Sets.Ensembles.

Require Import SpecCert.LTS.LTS_rec.
Require Import SpecCert.LTS.LTS_prop.

Inductive Trace (State Label:Type) :=
| one_transition: State -> Label -> State -> Trace State Label
| n_transition: Trace State Label -> Label -> State -> Trace State Label.

Arguments one_transition : default implicits.
Arguments n_transition : default implicits.
