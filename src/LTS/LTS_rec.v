Require Import Coq.Sets.Ensembles.

Record LTS (State Label:Type) :=
  {
    domain: Ensemble State;
    transition: State -> Label -> State -> Prop;
    domain_consistency: forall s s':State, forall l:Label,
          transition s l s'
          -> In _ domain s
            /\ In _ domain s'
  }.

Arguments domain : default implicits.
Arguments transition : default implicits.
Arguments domain_consistency : default implicits.
