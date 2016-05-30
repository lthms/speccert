Require Import Coq.Sets.Ensembles.
Require Import Coq.Program.Tactics.

Require Import SpecCert.LTS.LTS_rec.

Definition trans_cons {State Label:Type}
           (trans: State -> Label -> State -> Prop)
           (S:Ensemble State)
           (s:State)
           (l:Label)
           (s':State): Prop :=
  trans s l s' /\ In _ S s /\ In _ S s'.

Program Definition Restricted_LTS {State Label:Type}
        (lts    :LTS State Label)
        (S      :Ensemble State)
        (trans  :State -> Label -> Prop)
        (h      :Included State S (domain lts)): LTS State Label :=
  let trans' := fun s l s' => transition lts s l s' /\ trans s l in
  {|
    domain := S;
    transition := trans_cons trans' S
  |}.
Next Obligation.
  destruct H as [H1 H2].
  exact H2.
Qed.

Definition StateRestricted_LTS {State Label:Type}
        (lts    :LTS State Label)
        (S      :Ensemble State)
        (h      :Included State S (domain lts)): LTS State Label :=
  Restricted_LTS lts S (fun s l => True) h.

Program Definition TransRestricted_LTS {State Label:Type}
        (lts    :LTS State Label)
        (trans  :State -> Label -> Prop) :=
  Restricted_LTS lts (domain lts) trans _.
Next Obligation.
  unfold Included.
  intros x Hin; exact Hin.
Qed.

Definition subsystem {State Label:Type} (T S:LTS State Label): Prop :=
  forall s s':State, forall l:Label,
      transition T s l s'
      -> transition S s l s'.

Definition closed_subsystem {State Label:Type} (T S: LTS State Label) : Prop :=
  subsystem T S
  /\ (forall s s':State, forall l:Label, In _ (domain T) s
                              -> In _ (domain S) s'
                              -> transition S s l s'
                              -> transition T s l s').