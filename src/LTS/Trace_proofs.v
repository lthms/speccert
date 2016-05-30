Require Import Coq.Sets.Ensembles.

Require Import SpecCert.LTS.LTS_rec.
Require Import SpecCert.LTS.LTS_prop.
Require Import SpecCert.LTS.Trace_ind.
Require Import SpecCert.LTS.Trace_func.
Require Import SpecCert.LTS.Trace_prop.

Lemma subsystem_derivation {State Label:Type}: forall T S:LTS State Label, forall p:Trace State Label,
      subsystem T S
      -> run_of T p
      -> run_of S p.
Proof.
  intros T S p Htrans_in Hpath.
  induction p.
  + apply Htrans_in in Hpath.
    exact Hpath.
  + destruct Hpath as [Hp1 Hp2].
    split; [| apply Htrans_in in Hp2; exact Hp2 ].
    apply IHp in Hp1.
    exact Hp1.
Qed.

Lemma was_run {State Label:Type}:
  forall lts:LTS State Label,
  forall p p':Trace State Label,
  forall s':State, forall l:Label,
      p' = n_transition p l s'
      -> run_of lts p'
      -> run_of lts p.
Proof.
  intros lts p p' s' l Htrans Hpath.
  rewrite Htrans in Hpath.
  destruct Hpath as [Hp1 Hp2].
  exact Hp1.
Qed.

Lemma stay_in_domain {State Label:Type}: forall T S:LTS State Label, forall p:Trace State Label,
      closed_subsystem T S
      -> In _ (domain T) (init p)
      -> run_of S p
      -> In _ (domain T) (last p).
Proof.
  intros T S p [Htrans Hstay_in] Hin_dom Hpath.
  induction p; simpl in *.
  + assert (In State (domain S) s /\ In State (domain S) s0) as [Hin1 Hin2]; [
      apply domain_consistency in Hpath;
      exact Hpath |].
    apply Hstay_in in Hpath.
    * assert (In State (domain T) s /\ In State (domain T) s0) as [Hin3 Hin4]; [
        apply domain_consistency in Hpath;
        exact Hpath |].
      exact Hin4.
    * exact Hin_dom.
    * exact Hin2.
  + destruct Hpath as [Hp1 Hp2].
    apply IHp in Hin_dom; [| exact Hp1 ].
    apply Hstay_in in Hp2.
    * apply domain_consistency in Hp2.
      destruct Hp2 as [H HH].
      exact HH.
    * exact Hin_dom.
    * apply domain_consistency in Hp2.
      destruct Hp2 as [H HH].
      exact HH.
Qed.

Lemma closed_subsystem_derivation {State Label:Type}:
  forall T S:LTS State Label,
  forall p:Trace State Label,
    closed_subsystem T S
    -> In _ (domain T) (init p)
    -> run_of S p
    -> run_of T p.
Proof.
  intros T S p Hclosed Hin_dom Hpath.
  assert (In _ (domain T) (last p))
    by (apply (stay_in_domain T S p Hclosed Hin_dom Hpath)).
  destruct Hclosed as [Htrans Hstay_in].
  induction p; simpl in *.
  + apply Hstay_in in Hpath; [
      exact Hpath
    | exact Hin_dom
    | apply domain_consistency in Hpath;
      destruct Hpath as [Hp1 Hp2] ].
    exact Hp2.
  + destruct Hpath as [Hp1 Hp2].
    split.
    * apply IHp.
      - exact Hin_dom.
      - exact Hp1.
      - apply (stay_in_domain T S p) in Hp1.
        exact Hp1.
        firstorder.
        exact Hin_dom.
    * apply Hstay_in in Hp2.
      - exact Hp2.
      - apply (stay_in_domain T S p) in Hp1.
        exact Hp1.
        firstorder.
        apply Hin_dom.
      - apply (domain_consistency S) in Hp2 as [H1 H2].
        exact H2.
Qed.