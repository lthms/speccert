Require Import Coq.Program.Tactics.

Require Import Coq.Bool.Sumbool.
Require Import Coq.Bool.Bool.

Require Import SpecCert.Utils.
Require Import SpecCert.x86.Architecture.MemoryController.Registers.Smramc_rec.

Definition smramc_eq
           (s s': SmramcRegister) :=
  d_open s = d_open s' /\ d_lock s = d_lock s'.

Axiom smramc_eq_eq:
  forall s s':SmramcRegister,
    smramc_eq s s' -> s = s'.

Axiom eq_smramc_eq:
  forall s s':SmramcRegister,
    s = s'
    -> smramc_eq s s'.

Program Definition smramc_eq_dec
        (s s': SmramcRegister)
  : { smramc_eq s s' } + { ~ smramc_eq s s' } :=
  let o := d_open s in
  let o' := d_open s' in
  let l := d_lock s in
  let l' := d_lock s' in
  (bool_dec o o') :&& (bool_dec l l').
Next Obligation.
  unfold smramc_eq.
  split; [exact H|exact H0].
Qed.
Next Obligation.
  unfold smramc_eq.
  destruct H as [H|H];
    intros [H' H'']; [ apply H in H'; exact H'
                     | apply H in H''; exact H''
                     ].
Qed.