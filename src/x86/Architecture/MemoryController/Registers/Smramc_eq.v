Require Import Coq.Bool.Sumbool.
Require Import Coq.Bool.Bool.

Require Import SpecCert.Utils.
Require Import SpecCert.x86.Architecture.MemoryController.Registers.Smramc_rec.

Definition smramc_eq (s s':SmramcRegister) :=
  d_open s = d_open s' /\ d_lock s = d_lock s'.

Axiom smramc_eq_eq: forall s s':SmramcRegister,
  smramc_eq s s' -> s = s'.

Axiom eq_smramc_eq: forall s s':SmramcRegister,
  s = s' -> smramc_eq s s'.

Definition smramc_eq_dec (s s':SmramcRegister): {smramc_eq s s'}+{~smramc_eq s s'}.
  refine (
    let o := d_open s in
    let o' := d_open s' in
    let l := d_lock s in
    let l' := d_lock s' in
      decide_dec (sumbool_and _ _ _ _  (bool_dec o o') (bool_dec l l'))
  ); firstorder.
Qed.

Definition smramc_eqb (s s':SmramcRegister) :=
  if smramc_eq_dec s s' then true else false.
