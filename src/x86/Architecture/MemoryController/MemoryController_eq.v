Require Import Coq.Program.Tactics.

Require Import SpecCert.Utils.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_rec.

Definition memory_controller_eq
           (m m': MemoryController) :=
  smramc m = smramc m'.

Lemma memory_controller_eq_eq
      (m m': MemoryController)
  : memory_controller_eq m m' -> m = m'.
Proof.
  induction m as [s].
  induction m' as [s'].
  unfold memory_controller_eq, smramc.
  intro Heq.
  rewrite Heq.
  reflexivity.
Qed.

Lemma eq_memory_controller_eq
      (m m': MemoryController)
      (Heq:  m = m')
  : memory_controller_eq m m'.
Proof.
  induction m as [s].
  induction m' as [s'].
  rewrite Heq.
  reflexivity.
Qed.

Program Definition memory_controller_eq_dec
        (m m': MemoryController)
  : { memory_controller_eq m m' } + { ~ memory_controller_eq m m' } :=
  decide_dec (smramc_eq_dec (smramc m) (smramc m')).
Next Obligation.
  unfold memory_controller_eq.
  apply smramc_eq_eq.
  trivial.
Defined.
Next Obligation.
  unfold memory_controller_eq.
  unfold not in H; unfold not.
  intro Hfalse.
  apply eq_smramc_eq in Hfalse.
  apply H in Hfalse.
  trivial.
Defined.
