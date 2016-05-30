Require Import SpecCert.Utils.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_rec.

Definition memory_controller_eq (m m':MemoryController) :=
  smramc m = smramc m'.

Lemma memory_controller_eq_eq: forall m m':MemoryController,
  memory_controller_eq m m' -> m = m'.
Proof.
  intros m m'.
  induction m as [s].
  induction m' as [s'].
  unfold memory_controller_eq, smramc.
  intro Heq.
  rewrite Heq.
  reflexivity.
Qed.

Lemma eq_memory_controller_eq: forall m m':MemoryController,
  m = m' -> memory_controller_eq m m'.
Proof.
  intros m m'.
  induction m as [s].
  induction m' as [s'].
  intro Heq.
  rewrite Heq.
  reflexivity.
Qed.

Definition memory_controller_eq_dec (m m':MemoryController):
  {memory_controller_eq m m'}+{~memory_controller_eq m m'}.
refine (
  decide_dec (smramc_eq_dec (smramc m) (smramc m'))
).
+ unfold memory_controller_eq.
  apply smramc_eq_eq.
  trivial.
+ unfold memory_controller_eq.
  unfold not in n; unfold not.
  intro Hfalse.
  apply eq_smramc_eq in Hfalse.
  apply n in Hfalse.
  trivial.
Defined.

Definition memory_controller_eqb (m m':MemoryController) :=
  if memory_controller_eq_dec m m' then true else false.
