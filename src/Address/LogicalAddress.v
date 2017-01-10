Require Import SpecCert.Address.Address.
Require Import SpecCert.Equality.

Inductive LogicalMap :=
| lm: LogicalMap.

Lemma lm_singleton
      (l l': LogicalMap)
  : l = l'.
Proof.
  induction l; induction l'.
  reflexivity.
Qed.

Instance lmSingleton
  : Singleton LogicalMap := { singleton := lm_singleton }.

Instance lmMapEq
  : Eq LogicalMap
  := singletonEq LogicalMap.

Definition LogicalAddress := Address LogicalMap.