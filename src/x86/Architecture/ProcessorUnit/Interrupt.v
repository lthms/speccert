Inductive Interrupt :=
| SMI.

Definition interrupt_eq_dec: forall i i':Interrupt, {i = i'}+{i <> i'}.
Proof.
  intros i i'.
  destruct i; destruct i'.
  left.
  reflexivity.
Qed.