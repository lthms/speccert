Require Import Coq.Classes.RelationClasses.

Require Import SpecCert.Smm.Software.Software_ind.

Definition smm_security_lt
           (s1 s2 :Software) :=
  match s1,s2 with
  | unprivileged, smm => True
  | _, _ => False
  end.

Instance smm_security_transitive : Transitive smm_security_lt.
Proof.
  unfold Transitive.
  intros x y z.
  unfold smm_security_lt.
  induction x; induction y; induction z; simpl; auto.
Qed.

Instance smm_security_irreflexive : Irreflexive smm_security_lt.
Proof.
  unfold Irreflexive, Reflexive, complement.
  unfold smm_security_lt.
  induction x; simpl; auto.
Qed.

Instance smm_security : StrictOrder smm_security_lt :=
  {| StrictOrder_Irreflexive := smm_security_irreflexive
   ; StrictOrder_Transitive  := smm_security_transitive |}.