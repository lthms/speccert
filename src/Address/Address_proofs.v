Require Export SpecCert.Address.Address_ind.
Require Export SpecCert.Address.Address_eq.

Lemma addr_eq_refl: forall x:Address, addr_eq x x.
Proof.
  unfold addr_eq.
  reflexivity.
Qed.

Lemma addr_eq_trans: forall x y z:Address, addr_eq x y -> addr_eq y z -> addr_eq x z.
Proof.
  unfold addr_eq.
  intuition.
  rewrite H; trivial.
Qed.

Lemma addr_eq_sym: forall x y:Address, addr_eq x y -> addr_eq y x.
Proof.
  unfold addr_eq.
  intuition.
Qed.
