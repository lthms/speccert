Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.DecidableType.

Module Map (K:DecidableType).
  Definition Kset := K.t.

  Definition Map (t:Set) := Kset -> t.
  (*Definition Map := fun (k:Kset) => init.*)

  Definition add_in_map {t:Set} (m:Map t) (k:Kset) (c:t):Map t :=
    fun (k':Kset) => 
      if K.eq_dec k k' then
        c
      else
        m k'.

  Definition find_in_map {t:Set} (m:Map t) (k:Kset):t := m k.

  Lemma add_1: forall t:Set, forall m:Map t, forall k:Kset, forall c:t,
          find_in_map (add_in_map m k c) k = c.
  Proof.
    intros t m k c.
    unfold add_in_map.
    unfold find_in_map.
    destruct (K.eq_dec k k).
    + reflexivity.
    + unfold not in n.
      assert (K.eq k k) by (apply K.eq_refl).
      apply n in H.
      destruct H.
  Qed.

  Lemma add_2: forall t:Set, forall m:Map t, forall k k', forall c:t,
          ~ K.eq k k' -> find_in_map m k' = find_in_map (add_in_map m k c) k'.
  Proof.
    intros t m k k' c Hdiff.
    unfold find_in_map, add_in_map.
    destruct (K.eq_dec k k').
    + unfold not in Hdiff.
      apply Hdiff in e.
      destruct e.
    + reflexivity.
  Qed.
End Map.
