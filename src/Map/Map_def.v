Require Import SpecCert.Equality.

Definition Map
           (K V: Type)
          `{Eq K}
  := K -> V.

Definition add_in_map
           {K V: Type}
          `{Eq K}
           (m:   Map K V)
           (k:   K)
           (v:   V)
  : Map K V :=
  fun (k':K) => 
    if eq_dec k k'
    then v
    else m k'.

Definition find_in_map
           {K V: Type}
          `{Eq K}
           (m:   Map K V)
           (k: K)
  : V :=
  m k.

Lemma add_1
      {K V: Type}
     `{Eq K}
      (m:   Map K V)
      (k:   K)
      (v:   V)
  : find_in_map (add_in_map m k v) k = v.
Proof.
  unfold add_in_map.
  unfold find_in_map.
  destruct (eq_dec k k).
  + reflexivity.
  + destruct n.
    apply (eq_refl k).
Qed.

Lemma add_2
      {K V:  Type}
     `{Eq K}
      (m:    Map K V)
      (k k': K)
      (v:    V)
      (neq: ~ eq k k')
  : find_in_map m k' = find_in_map (add_in_map m k v) k'.
Proof.
  unfold find_in_map, add_in_map.
  destruct (eq_dec k k').
  + apply neq in e.
    destruct e.
  + reflexivity.
Qed.