Require Import Coq.Structures.DecidableType.

Require Import SpecCert.Address.
Require Import SpecCert.Map.

Parameter Index: Set.
Parameter index_eq: Index -> Index -> Prop.
Parameter index_eq_refl: forall i:Index, index_eq i i.
Parameter index_eq_sym: forall i i':Index, index_eq i i' -> index_eq i' i.
Parameter index_eq_trans: forall i i' i'':Index, index_eq i i' -> index_eq i' i'' -> index_eq i i''.
Parameter index_dec: forall i i':Index, {index_eq i i'}+{~index_eq i i'}.
Parameter index_eq_eq: forall i i':Index, index_eq i i' -> i = i'.
Parameter eq_index_eq: forall i i':Index, i = i' -> index_eq i i'.

Parameter phys_to_index: forall pa:PhysicalAddress, Index.

Module IndexDec <: DecidableType with
      Definition t:= Index.
                      Definition t := Index.

                      Definition eq := index_eq.
                      Definition eq_refl := index_eq_refl.
                      Definition eq_sym := index_eq_sym.
                      Definition eq_trans := index_eq_trans.
                      Definition eq_dec := index_dec.
End IndexDec.

Record CacheEntry (S :Set) := {
                      dirty: bool;
                      content: S;
                      tag: PhysicalAddress
                    }.

Arguments dirty   : default implicits.
Arguments content : default implicits.
Arguments tag     : default implicits.

Module _IndexMap := Map (IndexDec).
Definition Cache (S:Set) := _IndexMap.Map (CacheEntry S).