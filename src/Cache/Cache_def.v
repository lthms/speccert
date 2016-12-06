Require Import SpecCert.Equality.
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

Parameter phys_to_index: PhysicalAddress -> Index.

Instance IndexEq: Eq Index :=
  { eq       := index_eq
  ; eq_sym   := index_eq_sym
  ; eq_refl  := index_eq_refl
  ; eq_trans := index_eq_trans
  ; eq_dec   := index_dec
  ; eq_equal := index_eq_eq
  ; equal_eq := eq_index_eq
  }.

Record CacheEntry
       (S: Type)
  := { dirty: bool
     ; content: S
     ; tag: PhysicalAddress }.

Arguments dirty   : default implicits.
Arguments content : default implicits.
Arguments tag     : default implicits.

Definition Cache (S: Type) := Map Index (CacheEntry S).
