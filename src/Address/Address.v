Require Import Coq.Arith.EqNat.
Require Import Coq.Structures.DecidableType.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Sumbool.

Require Import SpecCert.Interval.
Require Import SpecCert.Address.AddressSpace.
Require Import SpecCert.Utils.
Require Import SpecCert.Equality.

(**
Definitions
 *)

Inductive Address
          (T: Type)
  : Type :=
| address (t: T)
          (n:nat)
          (h: is_inside_interval n address_space)
  : Address T.

Arguments address [T] (t n h).

Definition address_offset
           {T: Type}
           (a:Address T) :=
  match a with
  | address _ x _ => x
  end.

Definition address_scope
           {T: Type}
           (a: Address T)
  : T :=
  match a with
  | address t _ _ => t
  end.

(**
   Equality
 *)

Definition addr_eq
           {T: Type}
          `{Eq T}
           (a a':Address T) :=
  address_offset a = address_offset a'
  /\ eq (address_scope a) (address_scope a').

(** We use axiom here because the type Address contains an embedded proof *)
Axiom addr_eq_eq: forall {T: Type} `{Eq T} (a a':Address T),
    addr_eq a a' -> a = a'.

Axiom eq_addr_eq: forall {T: Type} `{Eq T} (a a': Address T),
    a = a' -> addr_eq a a'.

Lemma addr_eq_refl
      {T: Type}
     `{Eq T}
  : forall (a: Address T), addr_eq a a.
Proof.
  intros a.
  unfold addr_eq.
  split.
  + reflexivity.
  + apply eq_refl.
Qed.

Lemma addr_eq_trans
      {T :Type}
     `{Eq T}
  : forall (a a' a'':Address T),
    addr_eq a a' -> addr_eq a' a'' -> addr_eq a a''.
Proof.
  intros a a' a'' [Ha1 Ha2] [Ha1' Ha2'].
  unfold addr_eq in *.
  split.
  + rewrite <- Ha1'.
    exact Ha1.
  + apply (eq_trans (address_scope a)
                    (address_scope a')
                    (address_scope a'')
                    Ha2
                    Ha2').
Qed.

Lemma addr_eq_sym
      {T: Type}
     `{Eq T}
  : forall (a a':Address T),
    addr_eq a a' -> addr_eq a' a.
Proof.
  unfold addr_eq in *.
  intros a a' [Heq Heq'].
  split.
  + symmetry; exact Heq.
  + apply eq_sym; exact Heq'.
Qed.

Program Definition addr_eq_dec
        {T:    Type}
       `{Eq T}
        (a a': Address T)
  : {addr_eq a a'}+{~addr_eq a a'} :=
  if (eq_nat_decide (address_offset a) (address_offset a'))
  then if (eq_dec (address_scope a) (address_scope a'))
       then true_dec
       else false_dec
  else false_dec.
Next Obligation.
  unfold addr_eq; split; intuition.
Qed.
Next Obligation.
  unfold addr_eq.
  intros [H2 H3].
  apply H1 in H3.
  exact H3.
Qed.
Next Obligation.
  unfold addr_eq.
  intros [H2 H3].
  intuition.
Qed.

Instance AddrEq
         {T: Type}
        `{Eq T}
  : Eq (Address T) :=
  { eq       := addr_eq
  ; eq_refl  := addr_eq_refl
  ; eq_sym   := addr_eq_sym
  ; eq_trans := addr_eq_trans
  ; eq_dec   := addr_eq_dec
  ; eq_equal := addr_eq_eq
  ; equal_eq := eq_addr_eq
  }.