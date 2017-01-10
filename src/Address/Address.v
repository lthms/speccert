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

Class Singleton (S: Type) :=
  { singleton: forall (s s': S), s = s' }.


Definition singleton_eq
           {S: Type}
          `{Singleton S}
           (s s': S)
  : Prop :=
  s = s'.

Program Definition singleton_eq_dec
           {S: Type}
          `{Singleton S}
           (s s': S)
  : { singleton_eq s s' } + { ~ singleton_eq s s'} :=
  true_dec.
Next Obligation.
  apply singleton.
Defined.

Lemma singleton_eq_refl
      {S: Type}
      `{Singleton S}
      (s: S)
  : singleton_eq s s.
Proof.
  reflexivity.
Qed.

Lemma singleton_eq_sym
      {S:    Type}
     `{Singleton S}
      (s s': S)
  : singleton_eq s s' -> singleton_eq s' s.
Proof.
  unfold singleton_eq; auto.
Qed.

Lemma singleton_eq_trans
      {S:    Type}
     `{Singleton S}
      (s s' s'': S)
  : singleton_eq s s'
    -> singleton_eq s' s''
    -> singleton_eq s s''.
Proof.
  rewrite (singleton s' s); rewrite (singleton s'' s).
  trivial.
Qed.

Lemma singleton_eq_eq
      {S:    Type}
     `{Singleton S}
      (s s': S)
  : singleton_eq s s' -> s = s'.
Proof.
  intro H'; apply singleton.
Qed.

Lemma eq_singleton_eq
      {S:    Type}
     `{Singleton S}
      (s s': S)
  : s = s' -> singleton_eq s s'.
Proof.
  intro Heq.
  apply singleton.
Qed.

Instance singletonEq
         (S: Type)
        `{Singleton S}
  : Eq S :=
  { eq       := singleton_eq
  ; eq_refl  := singleton_eq_refl
  ; eq_sym   := singleton_eq_sym
  ; eq_trans := singleton_eq_trans
  ; eq_dec   := singleton_eq_dec
  ; eq_equal := singleton_eq_eq
  ; equal_eq := eq_singleton_eq
  }.