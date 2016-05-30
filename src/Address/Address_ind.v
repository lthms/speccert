Require Import SpecCert.Interval.
Require Import SpecCert.Address.AddressSpace.

Inductive Address :=
| address (n:nat): is_inside_interval n address_space -> Address.

Definition address_offset (a:Address) :=
  match a with
| address x _ => x
  end.
