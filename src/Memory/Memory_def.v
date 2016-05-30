Require Import SpecCert.Address.
Require Import SpecCert.Map.

Module _HardAddrMap := Map (HardwareAddressDec).
Definition Memory (S:Set) := _HardAddrMap.Map S.