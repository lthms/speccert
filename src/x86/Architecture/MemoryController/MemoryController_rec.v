Require Import Coq.Bool.Bool.

Require Export SpecCert.x86.Architecture.MemoryController.Registers.

(* Base on 5th Generation Intel Core family datasheet *)
Record MemoryController := {
  smramc: SmramcRegister
}.
