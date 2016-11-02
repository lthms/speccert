Require Import SpecCert.Address.

Parameter Value: Type.
Inductive Instruction: Type.

Parameter decode: Value -> option Instruction.
Parameter read_as_addr: Value -> PhysicalAddress.
