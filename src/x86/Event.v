Require Import SpecCert.x86.Architecture.
Require Import SpecCert.x86.Value.
Require Import SpecCert.Address.
Require Import SpecCert.Formalism.

(* A software event is an event produced by the execution of an
 * assembly instruction.
 *)
Inductive SoftwareEvent :=
| DisableInterrupt :SoftwareEvent
| EnableInterrupt  :SoftwareEvent
| Read             :PhysicalAddress -> Value -> SoftwareEvent
| Write            :PhysicalAddress -> Value -> SoftwareEvent
| OpenSmram        :SoftwareEvent
| CloseSmram       :SoftwareEvent
| LockSmramc       :SoftwareEvent
| NextInstruction  :PhysicalAddress -> SoftwareEvent.

(* A hardware event is an event produced by the hardware in response
 * to *something*. It can interrupt the normal execution flow of an
 * assembly instruction, for instance
 *)
Inductive HardwareEvent :=
| Exec             :Value -> HardwareEvent
| ReceiveInterrupt :Interrupt -> HardwareEvent.

Definition x86Event := Event SoftwareEvent HardwareEvent.
