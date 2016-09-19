Require Import SpecCert.x86.Architecture.
Require Import SpecCert.Address.
Require Import SpecCert.Formalism.

(* A software event is an event produced by the execution of an
 * assembly instruction.
 *)
Inductive SoftwareEvent :=
| DisableInterrupt :SoftwareEvent
| EnableInterrupt  :SoftwareEvent
| Read             :PhysicalAddress -> SoftwareEvent
| Write            :PhysicalAddress -> SoftwareEvent
| OpenSmram        :SoftwareEvent
| CloseSmram       :SoftwareEvent
| LockSmramc       :SoftwareEvent
| NextInstruction  :PhysicalAddress -> SoftwareEvent.

(* A hardware event is an event produced by the hardware in response
 * to *something*. It can interrupt the normal execution flow of an
 * assembly instruction, for instance
 *)
Inductive HardwareEvent (S :Set) :=
| Exec             :S -> HardwareEvent S
| ReceiveInterrupt :Interrupt -> HardwareEvent S.

Definition x86Event (S: Set) := Event SoftwareEvent (HardwareEvent S).

Arguments Exec {S} _.
Arguments ReceiveInterrupt {S} _.