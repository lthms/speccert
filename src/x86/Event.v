Require Import SpecCert.x86.Architecture.
Require Import SpecCert.Address.

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

(* We consider two kind of events, software and hardware *)
Inductive Event (S :Set) :=
| hardware: HardwareEvent S -> Event S
| software: SoftwareEvent -> Event S.

Arguments software {S} _.
Arguments hardware {S} _.
Arguments Exec {S} _.
Arguments ReceiveInterrupt {S} _.