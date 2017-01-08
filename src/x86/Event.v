Require Import Program.

Require Import SpecCert.x86.Architecture.
Require Import SpecCert.x86.Value.
Require Import SpecCert.Address.
Require Import SpecCert.Formalism.
Require Import SpecCert.Utils.

(* A software event is an event produced by the execution of an
 * assembly instruction.
 *
 * A hardware event is an event produced by the hardware in response
 * to *something*. It can interrupt the normal execution flow of an
 * assembly instruction, for instance *)

Inductive R :=
| Fetch: R
| Data: R.

Inductive x86Event :=
| DisableInterrupt: x86Event
| EnableInterrupt:  x86Event
| Read:             R -> PhysicalAddress -> Value -> x86Event
| Write:            PhysicalAddress -> Value -> x86Event
| OpenSmram:        x86Event
| CloseSmram:       x86Event
| LockSmramc:       x86Event
| NextInstruction:  PhysicalAddress -> x86Event
| ReceiveInterrupt: Interrupt -> x86Event.
Definition x86_software
           (e: x86Event)
  : Prop :=
  match e with
  | DisableInterrupt  => True
  | EnableInterrupt   => True
  | Read Data _ _     => True
  | Write _ _         => True
  | OpenSmram         => True
  | CloseSmram        => True
  | LockSmramc        => True
  | NextInstruction _ => True
  | _                 => False
  end.

Program Definition x86_software_dec
           (e: x86Event)
  : { x86_software e } + { ~ x86_software e } :=
  match e with
  | DisableInterrupt   => true_dec
  | EnableInterrupt    => true_dec
  | Read r _ _         => match r with
                          | Data => true_dec
                          | Fetch => false_dec
                          end
  | Write _ _          => true_dec
  | OpenSmram          => true_dec
  | CloseSmram         => true_dec
  | LockSmramc         => true_dec
  | NextInstruction _  => true_dec
  | ReceiveInterrupt _ => false_dec
  end.

Instance X86Event: Event x86Event :=
  { software := x86_software
  ; software_dec := x86_software_dec
  }.

Program Definition DisableInterrupt'
  : { e: x86Event | x86_software e }
  := DisableInterrupt.

Program Definition EnableInterrupt'
  : { e: x86Event | x86_software e }
  := EnableInterrupt.

Program Definition Read'
        (pa: PhysicalAddress)
        (v:  Value)
  : { e: x86Event | x86_software e }
  := Read Data pa v.

Program Definition Write'
        (pa: PhysicalAddress)
        (v:  Value)
  : { e: x86Event | x86_software e }
  := Write pa v.

Program Definition OpenSmram'
  : { e: x86Event | x86_software e }
  := OpenSmram.

Program Definition CloseSmram'
  : { e: x86Event | x86_software e }
  := CloseSmram.

Program Definition LockSmram'
  : { e: x86Event | x86_software e }
  := LockSmramc.

Program Definition NextInstruction'
        (pa: PhysicalAddress)
  : { e: x86Event | x86_software e }
  := NextInstruction pa.
