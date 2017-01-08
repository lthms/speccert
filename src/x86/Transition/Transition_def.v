Require Import SpecCert.Formalism.

Require Import SpecCert.x86.Event.
Require Import SpecCert.x86.Architecture.
Require Import SpecCert.x86.Transition.Event.

Definition x86Context
           (S: Type) :=
  HardwareSoftwareMapping (Architecture S) S.

Definition pre_condition
           {S :Type} :=
  Architecture S -> Prop.

Definition post_condition
           {S :Type} :=
  Architecture S -> Architecture S -> Prop.

Definition no_pre
           {S :Type} :=
  fun (a: Architecture S) => True.

Definition id_post
           {S :Type} :=
  fun (a a':Architecture S) => a = a'.

Definition x86_precondition
           {Label: Type}
           (a:  Architecture Label)
           (ev: x86Event)
  : Prop :=
  match ev with
  | DisableInterrupt     => no_pre
  | EnableInterrupt      => no_pre
  | (Write addr value)   => no_pre
  | (Read addr value)    => read_pre addr value
  | OpenSmram            => open_smram_pre
  | CloseSmram           => close_smram_pre
  | LockSmramc           => lock_smramc_pre
  | (NextInstruction pa) => no_pre
  | (ReceiveInterrupt i) => no_pre
  | (Exec value)         => read_pre (ip (proc a)) value
  end a.

Definition x86_postcondition
           {S:       Type}
           (context: x86Context S)
           (h:       Architecture S)
           (ev:      x86Event)
           (h':      Architecture S)
  : Prop :=
  match ev with
  | DisableInterrupt     => disable_interrupt_post
  | EnableInterrupt      => enable_interrupt_post
  | (Write addr value)   => write_post context addr value
  | (Read addr value)    => read_post addr
  | OpenSmram            => open_smram_post
  | CloseSmram           => close_smram_post
  | LockSmramc           => lock_smramc_post
  | (NextInstruction pa) => nextinstr_post pa
  | (ReceiveInterrupt i) => receive_interrupt_post i
  | (Exec value)         => read_post (ip (proc h))
  end h h'.
