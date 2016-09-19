Require Import SpecCert.Formalism.

Require Import SpecCert.x86.Event.
Require Import SpecCert.x86.Architecture.
Require Import SpecCert.x86.Transition.Event.

Definition x86Context
           (S: Set)
  := HardwareSoftwareMapping (Architecture S) S.

Definition pre_condition
           {S :Set} :=
  Architecture S -> Prop.

Definition post_condition
           {S :Set} :=
  Architecture S -> Architecture S -> Prop.

Definition no_pre
           {S :Set} :=
  fun (a: Architecture S) => True.

Definition id_post
           {S :Set} :=
  fun (a a':Architecture S) => a = a'.

Definition x86_precondition
           {S:  Set}
           (h:  Architecture S)
           (ev: x86Event S)
  : Prop :=
  match ev with
  | software DisableInterrupt     => no_pre
  | software EnableInterrupt      => no_pre
  | software (Write addr)         => no_pre
  | software (Read addr)          => no_pre
  | software OpenSmram            => open_smram_pre
  | software CloseSmram           => close_smram_pre
  | software LockSmramc           => lock_smramc_pre
  | software (NextInstruction pa) => no_pre
  | hardware (ReceiveInterrupt i) => no_pre
  | hardware (Exec o)             => (exec_pre o)
  end h.

Definition x86_postcondition
           {S:       Set}
           (context: x86Context S)
           (h:       Architecture S)
           (ev:      x86Event S)
           (h':      Architecture S)
  : Prop :=
  match ev with
  | software DisableInterrupt     => disable_interrupt_post
  | software EnableInterrupt      => enable_interrupt_post
  | software (Write addr)         => write_post context addr
  | software (Read addr)          => read_post addr
  | software OpenSmram            => open_smram_post
  | software CloseSmram           => close_smram_post
  | software LockSmramc           => lock_smramc_post
  | software (NextInstruction pa) => nextinstr_post pa
  | hardware (ReceiveInterrupt i) => receive_interrupt_post i
  | hardware (Exec o)             => read_post (ip (proc h))
  end h h'.
