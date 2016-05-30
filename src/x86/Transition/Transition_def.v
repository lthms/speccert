Require Import SpecCert.x86.Event.
Require Import SpecCert.x86.Architecture.
Require Import SpecCert.x86.Transition.Event.

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

Inductive ValidTransition
          {S    :Set}
          (a a' :Architecture S)
          (pre  :pre_condition)
          (post :post_condition) :=
| valid_transition: pre a -> post a a' -> ValidTransition a a' pre post.

Definition Transition
           {S  :Set}
           (context :ProcessorUnit -> S)
           (a       :Architecture S)
           (ev      :Event S)
           (a'      :Architecture S) :=
  match ev with
  | software DisableInterrupt     => ValidTransition a a' no_pre          disable_interrupt_post
  | software EnableInterrupt      => ValidTransition a a' no_pre          enable_interrupt_post
  | software (Write addr)         => ValidTransition a a' no_pre          (write_post context addr)
  | software (Read addr)          => ValidTransition a a' no_pre          (read_post addr)
  | software OpenSmram            => ValidTransition a a' open_smram_pre  open_smram_post
  | software CloseSmram           => ValidTransition a a' close_smram_pre close_smram_post
  | software LockSmramc           => ValidTransition a a' lock_smramc_pre lock_smramc_post
  | software (NextInstruction pa) => ValidTransition a a' no_pre          (nextinstr_post pa)
  | hardware (ReceiveInterrupt i)
                                  => ValidTransition a a' no_pre          (receive_interrupt_post i)
  | hardware (Exec o)             => ValidTransition a a' (exec_pre o)    (read_post (ip (proc a)))
  end.
