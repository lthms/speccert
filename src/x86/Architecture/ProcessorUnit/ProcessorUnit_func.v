Require Import SpecCert.x86.Architecture.ProcessorUnit.ProcessorUnit_rec.
Require Import SpecCert.x86.Architecture.ProcessorUnit.ProcessorUnit_prop.
Require Import SpecCert.x86.Architecture.ProcessorUnit.ProcessorUnit_dec.
Require Import SpecCert.Address.
Require Import SpecCert.Cache.

Definition next_instruction
           (p  :ProcessorUnit)
           (pa :PhysicalAddress) :=
  {| in_smm   := (in_smm p)
   ; cli      := (cli p)
   ; strategy := (strategy p)
   ; smrr     := (smrr p)
   ; ip       := pa
   ; smbase   := (smbase p) |}.

Definition enable_interrupt (p:ProcessorUnit) :=
  {| in_smm   := (in_smm p)
   ; cli      := false
   ; strategy := (strategy p)
   ; smrr     := (smrr p)
   ; ip       := (ip p)
   ; smbase   := (smbase p) |}.

Definition disable_interrupt (p:ProcessorUnit) :=
  {| in_smm   := (in_smm p)
   ; cli      := true
   ; strategy := (strategy p)
   ; smrr     := (smrr p)
   ; ip       := (ip p)
   ; smbase   := (smbase p) |}.

Definition receive_smi (p:ProcessorUnit) :=
  {| in_smm   := true
   ; cli      := true
   ; strategy := (strategy p)
   ; smrr     := (smrr p)
   ; ip       := (smbase p)
   ; smbase   := (smbase p) |}.

Definition receive_interrupt (p:ProcessorUnit)(i:Interrupt) :=
  if will_process_interrupt_dec p i then
    (match i with
     | SMI => receive_smi p
     end)
  else p.

Definition resolve_cache_strategy (p:ProcessorUnit)(pa:PhysicalAddress) :=
  if is_inside_smrr_dec p pa then
    if is_in_smm_dec p then
      (smm_strategy (smrr p))
    else
      SmrrHit
  else
    strategy p.