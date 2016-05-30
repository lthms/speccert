Require Import SpecCert.Context.
Require Import SpecCert.Architecture.ProcessorUnit.ProcessorUnit_rec.
Require Import SpecCert.Architecture.ProcessorUnit.ProcessorUnit_prop.
Require Import SpecCert.Architecture.ProcessorUnit.ProcessorUnit_dec.
Require Import SpecCert.Architecture.ProcessorUnit.ProcessorUnit_func.

Lemma enable_interrupt_interrupts_are_enabled:
  forall p p':ProcessorUnit, p' = enable_interrupt p
    -> interrupts_are_enabled p'.
Proof.
  intros p p' Henable.
  rewrite Henable.
  unfold interrupts_are_enabled, enable_interrupt, cli.
  reflexivity.
Qed.

Lemma enable_interrupt_interrupts_are_disabled:
  forall p p':ProcessorUnit, p' = disable_interrupt p
    -> interrupts_are_disabled p'.
Proof.
  intros p p' Henable.
  rewrite Henable.
  unfold interrupts_are_disabled, enable_interrupt, cli.
  reflexivity.
Qed.

Lemma enable_interrupt_context_const:
  forall p p':ProcessorUnit, p' = enable_interrupt p
    -> context p = context p'.
Proof.
  intros p p' Henable.
  rewrite Henable.
  unfold enable_interrupt.
  unfold context.
  reflexivity.
Qed.

Lemma disable_interrupt_context_const:
  forall p p':ProcessorUnit, p' = disable_interrupt p
    -> context p = context p'.
Proof.
  intros p p' Henable.
  rewrite Henable.
  unfold disable_interrupt.
  unfold context.
  reflexivity.
Qed.

Lemma receive_smi_context_is_smm_and_interrupts_are_disabled:
  forall p p':ProcessorUnit,
    p' = receive_smi p -> context p' = smm /\ interrupts_are_disabled p'.
Proof.
  intros p p' Hrec.
  rewrite Hrec.
  unfold receive_smi.
  unfold context.
  unfold interrupts_are_disabled.
  unfold cli.
  split; reflexivity.
Qed.
