Require Import SpecCert.Address.
Require Import SpecCert.Memory.
Require Import SpecCert.Cache.
Require Import SpecCert.x86.

Require Import SpecCert.Smm.Software.
Require Import SpecCert.Smm.Delta.Behavior.

Definition invariant := Architecture Software -> Prop.

Definition smramc_inv :=
  fun (a:Architecture Software) =>
    smramc_is_locked (memory_controller a).

Definition smram_code_inv :=
  fun (a:Architecture Software) =>
    forall addr:Address,
      is_inside_smram addr -> find_memory_content a (dram addr) = smm.

Definition smrr_inv :=
  fun (a:Architecture Software) =>
    forall pa:PhysicalAddress, is_inside_smram pa -> is_inside_smrr (proc a) pa.

Definition cache_clean_inv :=
  fun (a:Architecture Software) =>
    forall pa:PhysicalAddress, is_inside_smram pa
                          -> cache_hit (cache a) pa
                          -> find_cache_content a pa = Some smm.

Definition ip_inv :=
  fun (a:Architecture Software) =>
    context (proc a) = smm
    -> is_inside_smram (ip (proc a)).

Definition smbase_inv :=
  fun (a:Architecture Software) =>
     is_inside_smram (smbase (proc a)).

Definition inv :=
  fun (a:Architecture Software) =>
    smramc_inv a
    /\ smram_code_inv a
    /\ smrr_inv a
    /\ cache_clean_inv a
    /\ ip_inv a
    /\ smbase_inv a.

Definition partial_preserve
           (ev   :Event Software)
           (prop :Architecture Software -> Prop)
           (i    :Architecture Software -> Prop) :=
  forall a a',
    inv a -> prop a -> Transition context a ev a' -> i a'.

Definition software_partial_preserve
           (ev   :SoftwareEvent)
           (prop :Architecture Software -> Prop)
           (i    :Architecture Software -> Prop) :=
  forall a a',
    inv a -> prop a -> smm_behavior a ev -> Transition context a (software ev) a' -> i a'.

Definition preserve
           (ev :Event Software)
           (i  :Architecture Software -> Prop) :=
  forall a a',
    inv a -> Transition context a ev a' -> i a'.

Definition software_preserve
           (ev :SoftwareEvent)
           (i  :Architecture Software -> Prop) :=
  forall a a',
    inv a -> smm_behavior a ev -> Transition context a (software ev) a' -> i a'.

Definition preserve_inv
           (ev:Event Software) :=
  forall a a',
    inv a -> Transition context a ev a' -> inv a'.

Definition software_preserve_inv
           (ev:SoftwareEvent) :=
  forall a a',
    inv a -> smm_behavior a ev -> Transition context a (software ev) a' -> inv a'.

Definition partial_preserve_inv

           (ev    :Event Software)
           (prop :Architecture Software -> Prop)
  := forall a a',
    inv a -> prop a -> Transition context a ev a' -> inv a'.

Definition software_partial_preserve_inv
           (ev    :SoftwareEvent)
           (prop :Architecture Software -> Prop)
  := forall a a',
    inv a -> prop a -> smm_behavior a ev -> Transition context a (software ev) a' -> inv a'.