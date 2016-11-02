Require Import SpecCert.Address.
Require Import SpecCert.Cache.
Require Import SpecCert.Formalism.
Require Import SpecCert.Memory.
Require Import SpecCert.Smm.Delta.Behavior.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.x86.

Definition invariant := Architecture Software -> Prop.

Definition smramc_inv :=
  fun (a:Architecture Software) =>
    smramc_is_locked (memory_controller a).

Definition smram_code_inv :=
  fun (a:Architecture Software) =>
    forall addr:PhysicalAddress,
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
  fun (h:Architecture Software) =>
    smm_context h = smm
    -> is_inside_smram (ip (proc h)).

Definition smbase_inv :=
  fun (h:Architecture Software) =>
     is_inside_smram (smbase (proc h)).

Definition inv :=
  fun (a:Architecture Software) =>
    smramc_inv a
    /\ smram_code_inv a
    /\ smrr_inv a
    /\ cache_clean_inv a
    /\ ip_inv a
    /\ smbase_inv a.

Definition partial_preserve
           (ev   :x86Event)
           (prop :Architecture Software -> Prop)
           (i    :Architecture Software -> Prop) :=
  forall h h': Architecture Software,
    inv h
    -> prop h
    -> x86_precondition h ev
    -> x86_postcondition smm_context h ev h'
    -> i h'.

Definition software_partial_preserve
           (ev   :SoftwareEvent)
           (prop :Architecture Software -> Prop)
           (i    :Architecture Software -> Prop) :=
  forall h h': Architecture Software,
    inv h
    -> prop h
    -> smm_behavior h ev
    -> x86_precondition h (software ev)
    -> x86_postcondition smm_context h (software ev) h'
    -> i h'.

Definition preserve
           (ev :x86Event)
           (i  :Architecture Software -> Prop) :=
  forall h h': Architecture Software,
    inv h
    -> x86_precondition h ev
    -> x86_postcondition smm_context h ev h'
    -> i h'.

Definition software_preserve
           (ev :SoftwareEvent)
           (i  :Architecture Software -> Prop) :=
  forall h h': Architecture Software,
    inv h
    -> smm_behavior h ev
    -> x86_precondition h (software ev)
    -> x86_postcondition smm_context h (software ev) h'
    -> i h'.

Definition preserve_inv
           (ev:x86Event) :=
  forall h h': Architecture Software,
    inv h
    -> x86_precondition h ev
    -> x86_postcondition smm_context h ev h'
    -> inv h'.

Definition software_preserve_inv
           (ev:SoftwareEvent) :=
  forall h h': Architecture Software,
    inv h
    -> smm_behavior h ev
    -> x86_precondition h (software ev)
    -> x86_postcondition smm_context h (software ev) h'
    -> inv h'.

Definition partial_preserve_inv
           (ev    :x86Event)
           (prop :Architecture Software -> Prop)
  := forall h h': Architecture Software,
    inv h
    -> prop h
    -> x86_precondition h ev
    -> x86_postcondition smm_context h ev h'
    -> inv h'.

Definition software_partial_preserve_inv
           (ev    :SoftwareEvent)
           (prop :Architecture Software -> Prop)
  := forall h h',
    inv h
    -> prop h
    -> smm_behavior h ev
    -> x86_precondition h (software ev)
    -> x86_postcondition smm_context h (software ev) h'
    -> inv h'.

Ltac intros_preserve :=
  let a := fresh "a" in
  let a' := fresh "a'" in
  let Hsmramc := fresh "Hsmramc" in
  let Hsmram := fresh "Hsmram" in
  let Hsmrr := fresh "Hsmrr" in
  let Hclean := fresh "Hclean" in
  let Hip := fresh "Hip" in
  let Hsmbase := fresh "Hsmbase" in
  let Hpre := fresh "Hpre" in
  let Hpost := fresh "Hpost" in
  intros a a' [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hpre Hpost.

Ltac intros_soft_preserve :=
  let a := fresh "a" in
  let a' := fresh "a'" in
  let Hsmramc := fresh "Hsmramc" in
  let Hsmram := fresh "Hsmram" in
  let Hsmrr := fresh "Hsmrr" in
  let Hclean := fresh "Hclean" in
  let Hip := fresh "Hip" in
  let Hsmbase := fresh "Hsmbase" in
  let Hsmm := fresh "Hsmm" in
  let Hpre := fresh "Hpre" in
  let Hpost := fresh "Hpost" in
  intros a a' [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hsmm Hpre Hpost.

Ltac unfold_inv :=
  unfold inv;
  unfold smramc_inv, smram_code_inv, smrr_inv, cache_clean_inv.

Ltac bully_preserve f1 f2 :=
  unfold preserve_inv;
  unfold_inv;
  intros a a' [Hsmramc [Hsmram [Hsmrr Hclean]]] Hpre Hpost;
  unfold x86_postcondition in Hpost;
  unfold f1 in Hpost;
  unfold f2 in Hpost;
  rewrite Hpost;
  simpl;
  do 3 (try split); trivial.
