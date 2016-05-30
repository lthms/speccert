Require Import SpecCert.Address.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_rec.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_eq.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_prop.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_dec.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_func.

Lemma open_smram_can_access_smram:
  forall mc mc' :MemoryController,
  forall h,
    mc' = open_smram mc h -> forall smiact:bool, can_access_smram mc' smiact.
Proof.
  intros mc mc' h Hmc' c.
  unfold open_smram in Hmc'.
  induction mc' as [smramc'].
  inversion Hmc' as [Hsmramc'].
  rewrite <- Hsmramc'.
  apply set_d_open_d_open_is_true in Hsmramc'.
  unfold can_access_smram.
  right.
  unfold smramc.
  trivial.
Qed.

Lemma close_smram_can_access_smram_if_context_smm:
  forall mc mc':MemoryController,
  forall h,
  forall smiact:bool,
    mc' = close_smram mc h -> can_access_smram mc' smiact
    -> smiact = true.
Proof.
  intros mc mc' h smiact Hmc' Hcan.
  unfold can_access_smram in Hcan.
  induction mc' as [smramc'].
  inversion Hmc' as [Hsmramc'].
  apply unset_d_open_d_open_is_false in Hsmramc'.
  unfold smramc in Hcan.
  rewrite Hsmramc' in Hcan.
  destruct Hcan; trivial.
  discriminate H.
Qed.

Lemma lock_smramc_smramc_is_lock:
  forall mc mc':MemoryController,
  forall h,
  mc' = lock_smramc mc h
  -> smramc_is_locked mc'.
Proof.
  intros mc mc' h Hmc'.
  induction mc' as [smramc'].
  unfold lock_smramc in Hmc'.
  inversion Hmc' as [Hsmramc'].
  rewrite <- Hsmramc'.
  apply set_d_lock_d_lock_is_true_d_open_is_false in Hsmramc'.
  unfold smramc_is_locked, smramc_is_ro.
  unfold smramc.
  destruct Hsmramc'.
  trivial.
Qed.

(* WARNING: Temporary Lemma that will not be true with address remapping *)
Lemma pa_neq_ha_translate_diff:
  forall mc     :MemoryController,
  forall smiact :bool,
  forall pa     :PhysicalAddress,
  forall ha     :HardwareAddress,
    pa <> hardware_address ha
    -> translate_physical_address mc smiact pa <> ha.
Proof.
  intros mc smiact pa ha Hdiff.
  unfold translate_physical_address.
  destruct (is_inside_smram_dec pa).
  + destruct (can_access_smram_dec mc smiact);
      intuition;
      rewrite <-H in Hdiff;
      unfold hardware_address in Hdiff;
      intuition.
  + unfold not.
    unfold not in Hdiff.
    intro Hdram.
    rewrite <- Hdram in Hdiff.
    simpl; intuition.
Qed.
