Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.

Require Import SpecCert.Address.
Require Import SpecCert.Formalism.
Require Import SpecCert.Smm.Delta.Behavior.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Secure.Secure_def.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.x86.
Require Import SpecCert.Cache.

Lemma read_inv_is_secure: forall pa:PhysicalAddress,
  inv_is_secure (software (Read pa)).
Proof.
  intro pa.
  trivial_inv_is_secure.
Qed.

Lemma fetch_memory_is_secure:
  forall a :Architecture Software,
    inv a
    -> smm_context a = smm
    -> find_memory_content a (phys_to_hard a (ip (proc a))) = smm.
Proof.
  intros a [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]] Hcont.
  + unfold phys_to_hard, translate_physical_address.
    destruct is_inside_smram_dec.
    * unfold smm_context in Hcont.
      destruct can_access_smram_dec; [| unfold can_access_smram in n;
                                        intuition ].
      rewrite Hsmram; [reflexivity | exact i ].
      destruct is_in_smm_dec; [ apply H in i0
                              ; destruct i0
                              | discriminate ].
    * unfold ip_inv in Hip.
      apply Hip in Hcont.
      apply n in Hcont.
      destruct Hcont.
Qed.

Lemma fetch_cache_is_secure:
  forall a :Architecture Software,
      inv a
      -> smm_context a = smm
      -> cache_hit (cache a) (ip (proc a))
      -> resolve_cache_strategy (proc a) (ip (proc a)) = WriteBack
      -> find_in_cache_location (cache a) (ip (proc a)) = smm.
Proof.
  intros a [_H [_G [Hsmrr [Hclean [Hip _Hs]]]]] Hcont Hres Hcache_hit.
  unfold cache_clean_inv in Hclean.
  unfold resolve_cache_strategy in Hcache_hit.
  remember (ip (proc a)) as pa.
  destruct (is_inside_smram_dec pa).
  + assert (is_inside_smrr (proc a) pa).
    apply Hsmrr; exact i.
    destruct is_inside_smrr_dec; [| intuition ].
    destruct is_in_smm_dec.
    * assert (find_cache_content a pa = Some smm).
      apply (Hclean pa i Hres).
      unfold find_cache_content, find_in_cache in H0.
      destruct (cache_hit_dec (cache a) pa); [| intuition ].
      unfold find_in_cache_location.
      inversion H0.
      rewrite H2.
      reflexivity.
    * discriminate Hcache_hit.
  + unfold ip_inv in Hip.
    case_eq (smm_context a); intro Heqc.
    * apply Hip in Heqc.
      rewrite <- Heqpa in Heqc.
      apply n in Heqc.
      destruct Heqc.
    * unfold smm_security_lt.
      induction (find_in_cache_location (cache a)); [reflexivity|].
      rewrite Hcont in Heqc.
      discriminate.
Qed.

Lemma exec_inv_is_secure:
  forall o :Software,
    inv_is_secure (hardware (Exec o)).
Proof.
  unfold inv_is_secure.
  intros o a a' Hinv Hpre Hpost.
  unfold software_step_isolation, software_tampering, fetched, is.
  intros t u Htrusted Huntrusted.
  apply or_not_and.
  unfold x86_precondition, exec_pre in Hpre.
  unfold In, SmmTCB in Htrusted.
  unfold In, SmmTCB in Huntrusted.
  assert (u = unprivileged) as Hequ; [induction u; [intuition|trivial]|].
  unfold find_address_content in Hpre.
  case_eq (smm_context a); intro Heqc.
  + case_eq (resolve_cache_strategy (proc a) (ip (proc a))); intro Heqstrat; rewrite Heqstrat in Hpre.
    * inversion Hpre.
      rewrite Htrusted.
      rewrite Hequ.
      right.
      rewrite (fetch_memory_is_secure a Hinv Heqc).
      unfold not.
      intro Hfalse.
      discriminate Hfalse.
    * right; destruct (cache_hit_dec); inversion Hpre.
      - rewrite (fetch_cache_is_secure a Hinv Heqc c Heqstrat).
        exact Huntrusted.
      - rewrite (fetch_memory_is_secure a Hinv Heqc).
        rewrite Hequ.
        unfold not.
        intro Hfalse.
        discriminate Hfalse.
    * discriminate.
  + left.
    rewrite Htrusted.
    unfold not.
    intro Hf.
    discriminate.
Qed.
