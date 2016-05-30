Require Import SpecCert.Address.
Require Import SpecCert.Security.
Require Import SpecCert.Cache.
Require Import SpecCert.LTS.
Require Import SpecCert.x86.

Require Import SpecCert.Smm.Software.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Secure.Secure_def.

Lemma read_inv_is_secure: forall pa:PhysicalAddress,
  inv_is_secure (software (Read pa)).
Proof.
  unfold inv_is_secure.
  intros pa a a' Hinv Htrans.
  unfold x86Sec, transition.
  simpl.
  unfold trans_cons.
  split; [split | split]; try constructor; try (apply Htrans).
Qed.

Lemma find_memory_is_secure:
  forall a :Architecture Software,
    inv a
    -> smm_security_lt (context (proc a)) (find_memory_content a (phys_to_hard a (ip (proc a))))
    \/ (context (proc a)) = (find_memory_content a (phys_to_hard a (ip (proc a)))).
Proof.
  intros a [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  case_eq (context (proc a)); intro Heqc.
  + unfold phys_to_hard, translate_physical_address.
    destruct is_inside_smram_dec.
    * unfold context in Heqc.
      destruct can_access_smram_dec; [| unfold can_access_smram in n;
                                        intuition ].
      right.
      rewrite Hsmram; [reflexivity | exact i ].
      destruct is_in_smm_dec; [ apply H in i0
                              ; destruct i0
                              | discriminate ].
    * unfold ip_inv in Hip.
      apply Hip in Heqc.
      apply n in Heqc.
      destruct Heqc.
  + unfold smm_security_lt.
    induction (find_memory_content a (phys_to_hard a (ip (proc a)))).
    * left; auto.
    * right; reflexivity.
Qed.

Lemma find_cache_is_secure:
  forall a :Architecture Software,
      inv a
      -> cache_hit (cache a) (ip (proc a))
      -> resolve_cache_strategy (proc a) (ip (proc a)) = WriteBack
      -> smm_security_lt (context (proc a)) (find_in_cache_location (cache a) (ip (proc a)))
      \/ (context (proc a)) = (find_in_cache_location (cache a) (ip (proc a))).
Proof.
  intros a [_H [_G [Hsmrr [Hclean [Hip _Hs]]]]] Hres Hcache_hit.
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
      induction (context (proc a)); [right; auto|left;reflexivity].
    * discriminate Hcache_hit.
  + unfold ip_inv in Hip.
    case_eq (context (proc a)); intro Heqc.
    * apply Hip in Heqc.
      rewrite <- Heqpa in Heqc.
      apply n in Heqc.
      destruct Heqc.
    * unfold smm_security_lt.
      induction (find_in_cache_location (cache a)); [left; auto|right;reflexivity].
Qed.

Lemma exec_inv_is_secure:
  forall o :Software,
    inv_is_secure (hardware (Exec o)).
Proof.
  unfold inv_is_secure.
  intros o a a' Hinv Htrans.
  inversion Htrans as [Hpre Hpost].
  unfold x86Sec, secure_transition, TransRestricted_LTS.
  simpl.
  unfold trans_cons.
  split; trivial.
  split.
  exact Htrans.
  unfold exec_sec.
  unfold exec_pre in Hpre.
  unfold find_address_content in Hpre.
  case_eq (resolve_cache_strategy (proc a) (ip (proc a))); intro Heqstrat; rewrite Heqstrat in Hpre.
  + inversion Hpre.
    apply (find_memory_is_secure a Hinv).
  + destruct (cache_hit_dec); inversion Hpre.
    * apply (find_cache_is_secure a Hinv c Heqstrat).
    * apply (find_memory_is_secure a Hinv).
  + discriminate.
  + repeat constructor.
Qed.