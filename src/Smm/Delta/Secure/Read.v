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

Lemma read_inv_is_secure:
  forall (pa:PhysicalAddress) (v: Value),
    inv_is_secure (software (Read pa v)).
Proof.
  intros pa v.
  trivial_inv_is_secure.
Qed.

Lemma fetch_memory_is_secure
      (a:     Architecture Software)
      (val:   Value)
      (s:     Software)
      (Hinv:  inv a)
      (Hcont: smm_context a = smm)
      (Hfind: find_memory_content a (phys_to_hard a (ip (proc a))) = (val, s))
  : s = smm.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  unfold phys_to_hard, translate_physical_address in Hfind.
  unfold smm_context in Hcont.
  assert (is_in_smm (proc a))
    by (destruct is_in_smm_dec as [Hsmm|_Hnsmm]; [exact Hsmm|discriminate]).
  destruct is_inside_smram_dec as [Hin|Hout].
  + destruct can_access_smram_dec.
    * remember (find_memory_content a (dram (ip (proc a)))) as cx.
      destruct cx as [v' s'].
      inversion Hfind.
      apply (Hsmram (ip (proc a)) val s Hin).
      symmetry.
      rewrite <- H1; rewrite <- H2.
      exact Heqcx.
    * unfold can_access_smram in n.
      apply not_or_and in n.
      destruct n as [Hfalse _H].
      intuition.
  + unfold ip_inv in Hip.
    apply Hip in Hcont.
    apply Hout in Hcont.
    destruct Hcont.
Qed.

Lemma fetch_cache_is_secure
      (a:          Architecture Software)
      (val:        Value)
      (s:          Software)
      (Hinv:       inv a)
      (Hcont:      smm_context a = smm)
      (Hres:       resolve_cache_strategy (proc a) (ip (proc a)) = WriteBack)
      (Hcache_hit: cache_hit (cache a) (ip (proc a)))
      (Hfind:      find_in_cache_location (cache a) (ip (proc a)) = (val, s))
  : s = smm.
Proof.
  destruct Hinv as [Hsmramc [Hsmram [Hsmrr [Hclean [Hip Hsmbase]]]]].
  unfold cache_clean_inv in Hclean.
  unfold resolve_cache_strategy in Hres.
  remember (ip (proc a)) as pa.
  destruct (is_inside_smram_dec pa).
  + assert (is_inside_smrr (proc a) pa)
      by (apply Hsmrr; exact i).
    destruct is_inside_smrr_dec; [| intuition ].
    destruct is_in_smm_dec.
    * apply (Hclean pa val s i Hcache_hit).
      unfold find_in_cache_location in Hfind.
      unfold find_cache_content, find_in_cache.
      destruct cache_hit_dec; [|intuition].
      rewrite Hfind.
      reflexivity.
    * discriminate Hres.
  + unfold ip_inv in Hip.
    case_eq (smm_context a); intro Heqc.
    * apply Hip in Heqc.
      rewrite <- Heqpa in Heqc.
      apply n in Heqc.
      destruct Heqc.
    * rewrite Hcont in Heqc.
      discriminate.
Qed.

Lemma exec_inv_is_secure
      (v: Value)
  : inv_is_secure (hardware (Exec v)).
Proof.
  unfold inv_is_secure.
  intros a a' Hinv Hpre Hpost.
  unfold software_step_isolation, software_tampering, fetched, is.
  intros t u Htrusted Huntrusted.
  apply or_not_and.
  unfold x86_precondition in Hpre.
  unfold In, SmmTCB in Htrusted.
  unfold In, SmmTCB in Huntrusted.
  assert (u = unprivileged) as Hequ; [induction u; [intuition|trivial]|].
  unfold find_address_content.
  case_eq (smm_context a); intro Heqc.
  + case_eq (resolve_cache_strategy (proc a) (ip (proc a))); intro Heqstrat.
    * rewrite Hequ.
      right.
      unfold option_map.
      remember (find_memory_content a (phys_to_hard a (ip (proc a)))) as c.
      destruct c as [v' s].
      simpl.
      assert (s = smm).
      apply (fetch_memory_is_secure a v' s Hinv Heqc).
      symmetry.
      exact Heqc0.
      rewrite H.
      intro Hfalse.
      discriminate.
    * right; destruct (cache_hit_dec).
      - unfold option_map.
        remember (find_in_cache_location (cache a) (ip (proc a))) as cx.
        destruct cx as [v' s].
        simpl.
        assert (s = smm).
        apply (fetch_cache_is_secure a v' s Hinv Heqc Heqstrat c).
        symmetry.
        exact Heqcx.
        rewrite H.
        rewrite Hequ.
        intro Hfalse.
        discriminate.
      - unfold option_map.
        remember (find_memory_content a (phys_to_hard a (ip (proc a)))) as c.
        destruct c as [v' s].
        simpl.
        assert (s = smm).
        apply (fetch_memory_is_secure a v' s Hinv Heqc).
        symmetry.
        exact Heqc0.
        rewrite H.
        intro Hfalse.
        rewrite Hequ in Hfalse.
        discriminate.
    * right.
      intro P; exact P.
  + left.
    rewrite Htrusted.
    unfold not.
    intro Hf.
    discriminate.
Qed.
