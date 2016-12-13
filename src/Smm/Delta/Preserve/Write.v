Require Import Coq.Logic.Classical_Prop.

Require Import SpecCert.Address.
Require Import SpecCert.Cache.
Require Import SpecCert.Formalism.
Require Import SpecCert.Interval.
Require Import SpecCert.Map.
Require Import SpecCert.Memory.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Preserve.Architecture.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.x86.

Lemma write_strat_uc:
  forall (pa :PhysicalAddress) (v: Value),
    partial_preserve (software (Write pa v))
                     (fun a => resolve_cache_strategy (proc a) pa = Uncachable)
                     inv.
Proof.
  unfold partial_preserve.
  intros pa v a a' Hinv Hsmm_strat Hpre Hpost.
  unfold x86_postcondition, write_post in Hpost.
  rewrite Hsmm_strat in Hpost.
  unfold write_uncachable in Hpost.
  apply (update_memory_content_with_context_preserves_inv a a' pa v Hinv Hpost).
Qed.

Lemma write_strat_sh:
  forall (pa :PhysicalAddress) (v: Value),
    partial_preserve (software (Write pa v))
                     (fun a => resolve_cache_strategy (proc a) pa = SmrrHit)
                     inv.
Proof.
  unfold partial_preserve.
  intros pa v a a' Hinv Hsmm_strat Hpre Hpost.
  unfold x86_postcondition, write_post in Hpost.
  rewrite Hsmm_strat in Hpost.
  unfold write_smrrhit in Hpost.
  rewrite Hpost.
  exact Hinv.
Qed.

Lemma write_strat_smrr_wb:
  forall (pa :PhysicalAddress) (v: Value),
    partial_preserve (software (Write pa v))
                     (fun a => is_inside_smrr (proc a) pa
                            /\ smm_strategy (smrr (proc a)) = WriteBack)
                     inv.
Proof.
  unfold partial_preserve.
  intros pa v a a' Hinv [Hinside_smrr Hsmm_strat] Hpre Hpost.
  unfold x86_postcondition, write_post, resolve_cache_strategy in Hpost.
  destruct is_inside_smrr_dec; [| intuition ].
  destruct is_in_smm_dec as [Hin_smm|Hnot].
  + rewrite Hsmm_strat in Hpost.
    unfold write_writeback in Hpost.
    assert (is_inside_smram pa -> is_in_smm (proc a)); [
        intro Hin;
        exact Hin_smm |].
    destruct cache_hit_dec.
    * apply (update_cache_content_with_context_preserves_inv a a' pa v Hinv H Hpost).
    * remember (load_in_cache_from_memory a pa) as a''.
      assert (inv a'') as Hinv''; [
          apply (load_in_cache_from_memory_preserves_inv a a'' pa Hinv H Heqa'') |].
      assert (proc a = proc a'').
      apply load_in_cache_from_memory_changes_only_mem_and_cache in Heqa'' as [Hproc Hmc].
      rewrite <- Hproc.
      reflexivity.
      assert (is_in_smm (proc a'')).
      rewrite <- H0.
      exact Hin_smm.
      assert (is_inside_smram pa -> is_in_smm (proc a'')); [
        intro Hin;
          exact H1 |].
      rewrite (context_is_preserves a a'' H0) in Hpost.
      eapply (update_cache_content_with_context_preserves_inv a'' a' pa v Hinv'' H2 Hpost).
  + unfold write_smrrhit in Hpost.
    rewrite Hpost.
    exact Hinv.
Qed.

Lemma write_not_smrr:
  forall (pa :PhysicalAddress) (v: Value),
    partial_preserve (software (Write pa v))
                     (fun a => ~ is_inside_smrr (proc a) pa)
                     inv.
Proof.
  unfold partial_preserve.
  intros pa v a a' Hinv Hnot_inside_smrr Hpre Hpost.
  unfold x86_postcondition in Hpost;
  unfold x86_precondition in Hpre.
  assert (write_post smm_context pa v a a') as Hx; [unfold x86_postcondition in Hpost; exact Hpost |].
  remember (resolve_cache_strategy (proc a) pa) as strat.
  unfold write_post in Hpost.
  assert (strat = strategy (proc a)).
  unfold resolve_cache_strategy in Heqstrat.
  destruct is_inside_smrr_dec; [ intuition |].
  exact Heqstrat.
  case_eq (resolve_cache_strategy (proc a) pa); intro Hres; rewrite Hres in Hpost.
  + apply (write_strat_uc pa v a a' Hinv Hres Hpre Hx).
  + destruct (is_inside_smrr_dec (proc a) pa); [ intuition |].
    unfold write_writeback in Hpost.
    assert (is_inside_smram pa -> is_in_smm (proc a)).
    intro Hfalse.
    destruct Hinv as [Hsmramc [Hsmram [Hsmrr Hclean]]].
    apply Hsmrr in Hfalse.
    apply n in Hfalse.
    destruct Hfalse.
    destruct (cache_hit_dec (cache a) pa).
    * apply (update_cache_content_with_context_preserves_inv a a' pa v Hinv H0 Hpost).
    * apply (load_then_update_cache_with_context_preserves_inv a a' pa v Hinv H0 Hpost).
 + apply (write_strat_sh pa v a a' Hinv Hres Hpre Hx).
Qed.

Lemma write_inv:
  forall (pa :PhysicalAddress) (v: Value),
    preserve (software (Write pa v)) inv.
Proof.
  unfold preserve.
  intros pa v a a' Hinv Htrans.
  destruct (is_inside_smrr_dec (proc a) pa).
  + case_eq (resolve_cache_strategy (proc a) pa); intro Hres.
    * apply (write_strat_uc pa v a a' Hinv Hres Htrans).
    * assert (is_inside_smrr (proc a) pa /\ smm_strategy (smrr (proc a)) = WriteBack).
      split; [ exact i |].
      unfold resolve_cache_strategy in Hres.
      destruct is_inside_smrr_dec; [| intuition ].
      destruct is_in_smm_dec; [| discriminate Hres ].
      exact Hres.
      apply (write_strat_smrr_wb pa v a a' Hinv H Htrans).
    * apply (write_strat_sh pa v a a' Hinv Hres Htrans).
  + apply (write_not_smrr pa v a a' Hinv n Htrans).
Qed.
