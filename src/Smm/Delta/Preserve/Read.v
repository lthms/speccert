Require Import SpecCert.Address.
Require Import SpecCert.Cache.
Require Import SpecCert.Interval.
Require Import SpecCert.Memory.
Require Import SpecCert.x86.

Require Import SpecCert.Smm.Software.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Preserve.Architecture.

Require Import Coq.Logic.Classical_Prop.

Lemma read_strat_uc:
  forall pa :PhysicalAddress,
      partial_preserve (software (Read pa))
                       (fun a => resolve_cache_strategy (proc a) pa = Uncachable)
                       inv.
Proof.
  unfold partial_preserve.
  intros pa a a' Hinv Hres [Hpre Hpost].
  unfold read_post in Hpost.
  rewrite Hres in Hpost.
  unfold read_uncachable_post in Hpost.
  rewrite Hpost.
  exact Hinv.
Qed.

Lemma read_strat_sh:
  forall pa :PhysicalAddress,
      partial_preserve (software (Read pa))
                       (fun a => resolve_cache_strategy (proc a) pa = SmrrHit)
                       inv.
Proof.
  unfold partial_preserve.
  intros pa a a' Hinv Hres [Hpre Hpost].
  unfold read_post in Hpost.
  rewrite Hres in Hpost.
  unfold read_smrrhit_post in Hpost.
  rewrite Hpost.
  exact Hinv.
Qed.

Lemma read_strat_smrr_wb:
  forall pa :PhysicalAddress,
      partial_preserve (software (Read pa))
                       (fun a => is_inside_smrr (proc a) pa
                              /\ smm_strategy (smrr (proc a)) = WriteBack)
                       inv.
Proof.
  unfold partial_preserve.
  intros pa a a' Hinv [Hsmrr Hsmm] [Hpre Hpost].
  unfold read_post in Hpost.
  unfold resolve_cache_strategy in Hpost.
  destruct is_inside_smrr_dec; [| intuition ].
  destruct is_in_smm_dec.
  + rewrite Hsmm in Hpost.
    unfold read_writeback_post in Hpost.
    destruct cache_hit_dec.
    * rewrite Hpost.
      exact Hinv.
    * assert (is_inside_smram pa -> is_in_smm (proc a)).
      intro H; exact i0.
      apply (load_in_cache_from_memory_preserves_inv a a' pa Hinv H Hpost).
  + unfold read_smrrhit_post in Hpost.
    rewrite Hpost.
    exact Hinv.
Qed.

Lemma read_strat_not_smrr:
  forall pa :PhysicalAddress,
      partial_preserve (software (Read pa))
                       (fun a => ~ is_inside_smrr (proc a) pa)
                       inv.
Proof.
  unfold partial_preserve.
  intros pa a a' Hinv Hnot_smrr [Hpre Hpost].
  unfold read_post in Hpost.
  unfold resolve_cache_strategy in Hpost.
  destruct is_inside_smrr_dec; [ intuition |].
  case_eq (strategy (proc a)); intro Heqstrat; rewrite Heqstrat in Hpost.
  + unfold read_uncachable_post in Hpost.
    rewrite Hpost.
    exact Hinv.
  + unfold read_writeback_post in Hpost.
    destruct cache_hit_dec.
    * rewrite Hpost; exact Hinv.
    * assert (is_inside_smram pa -> is_in_smm (proc a)).
      intro H.
      destruct Hinv as [Hsmramc [Hsmram [Hsmrr Hclean]]].
      apply Hsmrr in H.
      intuition.
      apply (load_in_cache_from_memory_preserves_inv a a' pa Hinv H Hpost).
  + unfold read_smrrhit_post in Hpost.
    rewrite Hpost.
    exact Hinv.
Qed.

Lemma read_inv:
  forall pa :PhysicalAddress,
      preserve (software (Read pa)) inv.
Proof.
  unfold preserve.
  intros pa a a' Hinv Htrans.
  case_eq (resolve_cache_strategy (proc a) pa); intro Heqstrat.
  + apply (read_strat_uc pa a a' Hinv Heqstrat Htrans).
  + destruct (is_inside_smrr_dec (proc a) pa).
    * unfold resolve_cache_strategy in Heqstrat.
      destruct is_inside_smrr_dec; [| intuition ].
      destruct is_in_smm_dec; [| discriminate ].
      assert (is_inside_smrr (proc a) pa /\ smm_strategy (smrr (proc a)) = WriteBack); [
          split; trivial
         |].
      apply (read_strat_smrr_wb pa a a' Hinv H Htrans).
    * apply (read_strat_not_smrr pa a a' Hinv n Htrans).
  + apply (read_strat_sh pa a a' Hinv Heqstrat Htrans).
Qed.

Lemma exec_inv:
  forall o :Software,
    preserve (hardware (Exec o)) inv.
Proof.
  unfold preserve.
  intros o a a' Hinv Htrans.
  apply (read_inv (ip (proc a)) a a'); [ exact Hinv
                                       | destruct Htrans
                                       ; constructor ].
  + unfold no_pre; trivial.
  + exact r.
Qed.