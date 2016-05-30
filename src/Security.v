(* begin hide *)
Require Import Coq.Classes.RelationClasses.

Require Import SpecCert.x86.
Require Import SpecCert.Defender.
Require Import SpecCert.LTS.
(* end hide *)

(** * Code Injection

    We first give a formal definition of code injection.  For $x, y
    \in \mathcal{S}$ #<em>x</em> and <em>y</em> two software
    components#, we say $x$ #<em>x</em># is performing a code
    injection against #<em>y</em># $y$ if $y$ #<em>y</em># executes an
    instruction which is owned by $x$ #<em>x</em>#.  A code injection
    may or may not be an attack. It depends on the context. For
    instance, an operating system is performing a code injection when
    it loads the code of a process.

 *)

Definition code_injection
           {S       :Set}
           (context :ProcessorUnit -> S)
           (x y     :S)
           (s       :Architecture S)
           (ev      :Event S)
           (s'      :Architecture S)
           :Prop :=
  context (proc s) = y /\ ev = hardware (Exec x).

(** * Security Policy

    We build our security policy upon this definition of code
    injection.

    First, we say that a software component $x$ #<em>x</em># was
    isolated from $y$ #<em>x</em># during an execution $\rho$
    #<em>p</em># if for each transition of $\rho$ #<em>p</em>#, $y$
    #<em>y</em># was not performing a code injection agains $x$
    #<em>x</em>#.

 *)

Inductive software_isolated_execution
                 {S       :Set}
                 {context :ProcessorUnit -> S}
                 (x y     :S)
  :Execution S -> Prop :=
| isolated_one_transition
    (s    :Architecture S)
    (ev   :Event S)
    (s'   :Architecture S)
    (run  :run_of (x86 context) (one_transition s ev s'))
    (ncia : ~code_injection context y x s ev s')
  : software_isolated_execution x y (one_transition s ev s')
| isolated_n_transition
    (p'   :Execution S)
    (ev   :Event S)
    (s'   :Architecture S)
    (run  :run_of (x86 context) (n_transition p' ev s'))
    (siec :software_isolated_execution x y p')
    (ncia : ~ code_injection context y x (last p') ev s')
  : software_isolated_execution x y (n_transition p' ev s').

(** We then give a formal definition of what we call a _secure
    execution_ regarding a given security policy. The security policy
    is a strict and partial order on $\mathcal{S}$ #the software
    components set#.

  *)

Definition secure_execution
           {S       :Set}
           {context :ProcessorUnit -> S}
           {lt      :S -> S -> Prop}
           (policy  :StrictOrder lt)
           (p       :Execution S)
           (run     :run_of (x86 context) p)
           :Prop :=
  forall x y :S,
    lt x y
    -> @software_isolated_execution _ context y x p.

(** We say a defender model enforces a security policy if, each
    compliant execution of the model is secure.

 *)

Definition defender_enforces_security
           {S       :Set}
           {lt      :S -> S -> Prop}
           (context :ProcessorUnit -> S)
           (policy  :StrictOrder lt)
           (def     :Defender S)
           :Prop :=
  forall p   :Execution S,
  forall run :run_of (x86 context) p,
    defender_compliant_execution def p
    -> secure_execution policy p run.

(** * Secured x86 Hardware Platform by design *)


Definition x86Sec
           {S       :Set}
           {lt      :S -> S -> Prop}
           (policy  :StrictOrder lt)
           :HardwarePlatform :=
  fun context =>
    TransRestricted_LTS (x86 context) (secure_transition context policy).

(**
    We first prove that the theorical perfect hardware platform _is_
    secure as we said when we defined it.

 *)

Theorem x86Sec_is_secure
      {S       :Set}
      {lt      :S -> S -> Prop}
      {context :ProcessorUnit -> S} :
  forall policy :StrictOrder lt,
  forall p      :Execution S,
  forall h      :run_of (x86 context) p,
    run_of (x86Sec policy context) p
    -> secure_execution policy p h.
Proof.
  intros policy p.
  induction p; intros h run x y.
  + constructor.
    * exact h.
    * unfold code_injection, not.
      intro Hfalse.
      destruct Hfalse as [Hcontext Hevent].
      unfold run_of in run.
      unfold x86Sec in run.
      unfold TransRestricted_LTS in run.
      destruct run as [[Htrans Hsec] _].
      unfold secure_transition in Hsec.
      rewrite Hevent in Hsec.
      unfold exec_sec in Hsec.
      rewrite Hcontext in Hsec.
      destruct Hsec as [Hsec|Hsec].
      - apply asymmetry in Hsec; [exact Hsec | exact H].
      - rewrite Hsec in H.
        apply irreflexivity in H.
        exact H.
  + constructor; eauto.
    destruct run as [run Hsec].
    destruct h as [h Htrans].
    apply IHp.
    * exact h.
    * exact run.
    * exact H.
    * unfold code_injection, not.
      intro Hfalse.
      destruct Hfalse as [Hcontext Hevent].
      destruct h as [h Htrans].
      destruct run as [run Htr].
      unfold x86Sec in Htr.
      unfold TransRestricted_LTS in Htr.
      destruct Htr as [[Htr Hsec] _].
      rewrite Hevent in Hsec.
      unfold secure_transition, exec_sec in Hsec.
      rewrite Hcontext in Hsec.
      destruct Hsec as [Hsec|Hsec].
      - apply asymmetry in Hsec; [exact Hsec | exact H].
      - rewrite Hsec in H.
        apply irreflexivity in H.
        exact H.
Qed.

(** We also prove an helper lemma, based on the previous result. If
    one can prove that the derived LTS from a defender model is a
    subsystem of ExecSec, then it can conclude this defender model
    enforces the security policy.

 *)

Lemma x86Sec_subsystems_are_secure
      {S       :Set}
      {lt      :S -> S -> Prop}
      {context :ProcessorUnit -> S} :
  forall policy :StrictOrder lt,
  forall def    :Defender S,
    subsystem (derive_computing_system def) (x86Sec policy context)
    -> defender_enforces_security context policy def.
Proof.
  intros policy def Hsub.
  unfold defender_enforces_security.
  intros p run Hcomp.
  unfold defender_compliant_execution in Hcomp.
  eapply (subsystem_derivation _ _ p) in Hsub; [| exact Hcomp].
  apply (x86Sec_is_secure policy p run) in Hsub.
  exact Hsub.
Qed.
