From sflib Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement.
From Coq Require Import Strings.String List.
From Tutorial Require Import Imp FiniteSimulation.

Require Import ZArith.
Require Import Zwf.
Require Import Lia.

Set Implicit Arguments.

Section DEMO.
  (** We will prove that src refines tgt, using the finite simulation. *)

  Definition src0 : com :=
    <{ ret 0 }>.

  Definition tgt0 : com :=
    <{ "x" := (1 + 1); "y" := (2 * 1 - "x"); ret "y" }>.

  Goal refines (Imp_Program_Mem src0) (Imp_Program_Mem tgt0).
  Proof.
    apply adequacy. unfold simulation, Imp_Program_Mem, Imp_STS_Mem, src0, tgt0, Imp_init. ss.
    (* Same as 'econstructor 4.' or 'eapply sim_silentT.' *)
    econs 4.
    { ss. }
    ss. i. inv H.
    (* We have two cases: 1. normal step, 2. step is not defined.
       Step is defined for this case, so the second case is trivially solved.
     *)
    2:{ exfalso. eapply UNDEF. repeat econs. }
    inv STEP. ss. split; auto.
    econs 4.
    { ss. }
    ss. i. inv H.
    2:{ exfalso. eapply UNDEF. repeat econs. }
    inv STEP. ss. split; auto.
    (* As you can see, simulation proofs can get very length.
       Thus one usually defines a tactic that automatically takes care of trivial steps.
       So let us define some simple tactics first.
     *)
  Abort.

  (** Note that a tactic defined inside a section can only be used in that section, in general. *)

  (* Solves tgt undef case if tgt is not undef. *)
  Ltac solve_tgt_ub :=
    exfalso;
    match goal with
    | [UNDEF : forall _ _, ~ (ceval _ _ _) |- _] => eapply UNDEF
    end;
    repeat econs.

  (* Makes a tgt step. *)
  Ltac step_tgt_silent0 :=
    match goal with
    | [STEP: ceval _ _ _ |- _] => inv STEP
    end;
    ss; split; auto.

  (* Combines above two tactics. *)
  Ltac step_tgt_silent :=
    try (econs 4;
         [ss
         | ss; intros ev st_tgt1 STEP0; inv STEP0;
           [step_tgt_silent0 | solve_tgt_ub]
        ]).

  Goal refines (Imp_Program_Mem src0) (Imp_Program_Mem tgt0).
  Proof.
    apply adequacy. unfold simulation, Imp_Program_Mem, Imp_STS_Mem, src0, tgt0, Imp_init. ss.
    step_tgt_silent.
    step_tgt_silent.
    inv H6. inv H4. inv H5. ss.
    (* We can take multiple steps like this: *)
    do 3 step_tgt_silent.
    inv H6. inv H4. inv H5. inv H6. inv H7. inv H1. ss.
    step_tgt_silent.
    (* Now evaluate return commands.
       When both src and tgt needs to progress, usually taking tgt step first is better;
       we are usually proving 'forall tgt event, exists src event'.
     *)
    step_tgt_silent.
    inv H5. inv H1.
    (* Now take src step. *)
    econs 3.
    { ss. }
    ss. exists (inr LInternal). eexists. split.
    { econs. econs. econs.
      (* Coq detects correct constructors for this case.
         Same as 'eapply Step_normal. eapply E_Ret. eapply E_ANum.'. *)
    }
    ss. split; auto.
    (* There is only one possible constructor for this: 'sim_term'. *)
    econs.
    { simpl. eauto. }
    { simpl. eauto. }
    { auto. }
  Qed.

End DEMO.

Section EX.
  (** Prove the following refinements. Develop tactics to simplify proofs. *)

  (* Solves tgt undef case if tgt is not undef. *)
  Ltac solve_tgt_ub :=
    exfalso;
    match goal with
    | [UNDEF : forall _ _, ~ (ceval _ _ _) |- _] => eapply UNDEF
    end;
    repeat econs.

  (* Makes a tgt step. *)
  Ltac step_tgt_silent0 :=
    match goal with
    | [STEP: ceval _ _ _ |- _] => inv STEP
    end;
    ss; split; auto.

  (* Combines above two tactics. *)
  Ltac step_tgt_silent :=
    try (econs 4;
         [ss
         | ss; intros ev st_tgt1 STEP0; inv STEP0;
           [step_tgt_silent0 | solve_tgt_ub]
        ]).

  Ltac step_src_silent :=
    try (econs 3;
         ss; exists (inr LInternal); eexists; split;
         [repeat econs | ss; split; auto]).

  Ltac step_term :=
    try (econs;
         [ simpl; eauto
           | simpl; eauto
           | reflexivity ]).

  (* Ex1. Interactions with the external world is observable, so should be preserved. *)
  Definition src1 : com :=
    <{ "a" :=@ "print" <[0 : aexp]>; ret "a" }>.

  Definition tgt1 : com :=
    <{ "x" := 0; "y" :=@ "print" <["x" : aexp]>; ret "y" }>.

  Goal refines (Imp_Program_Mem src1) (Imp_Program_Mem tgt1).
  Proof.
    apply adequacy. unfold simulation, Imp_Program1, Imp_STS1, src1, tgt1, Imp_init. ss.
    (* Make steps in tgt *)
    do 2 step_tgt_silent.
    inv H6.
    do 2 step_tgt_silent.
    (* Make a step in src *)
    step_src_silent.

    (* Make steps in both src and tgt *)
    econs 2; ss.
    intros ev st_tgt1 STEP0; inv STEP0.
    (* When tgt step is undef *)
    2:{ solve_tgt_ub. Unshelve. exact 1. }
    (* When tgt step is defined *)
    inv STEP. inv H7. inv H1. inv H3. inv H2.
    ss; split; auto.
    eexists. split.
    { repeat econs. }

    step_tgt_silent.
    step_src_silent.

    step_tgt_silent.
    inv H5. inv H1.
    step_src_silent.

    step_term.
  Qed.

  (* Ex2. If semantics is given by Imp_STS_Mem, memory accesses are also observable. *)
  Definition src2 : com :=
    <{ &<1> := 5; "a" := &<1>; ret "a" }>.

  Definition tgt2 : com :=
    <{ "x" := 2; &<1> := ("x" + 3); "y" := &<1>; ret "y" }>.

  Goal refines (Imp_Program_Mem src2) (Imp_Program_Mem tgt2).
  Proof.
    apply adequacy. unfold simulation, Imp_Program1, Imp_STS1, src2, tgt2, Imp_init. ss.
    (* Make a step in tgt *)
    do 2 step_tgt_silent.
    inv H6.
    do 2 step_tgt_silent.
    step_src_silent.

    (* Make steps in both src and tgt *)
    econs 2; ss.
    intros ev st_tgt1 STEP0; inv STEP0.
    2:{ solve_tgt_ub. }
    inv STEP. inv H6. inv H4. inv H5. inv H1.
    ss; split; auto.
    eexists. split.
    { repeat econs. }

    do 2 step_src_silent.
    do 2 step_tgt_silent.
    econs 2; ss.
    intros ev st_tgt1 STEP0; inv STEP0.
    2:{ solve_tgt_ub. }
    inv STEP. inv H6.
    ss; split; auto.
    eexists. split.
    { repeat econs. }

    do 2 step_src_silent.
    do 2 step_tgt_silent.
    inv H5. inv H1.

    step_term.
  Qed.

  (* But, if we want to reason about compiler optimizations, for example, we do not want to keep memory accesses.
     Imp_STS_Ext is the right semantics for this. 
   *)
  Definition src2' : com :=
    <{ ret 5 }>.

  Goal refines (Imp_Program_Ext src2') (Imp_Program_Ext tgt2).
  Proof.
    apply adequacy. unfold simulation, Imp_Program2, Imp_STS2, src2', tgt2, Imp_init. ss.

    (* Make silent steps in tgt until ret *)
    do 3 step_tgt_silent.
    do 3 step_tgt_silent.
    do 3 step_tgt_silent.
    inv H6. inv H8. inv H7. inv H4. inv H5. inv H1. ss.

    step_src_silent.
    step_tgt_silent.
    inv H5. inv H1.

    step_term.
  Qed.


  (* Ex3. If the source program can exhibit UB, refinement always holds. *)
  Definition src3 : com :=
    <{ ret "a" }>.

  Goal forall tgt, refines (Imp_Program_Mem src3) (Imp_Program_Mem tgt).
  Proof.
    intros tgt.
    apply adequacy. unfold simulation, Imp_Program1, Imp_STS1, src3, Imp_init. ss.
    econs 3.
    { ss. }
    ss. exists (inr LInternal).  exists (Mem.init, Undef).
    econs. eapply Step_undefined. unfold not.
    intros. inv H. inv H6. inv H1.
    ss; split; auto.
  Qed.

  (* Ex4. If a loop always terminates, we can prove it by induction. *)
  Definition src4 : com :=
    <{ ret 0 }>.

  Definition tgt4 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := ("x" - 1))
       end;
       ret "x"
      }>.

  Goal refines (Imp_Program_Mem src4) (Imp_Program_Mem tgt4).
  Proof.
    apply adequacy. unfold simulation, Imp_Program1, Imp_STS1, src4, tgt4, Imp_init. ss.
    step_src_silent.
    do 4 step_tgt_silent.
    inv H6.
    remember Reg.init as reg. clear Heqreg.
    remember 100 as n.
    assert (CASES : (n = 0 \/ 0 < n)%Z). by lia.
    clear Heqn.
    revert reg.

    induction n using (well_founded_ind (Zwf.Zwf_well_founded 0)).
    destruct CASES as [CEq | CGt].
    - rewrite CEq in H.
      rewrite <- CEq.
      step_tgt_silent.
      + inv H7. inv H2.
        do 2 step_tgt_silent.
        inv H6. inv H2.
        step_term.
      + rename H8 into TRUE.
        step_tgt_silent.
        inv H8. inv H7. inv H2.
        contradiction.
    - step_tgt_silent.
      + step_tgt_silent.
        inv H7. inv H2.
        ss.
      + rename H8 into TRUE.
        inv H7. inv H2.
        step_tgt_silent.
        step_tgt_silent.
        apply H.
        { unfold Zwf. split.
          - lia.
          - inv H7. inv H5. inv H6. inv H2. ss. lia. }
        { inv H7. inv H5. inv H6. inv H2. ss. lia. }
      + exfalso. destruct (Z.eqb n 0) eqn:CASES.
        { eapply UNDEF. eapply E_WhileFalse. repeat econs. apply Z.eqb_eq; auto. }
        { eapply UNDEF. eapply E_WhileTrue. repeat econs. apply Z.eqb_neq; auto. }
  Qed.

End EX.

Section DIV.
  (** Simulation in current form can't prove refinement between possibly diverging programs. *)

  Ltac solve_tgt_ub :=
    exfalso;
    match goal with
    | [UNDEF : forall _ _, ~ (ceval _ _ _) |- _] => eapply UNDEF
    end;
    repeat econs.

  (* Makes a tgt step. *)
  Ltac step_tgt_silent0 :=
    match goal with
    | [STEP: ceval _ _ _ |- _] => inv STEP
    end;
    ss; split; auto.

  (* Combines above two tactics. *)
  Ltac step_tgt_silent :=
    try (econs 4;
         [ss
         | ss; intros ev st_tgt1 STEP0; inv STEP0;
           [step_tgt_silent0 | solve_tgt_ub]
        ]).

  Ltac step_src_silent :=
    try (econs 3;
         ss; exists (inr LInternal); eexists; split;
         [repeat econs | ss; split; auto]).

  Ltac step_term :=
    try (econs;
         [ simpl; eauto
           | simpl; eauto
           | reflexivity ]).


  (* DIV1. We can prove the following refinement, which always terminates. *)
  Definition src5 : com :=
    <{ "x" := 100;
       while ("x")
       do ("a" :=@ "print" <["x" : aexp]>;
           "x" := ("x" - 1))
       end;
       ret "x"
    }>.

  Definition tgt5 : com :=
    <{ "x" := 100;
       while ("x")
       do ("a" :=@ "print" <["x" : aexp]>;
           "x" := ("x" - 1))
       end;
       ret "x"
    }>.

  Goal refines (Imp_Program_Ext src5) (Imp_Program_Ext tgt5).
  Proof.
    apply adequacy. unfold simulation, Imp_Program2, Imp_STS2, src5, tgt5, Imp_init. ss.
    do 4 step_src_silent.
    do 4 step_tgt_silent.
    inv H6.
    remember Reg.init as reg. clear Heqreg.
    remember 100 as n.
    assert (CASES : (n = 0 \/ 0 < n)%Z). by lia.
    clear Heqn.
    revert reg.

    induction n using (well_founded_ind (Zwf.Zwf_well_founded 0)).
    destruct CASES as [CEq | CGt].
    - rewrite CEq in H.
      do 2 step_tgt_silent.
      + do 2 step_src_silent.
        inv H7. inv H2.
        step_src_silent.
        step_tgt_silent.
        inv H6. inv H2.
        step_term.
      + rename H8 into TRUE.
        inv H7. inv H2.
        contradiction.
    - step_tgt_silent.
      + step_tgt_silent.
        do 2 step_src_silent.
        { inv H7. inv H2. lia. }
        { step_src_silent. step_tgt_silent.
          inv H6. inv H7. inv H2. inv H3.
          step_term. }
      + rename H8 into TRUE.
        econs 3; ss.
        exists (inr LInternal); eexists; split.
        { inv H7. inv H2. econs. eapply E_WhileTrue. repeat econs. apply TRUE. }
        { ss; split; auto. inv H7. inv H2.
          step_src_silent.
          step_tgt_silent.
          econs 2; ss.
          intros ev st_tgt1 STEP0; inv STEP0.
          - inv STEP. ss; split; auto.
            eexists. split.
            + repeat econs. apply H8.
            + do 3 step_src_silent.
              do 3 step_tgt_silent.
              inv H8. inv H7. inv H2. inv H4. inv H8. inv H9. inv H3. inv H2.
              apply H.
              { unfold Zwf. split.
                - lia.
                - ss. lia. }
              { ss. lia. }
          - solve_tgt_ub. }
      + exfalso. destruct (Z.eqb n 0) eqn:CASES.
        { eapply UNDEF. eapply E_WhileFalse. repeat econs. apply Z.eqb_eq; auto. }
        { eapply UNDEF. eapply E_WhileTrue. repeat econs. apply Z.eqb_neq; auto. }
        Unshelve. exact 1.
  Qed.

  (* DIV2. However, we can't prove the following refinement because it can diverge.
     Also note that even though src5 and tgt5 are the same programs (thus trivially refines each other), 
     our simulation relation is too weak to prove this.
   *)
  Definition src6 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := AAny)
       end;
       ret "x"
    }>.

  Definition tgt6 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := AAny)
       end;
       ret "x"
    }>.

  Goal refines (Imp_Program_Ext src6) (Imp_Program_Ext tgt6).
  Proof.
  (* We can't prove this right now. Try to prove using induction, and see where it fails. *)
  Abort.

End DIV.
