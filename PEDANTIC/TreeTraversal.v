(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * TreeTraversal.v
 * This file contains the proof of correctness of a tree traversal algorithm using
 * the PEDANTIC verification framework.
 *
 **********************************************************************************)

Require Import Omega.
Require Export SfLib.
Require Export SfLibExtras.
Require Export ImpHeap.
Require Export AbsState.
Require Export AbsExecute.
Require Export AbsStateInstance.
Require Export Simplify.
Require Export Eqdep.
Require Export StateImplication.
Require Export Classical.
Require Export Unfold.
Require Export Fold.
Require Export merge.
Require Export ProgramTactics.
Require Export ClosureHelper.
Require Export UpdateHelper.
Require Export MagicWandExistsHelper.
Require Export StateHypHelper.
Opaque basicEval.

(* **************************************************************************
 *
 * Here is the example from the paper.  We start with some definitions for
 * the variables in the program.
 *
 ***************************************************************************)

Notation "'P'" := (Id 0) (at level 1).
Notation "'RR'" := (Id 1) (at level 1).
Notation "'I'" := (Id 2) (at level 1).
Notation "'N'" := (Id 3) (at level 1).
Notation "'T'" := (Id 4) (at level 1).
Notation "'Tmp_l'" := (Id 5) (at level 1).
Notation "'Tmp_r'" := (Id 6) (at level 1).

(*
 * Here is the abstract state condition at the beginning of the program.
 * The \Sigma portion of the states that the variable RR points to a well
 * formed tree.  There are no predicates in the \Pi portion.
 *)
Definition precondition : absState :=
    (AbsExistsT (TREE(!!RR,v(0),#2,(#0::#1::nil)))).

(*
 * This assertion is a little tricky.  It is the invariant for the main
 * loop of our example. We still have the assertion that RR points to a
 * well formed tree.  We also have two additional data structures in the
 * heap.  Both are linked lists.  The first one is pointed to by the
 * variable I and the second one is pointed to by the variable P.
 *
 * The \Pi portion in the assertion below states that the variable T
 * is either nil or it points to a node inside the tree whose top is
 * stored in RR.
 * There is a second condition in \Pi which states that all of the
 * cells in the list headed by P, the F_p field points to a node in the
 * tree RR.  This is the condition that uses the quantifiers in the \Pi
 * portion.
 *)

Definition afterInitAssigns : absState :=
    (AbsExistsT (AbsExistsT (AbsExistsT
        (TREE(!!RR,v(0),#2,(#0 :: #1 :: nil)) **
         TREE(!!I,v(1),#2,(#0::nil)) **
         TREE(!!P,v(2),#2,(#0::nil)) **
         (AbsAll (TreeRecords(v(1)))
               ([nth(find(v(2),v(0)),#2) inTree v(1)])) **
         (AbsAll (TreeRecords(v(2)))
               ([nth(find(v(3),v(0)),#2) inTree v(1)])) **
         ([ (!!T)====#0 \\// (!!T) inTree v(0)]))))).

(*
 * Here are the first three lines of code from the example
 *)
Definition initCode : com :=
    I ::= A0;
    T ::= !RR;
    P ::= A0.

(*
 * ...and here is the proof that after these lines are executed, that
 * we indeed have the state described by "afterInitAssigns".  Actually,
 * the state afterInitAssigns is a generalization of the actual state.
 * Most of the proof involves simplifying the clauses after nil is filled
 * in for the variables I and P and after T is replaced with RR.
 *)
Theorem initialization : {{precondition}}initCode{{afterInitAssigns return nil with AbsNone}}.

Proof.
    (*unfold initCode. unfold afterInitAssigns. unfold precondition.

    eapply strengthenPost.
    pcrunch.

    Focus 2. intros. inversion H. Focus 2. intros. inversion H.

    intros.
    eapply stripUpdateVarHyp in H. Focus 2. compute. reflexivity.
    simplifyHyp H. propagateExistsHyp H.

    stateImplication. clear H.

    simpl. intros.

    reduceHyp. reduceHyp. reduceHyp. reduceHyp. reduceHyp. reduceHyp.
    reduceHyp.
    Transparent basicEval.
    simpl in H6.
    simpl in H8.
    simpl in H10.
    Opaque basicEval.
    inversion H6; subst; clear H6. inversion H8; subst; clear H8.
    inversion H10; subst; clear H10.
    reduceHyp. Focus 2. inversion H6; subst; clear H6. elim H8. reflexivity.
    reduceHyp. Focus 2. inversion H3; subst; clear H3. elim H4. reflexivity.
    reduceHyp. Focus 2. inversion H0; subst; clear H0. elim H1. reflexivity.

    reduceHypothesis. pcrunch. unfold env_p in *.

    erewrite composeEnvPropagate1 in HeqH1. Focus 2. apply H7. simpl in HeqH1.
    erewrite composeEnvPropagate1 in HeqH0. Focus 2. apply H9. simpl in HeqH0.
    erewrite composeEnvPropagate2 in HeqH0. Focus 2. apply H7. simpl in HeqH0.
    erewrite composeEnvPropagate1 in HeqH10. Focus 2. apply H11. simpl in HeqH10.
    erewrite composeEnvPropagate2 in HeqH10. Focus 2. apply H9. simpl in HeqH0.
    erewrite composeEnvPropagate2 in HeqH10. Focus 2. apply H7. simpl in HeqH10.
    erewrite composeEnvPropagate1 in HeqH0. Focus 2. apply H9. simpl in HeqH0.
    erewrite composeEnvPropagate2 in HeqH0. Focus 2. apply H7. simpl in HeqH0.
    subst. eapply ex_intro.
    instantiate (1 := (_::_::_::_::nil)).

    decomposeTheState.
        eapply RSEmpty. unfold empty_heap. simpl. reflexivity.
        simpl. rewrite HeqH10. eapply BStateTree. pcrunch. eapply TreeBase.
            omega. unfold empty_heap. simpl. reflexivity.
            eapply SNVCons. eapply SNVNil.
        simpl. rewrite HeqH1. eapply BStateTree. pcrunch. eapply TreeBase.
            omega. unfold empty_heap. simpl. reflexivity.
            eapply SNVCons. eapply SNVNil.
        eapply RSAll. simpl. reflexivity. Transparent basicEval. simpl. Opaque basicEval.
            reflexivity. intros. inversion H0.
        eapply RSAll. simpl. reflexivity. Transparent basicEval. simpl. Opaque basicEval.
            reflexivity. intros. inversion H0.
        Transparent basicEval. simpl. Opaque basicEval.

        remember (e T). destruct n. simpl. eapply BTStatePredicate.
        omega. unfold empty_heap. simpl. reflexivity.
            simpl. instantiate (1 := nth 0 b NoValue). erewrite rootIsMember.
            eapply BTStatePredicate. omega. unfold empty_heap. simpl. reflexivity.
            omega. rewrite HeqH0.
        erewrite composeEnvPropagate2 in H15. Focus 2. apply H11.
        erewrite composeEnvPropagate2 in H15. Focus 2. apply H9.
        erewrite composeEnvPropagate2 in H15. Focus 2. apply H7. simpl in H15.
        apply H15.*)
    admit.
Admitted.


(*
 * Now we define the abstract state that should exist after the while of
 * the main body of the program is executed.
 *
 * This is exactly the same as the state afterInitAssigns except that the
 * condition T=0 and I=0 have been added.
 *)
Definition afterWhile : absState :=
    (AbsExistsT (AbsExistsT (AbsExistsT
        (TREE(!!RR,v(0),#2,(#0::#1::nil)) **
         TREE(!!I,v(1),#2,(#0::nil)) **
         TREE(!!P,v(2),#2,(#0::nil)) **
         (AbsAll (TreeRecords(v(2)))
               ([nth(find(v(3),v(0)),#2) inTree v(1)])) **
         [(!!T)====#0])))).

Definition loopInv : absState :=
    (AbsExistsT (AbsExistsT (AbsExistsT
        (TREE(!!RR,v(0),#2,(#0::#1::nil)) **
         TREE(!!I,v(1),#2,(#0::nil)) **
         TREE(!!P,AbsQVar 2,#2,(#0::nil)) **
         (AbsAll (TreeRecords(v(1)))
               ([nth(find(v(2),v(0)),#2) inTree v(1)])) **
         (AbsAll (TreeRecords(v(2)))
               ([nth(find(v(3),v(0)),#2) inTree v(1)])) **
         ([(!!T)====#0 \\// (!!T) inTree v(0)]))))).
(*
 * Here is the code for the main loop of the program.
 *)
Definition loop : com :=
    WHILE ALnot (!T === A0) DO
        N ::= !P;
        NEW P,ANum(2);
        (CStore ((!P)+++(ANum 1)) (!T));
        (CStore ((!P)+++(ANum 0)) (!N));
        (CLoad Tmp_l ((!T)+++ANum(0)));
        (CLoad Tmp_r ((!T)+++ANum(1)));
        (CIf (ALand (!Tmp_l === A0) (!Tmp_r === A0))
            (CIf (!I === A0)
                 (T ::= A0)
                 ( (CLoad T ((!I)+++ANum(1)));
                   (CLoad Tmp_l ((!I)+++ANum(0)));
                   DELETE !I,ANum(2);
                   I ::= (!Tmp_l)))
        
            (CIf (!Tmp_l === A0)
                 (CLoad T ((!T)+++ANum(1)))
                 (CIf (!Tmp_r === A0)
                      (CLoad T ((!T)+++ANum(0)))
                      (N ::= !I;
                       NEW I,ANum(2);
                       (CStore ((!I)+++ANum(0)) (!N));
                       (CLoad Tmp_l ((!T)+++(ANum 1)));
                       (CStore ((!I)+++ANum(1)) (!Tmp_l));
                       (CLoad T ((!T)+++(ANum 0)))))))
    LOOP.

Opaque basicEval.



Theorem treeRef1 : forall s n,
(realizeState 
    (AbsExistsT
 (AbsExistsT
  (AbsExistsT
   (AbsUpdateVar (!! (P) ++++ # 1 |-> v( 2) **
     !! (P) |-> v( 1) **
     [!! (P) ==== v( 0)] **
     [# 0 <<<< !! (T)] **
     AbsExistsT
     (AbsExistsT
      (AbsExistsT
       (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
        TREE( !! (I), v( 1), # 2, # 0 :: nil) **
        TREE( v( 4), v( 2), # 2, # 0 :: nil) **
        AbsAll TreeRecords( v( 1)) ([nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
        AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
        [!! (T) inTree v( 0)])))) N v( 1))))) nil s) ->
    NatValue n = basicEval I (NatValue (env_p s P) :: NatValue 1 :: nil) ->
    heap_p s n <> None.
Proof.
    intros s n H H0. eapply stripUpdateVarHypp in H. vm_compute in H.
    simpl in H0. Transparent basicEval. unfold basicEval in H0.
    inversion H0; subst; clear H0.
     eapply stateAssertionThm in H. simpl in H.  crunch.
    destruct s. simpl. simpl in H14.
    assert (e P + 1 > 0 /\ h (e P + 1) = Some x3).
    eapply H14. reflexivity. reflexivity.
    inversion H1; subst; clear H1. erewrite H3. intro X. inversion X.
Qed.


Theorem treeRef2 : forall s n, (realizeState 
    (AbsUpdateLoc (AbsExistsT
  (AbsExistsT
   (AbsExistsT
    (AbsUpdateVar (!! (P) ++++ # 1 |-> v( 2) **
      !! (P) |-> v( 1) **
      [!! (P) ==== v( 0)] **
      [# 0 <<<< !! (T)] **
      AbsExistsT
      (AbsExistsT
       (AbsExistsT
        (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
         TREE( !! (I), v( 1), # 2, # 0 :: nil) **
         TREE( v( 4), v( 2), # 2, # 0 :: nil) **
         AbsAll TreeRecords( v( 1)) ([nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
         AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
         
         [!! (T) inTree v( 0)])))) N v( 1))))) !! (P) ++++ # 1 !! (T)) nil s) -> NatValue n = basicEval I 
    (NatValue (env_p s P) :: NatValue 0 :: nil) -> heap_p s n <> None.
Proof.
    intros s n H H0.
    eapply stripUpdateVarHypp in H. vm_compute in H.
    simplifyHyp H.
    eapply removeUpdateLocHyp in H. Focus 2. compute. reflexivity.
    simpl in H0. Transparent basicEval. unfold basicEval in H0.
    inversion H0; subst; clear H0.
    eapply stateAssertionThm in H. simpl in H.  crunch.
    assert (forall x, x+0=x).
    intros. induction x9. simpl. reflexivity. simpl. rewrite IHx9. reflexivity.
    rewrite H0.
    destruct s. simpl.
    simpl in H9.
    assert ((e P) > 0 /\ h (e P) = Some (e N)).
    apply H9. reflexivity. reflexivity.
    inversion H1; subst; clear H1. erewrite H7. 
    intro X. inversion X.
Qed.


Theorem deleteExists1 : forall x, (realizeState 
    (AbsUpdateWithLoc (AbsUpdateWithLoc ([~~ !! (I) ==== # 0] **
   [!! (Tmp_l) ==== # 0 //\\ !! (Tmp_r) ==== # 0] **
   AbsUpdateWithLoc (AbsUpdateWithLoc (AbsUpdateLoc (AbsUpdateLoc (AbsExistsT
       (AbsExistsT
        (AbsExistsT
         (AbsUpdateVar (!! (P) ++++ # 1 |-> v( 2) **
           !! (P) |-> v( 1) **
           [!! (P) ==== v( 0)] **
           [# 0 <<<< !! (T)] **
           AbsExistsT
           (AbsExistsT
            (AbsExistsT
             (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
              TREE( !! (I), v( 1), # 2, # 0 :: nil) **
              TREE( v( 4), v( 2), # 2, # 0 :: nil) **
              AbsAll TreeRecords( v( 1)) ([ nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
              AbsAll TreeRecords( v( 2)) ([ nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
              [!! (T) inTree v( 0)])))) N v( 1))))) !! (P) ++++ # 1 !! (T)) !! (P) !! 
         (N)) Tmp_l !! (T) ++++ # 0) Tmp_r !! (T) ++++ # 1) T !! (I) ++++ # 1) Tmp_l !! 
     (I) ++++ # 0) nil x) -> exists s, (realizeState 
    (AbsMagicWand (AbsUpdateWithLoc (AbsUpdateWithLoc ([~~ !! (I) ==== # 0] **
    [!! (Tmp_l) ==== # 0 //\\ !! (Tmp_r) ==== # 0] **
    AbsUpdateWithLoc (AbsUpdateWithLoc (AbsUpdateLoc (AbsUpdateLoc (AbsExistsT
        (AbsExistsT
         (AbsExistsT
          (AbsUpdateVar (!! (P) ++++ # 1 |-> v( 2) **
            !! (P) |-> v( 1) **
            [!! (P) ==== v( 0)] **
            [# 0 <<<< !! (T)] **
            AbsExistsT
            (AbsExistsT
             (AbsExistsT
              (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
               TREE( !! (I), v( 1), # 2, # 0 :: nil) **
               TREE( v( 4), v( 2), # 2, # 0 :: nil) **
               AbsAll TreeRecords( v( 1)) ([ nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
               AbsAll TreeRecords( v( 2)) ([ nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
               [!! (T) inTree v( 0)])))) N v( 1))))) !! (P) ++++ # 1 !! (T)) !! 
          (P) !! (N)) Tmp_l !! (T) ++++ # 0) Tmp_r !! (T) ++++ # 1) T !! (I) ++++ # 1) Tmp_l !! 
      (I) ++++ # 0) (AbsExistsT
  (AbsExistsT
   (AbsExistsT
    (v( 0) ++++ # 1 |-> v( 2) **
     v( 0) ++++ # 0 |-> v( 1) **
     [!! (I) ==== v( 0)]))))) nil s).
Proof.
    intros x H0.
    Set Printing Depth 200.
    propagateExistsHyp H0. propagateExistsHyp H0.
    simplifyHyp H0. eapply stripUpdateVarHypp in H0. vm_compute in H0.
    simplifyHyp H0.
    simplifyHyp H0. propagateExistsHyp H0.
    propagateExistsHyp H0. propagateExistsHyp H0.
    eapply stripUpdateWithLocHypp in H0. compute in H0.
    eapply unfold_rs2 in H0. Focus 2. unfoldHeap (!!I).
    simplifyHyp H0. simplifyHyp H0. simplifyHyp H0.
    eapply removeUpdateLocHyp in H0. Focus 2. compute. reflexivity.
    eapply removeUpdateLocHyp in H0. Focus 2. compute. reflexivity.
    eapply stripUpdateWithLocHypp in H0. compute in H0.
    eapply stripUpdateWithLocHypp in H0. compute in H0.
    simplifyHyp H0.
    propagateExistsHyp H0.
    eapply existsRealizeState.
    intros.
    propagateExists. propagateExists. simplify. simplify.  
    eapply stripUpdateVarp. compute. eapply stripUpdateVarp. compute.
    simplify. simplify. propagateExists.
    eapply stripUpdateWithLocp. compute.
    eapply unfold_rs1. unfoldHeap (!!I).
    simplify.
    simplify. simplify. simplify. propagateExists. simplify.
    eapply removeUpdateLocThm. compute. reflexivity.
    eapply removeUpdateLocThm. compute. reflexivity.
    eapply stripUpdateWithLocp. compute.
    eapply stripUpdateWithLocp. compute.
    simplify. propagateExists.
    apply H.
    eapply magicWandStateExists.
    compute. reflexivity.
    eapply ex_intro. apply H0.
    compute. reflexivity.
    compute. reflexivity.
    compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsId. reflexivity.
    compute. reflexivity.
    intros.
    compute in H.
    eapply stateAssertionThm in H. simpl in H.  crunch.

    destruct s. simpl in H. simpl. remember (e I).
    destruct n. inversion H. exists n. reflexivity.

    Grab Existential Variables.
    apply x.
Qed.

Opaque mergeStates.

Theorem mergeTheorem1:
mergeStates 
    (AbsUpdateVar ([!! (I) ==== # 0] **
  [!! (Tmp_l) ==== # 0 //\\ !! (Tmp_r) ==== # 0] **
  AbsUpdateWithLoc (AbsUpdateWithLoc (AbsUpdateLoc (AbsUpdateLoc (AbsExistsT
      (AbsExistsT
       (AbsExistsT
        (AbsUpdateVar (!! (P) ++++ # 1 |-> v( 2) **
          !! (P) |-> v( 1) **
          [!! (P) ==== v( 0)] **
          [# 0 <<<< !! (T)] **
          AbsExistsT
          (AbsExistsT
           (AbsExistsT
            (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
             TREE( !! (I), v( 1), # 2, # 0 :: nil) **
             TREE( v( 4), v( 2), # 2, # 0 :: nil) **
             AbsAll TreeRecords( v( 1)) ([nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
             AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
             
             [!! (T) inTree v( 0)])))) N v( 1))))) !! (P) ++++ # 1 !! (T)) !! (P) !! 
        (N)) Tmp_l !! (T) ++++ # 0) Tmp_r !! (T) ++++ # 1) T # 0)

     (AbsUpdateVar 
     (AbsMagicWand (AbsUpdateWithLoc (AbsUpdateWithLoc ([~~ !! (I) ==== # 0] **
     [!! (Tmp_l) ==== # 0 //\\ !! (Tmp_r) ==== # 0] **
     AbsUpdateWithLoc (AbsUpdateWithLoc (AbsUpdateLoc (AbsUpdateLoc (AbsExistsT
         (AbsExistsT
          (AbsExistsT
           (AbsUpdateVar (!! (P) ++++ # 1 |-> v( 2) **
             !! (P) |-> v( 1) **
             [!! (P) ==== v( 0)] **
             [# 0 <<<< !! (T)] **
             AbsExistsT
             (AbsExistsT
              (AbsExistsT
               (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
                TREE( !! (I), v( 1), # 2, # 0 :: nil) **
                TREE( v( 4), v( 2), # 2, # 0 :: nil) **
                AbsAll TreeRecords( v( 1)) ([ nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
                AbsAll TreeRecords( v( 2)) ([ nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
                [!! (T) inTree v( 0)])))) N v( 1))))) !! (P) ++++ # 1 !! (T)) !! 
           (P) !! (N)) Tmp_l !! (T) ++++ # 0) Tmp_r !! (T) ++++ # 1) T !! (I) ++++ # 1) Tmp_l !!(I) ++++ # 0) (AbsExistsT
   (AbsExistsT
    (AbsExistsT
     (v( 0) ++++ # 1 |-> v( 2) **
      v( 0) ++++ # 0 |-> v( 1) **
      [!! (I) ==== v( 0)]))))) I !! (Tmp_l))

    (AbsExistsT (AbsExistsT (AbsExistsT
        (TREE(!!RR,v(0),#2,(#0::#1::nil)) **
         TREE(!!I,v(1),#2,(#0::nil)) **
         TREE(!!P,AbsQVar 2,#2,(#0::nil)) **
         (AbsAll (TreeRecords(v(1)))
               ([nth(find(v(2),v(0)),#2) inTree v(1)])) **
         (AbsAll (TreeRecords(v(2)))
               ([nth(find(v(3),v(0)),#2) inTree v(1)])) **
         ([(!!T)====#0 \\// (!!T) inTree v(0)]))))).
Proof.
    Set Printing Depth 200.
    eapply stripUpdateVarLeft. compute. reflexivity.
    eapply stripUpdateVarRight. compute. reflexivity.
    mergePropagateExistsLeft. mergePropagateExistsRight.
    eapply removeUpdateLocLeft. compute. reflexivity.
    eapply removeUpdateLocLeft. compute. reflexivity.
    eapply removeUpdateLocRight. compute. reflexivity.
    eapply removeUpdateLocRight. compute. reflexivity.
    mergeSimplifyLeft. mergeSimplifyRight. 
    eapply unfold_merge2. unfoldHeap (v(5)).
    mergeSimplifyRight.
    eapply stripUpdateWithLocRight. compute. reflexivity.
    mergeSimplifyRight. mergePropagateExistsRight.
    eapply stripUpdateWithLocRight. compute. reflexivity.
    eapply mergeStripVarInsideRight. instantiate (1 := Tmp_l). compute. reflexivity.
    eapply stripUpdateWithLocRight. compute. reflexivity.
    mergeSimplifyRight. mergePropagateExistsRight.
    eapply localizeExistsRightp. compute.
    eapply localizeExistsRightp. compute.
    eapply localizeExistsRightp. compute.
    eapply removeMagicWandRight. compute. reflexivity.
    mergeSimplifyRight. mergeSimplifyRight.
    eapply mergeStripVarRight. instantiate (1 := Tmp_r). compute. reflexivity.
    eapply mergeStripVarLeft. instantiate (1 := Tmp_l). compute. reflexivity.
    eapply mergeStripVarLeft. instantiate (1 := Tmp_r). compute. reflexivity.
    eapply normalizeRight. instantiate (1 := (I)). compute.
    mergeSimplifyRight. mergePropagateExistsRight.
    eapply normalizeRight. instantiate (1 := (I)). compute.

    eapply mergeImplies.

    startMerge.

    doMergeStates.

    eapply DMOrPredicates2. compute.
    eapply PESComposeRight. eapply PESComposeRight. eapply PESComposeRight.
    eapply PESComposeLeft. eapply PESComposeRight. eapply PESComposeLeft. eapply PESR.
    eapply PESComposeLeft. eapply PESComposeLeft. eapply PESComposeRight.
    eapply PESComposeLeft. eapply PESComposeRight. eapply PESComposeRight.
    eapply PESComposeRight. eapply PESComposeRight. eapply PESComposeRight.
    eapply PESComposeRight. eapply PESComposeLeft. eapply PESComposeLeft.
    eapply PESR. compute. reflexivity.
    finishMerge. 

    intros.
    eapply foldHeapTheorem in H. Focus 2. foldHeap (!!P) (0::nil) 2.
    eapply foldAllTheorem in H. Focus 2. foldAll 2.
    simplifyHyp H. simplifyHyp H. simplify.
    eapply stateImplication. apply H. compute. reflexivity. compute. reflexivity.
    prove_implication. compute. reflexivity. compute. reflexivity. simpl.
    intros. eapply ex_intro.
    eapply emptyRealizeState. simpl. reflexivity.

    intros. compute in H.
    eapply stateAssertionThm in H. simpl in H.  crunch.
    remember (nth 5 bindings NoValue). destruct y.
    destruct n. inversion H. exists n. reflexivity. inversion H. inversion H. inversion H.

    Grab Existential Variables.
    apply nil. apply nil.
Qed.

    (*eapply FoldAll. compute. reflexivity. compute. reflexivity. solveSPickElement.
    solveSPickElement. instantiate (3 := (2)). solveSPickElement. stripFields.
    compute. reflexivity. compute. reflexivity. solveSPickElement. compute. reflexivity.*)
 (*foldAll 0.
    eapply FoldAll.
 foldAll 1.*)
    (*eapply FoldHeap. instantiate (2 := ((#0)::nil)). stripFields. 
    compute. reflexivity. (instantiate (2 := (!!P))).
        instantiate (2 := 2). pickNCells. pickNHeaps. compute. reflexivity. eapply PNCInductive. solveSPickElement.
        eapply PNCInductive0. solveSPickElement. eapply PNCBase. pickNHeaps.
        eapply SFCons. eapply SFNil. simpl. reflexivity.
        Focus 2. simpl. reflexivity.
        Focus 5. simpl.*)

    (*eapply normalizeHyp in H. instantiate (1 := P).*)

Theorem storeCheck1 : forall s n, realizeState 
    (AbsExistsT
 (AbsExistsT
  (AbsExistsT
   (AbsExistsT
    (v( 0) ++++ # 1 |-> v( 2) **
     v( 0) ++++ # 0 |-> v( 1) **
     [!! (I) ==== v( 0)] **
     AbsUpdateVar ([~~ !! (Tmp_r) ==== # 0] **
      [~~ !! (Tmp_l) ==== # 0] **
      [~~ (!! (Tmp_l) ==== # 0 //\\ !! (Tmp_r) ==== # 0)] **
      AbsUpdateWithLoc (AbsUpdateWithLoc (AbsUpdateLoc (AbsUpdateLoc (AbsExistsT
          (AbsExistsT
           (AbsExistsT
            (AbsUpdateVar (!! (P) ++++ # 1 |-> v( 2) **
              !! (P) |-> v( 1) **
              [!! (P) ==== v( 0)] **
              [# 0 <<<< !! (T)] **
              AbsExistsT
              (AbsExistsT
               (AbsExistsT
                (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
                 TREE( v( 7), v( 1), # 2, # 0 :: nil) **
                 TREE( v( 4), v( 2), # 2, # 0 :: nil) **
                 AbsAll TreeRecords( v( 1)) ([ nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
                 AbsAll TreeRecords( v( 2)) ([ nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
                 [!! (T) inTree v( 0)])))) N v( 1))))) !! (P) ++++ # 1 !! (T)) !! 
            (P) !! (N)) Tmp_l !! (T) ++++ # 0) Tmp_r !! (T) ++++ # 1) N v( 1)))))) nil s -> NatValue n = basicEval I 
    (NatValue (env_p s I) :: NatValue 0 :: nil) -> heap_p s n <> None.
Proof.
    Set Printing Depth 1000.
    intros s n H H0.
    eapply stripUpdateVarHyp in H. Focus 2. compute. reflexivity.
    simplifyHyp H.
    eapply stateAssertionThm in H. simpl in H.  crunch.

    destruct s. Transparent basicEval. simpl. simpl in H9. simpl in H0.

    assert (forall x, x + 0=x).
    induction x5. simpl. reflexivity. simpl. rewrite IHx5. reflexivity.
    assert ((e I) > 0 /\ h (e I) = Some (e N)).
    eapply H9. reflexivity. reflexivity. inversion H3; subst; clear H3. rewrite H2 in H0.
    inversion H0; subst; clear H0.

    remember (e I). rewrite H7.
    intro X. inversion X.
Qed.

Set Printing Depth 1000.

Theorem storeCheck2 : forall s n,
 (realizeState 
    (AbsUpdateWithLoc (AbsUpdateLoc (AbsExistsT
   (AbsExistsT
    (AbsExistsT
     (AbsExistsT
      (v( 0) ++++ # 1 |-> v( 2) **
       v( 0) ++++ # 0 |-> v( 1) **
       [!! (I) ==== v( 0)] **
       AbsUpdateVar ([~~ !! (Tmp_r) ==== # 0] **
        [~~ !! (Tmp_l) ==== # 0] **
        [~~ (!! (Tmp_l) ==== # 0 //\\ !! (Tmp_r) ==== # 0)] **
        AbsUpdateWithLoc (AbsUpdateWithLoc (AbsUpdateLoc (AbsUpdateLoc (AbsExistsT
            (AbsExistsT
             (AbsExistsT
              (AbsUpdateVar (!! (P) ++++ # 1 |-> v( 2) **
                !! (P) |-> v( 1) **
                [!! (P) ==== v( 0)] **
                [# 0 <<<< !! (T)] **
                AbsExistsT
                (AbsExistsT
                 (AbsExistsT
                  (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
                   TREE( v( 7), v( 1), # 2, # 0 :: nil) **
                   TREE( v( 4), v( 2), # 2, # 0 :: nil) **
                   AbsAll TreeRecords( v( 1)) ([ nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
                   AbsAll TreeRecords( v( 2)) ([ nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
                   [!! (T) inTree v( 0)])))) N v( 1))))) !! (P) ++++ # 1 !! (T)) !! 
              (P) !! (N)) Tmp_l !! (T) ++++ # 0) Tmp_r !! (T) ++++ # 1) N v( 1)))))) !! 
      (I) ++++ # 0 !! (N)) Tmp_l !! (T) ++++ # 1) nil s
) ->
     (NatValue n = basicEval I (NatValue 
         (env_p s I) :: NatValue 1 :: nil)) ->
     heap_p s n <> None.
Proof.
    Set Printing Depth 1000.
    intros s n H H0.

    eapply stripUpdateVarHyp in H. Focus 2. compute. reflexivity.
    simplifyHyp H.
    simplifyHyp H. propagateExistsHyp H. propagateExistsHyp H.
    propagateExistsHyp H. propagateExistsHyp H. propagateExistsHyp H.
    propagateExistsHyp H.
    eapply removeUpdateLocHyp in H. Focus 2. simpl. reflexivity.
    eapply stripUpdateWithLocHypp in H. compute in H.
    eapply stateAssertionThm in H. simpl in H.  crunch.

    destruct s. Transparent basicEval. simpl.  simpl in H0. simpl in H19.

    assert ((e I) + 1 > 0 /\ h ((e I)+1) = Some x6).
    eapply H19. unfold override. simpl. reflexivity. reflexivity. inversion H; subst; clear H. inversion H0; subst; clear H0.

    rewrite H3. intro X. inversion X.
Qed.

Theorem mergeTheorem2:
mergeStates 
    (AbsUpdateWithLoc ([!! (Tmp_r) ==== # 0] **
  [~~ !! (Tmp_l) ==== # 0] **
  [~~ (!! (Tmp_l) ==== # 0 //\\ !! (Tmp_r) ==== # 0)] **
  AbsUpdateWithLoc (AbsUpdateWithLoc (AbsUpdateLoc (AbsUpdateLoc (AbsExistsT
      (AbsExistsT
       (AbsExistsT
        (AbsUpdateVar (!! (P) ++++ # 1 |-> v( 2) **
          !! (P) |-> v( 1) **
          [!! (P) ==== v( 0)] **
          [# 0 <<<< !! (T)] **
          AbsExistsT
          (AbsExistsT
           (AbsExistsT
            (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
             TREE( !! (I), v( 1), # 2, # 0 :: nil) **
             TREE( v( 4), v( 2), # 2, # 0 :: nil) **
             AbsAll TreeRecords( v( 1)) ([nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
             AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
             
             [!! (T) inTree v( 0)])))) N v( 1))))) !! (P) ++++ # 1 !! (T)) !! (P) !! 
        (N)) Tmp_l !! (T) ++++ # 0) Tmp_r !! (T) ++++ # 1) T !! (T) ++++ # 0) (AbsUpdateWithLoc 
     (AbsUpdateLoc (AbsUpdateWithLoc (AbsUpdateLoc (AbsExistsT
     (AbsExistsT
      (AbsExistsT
       (AbsExistsT
        (v( 0) ++++ # 1 |-> v( 2) **
         v( 0) ++++ # 0 |-> v( 1) **
         [!! (I) ==== v( 0)] **
         AbsUpdateVar ([~~ !! (Tmp_r) ==== # 0] **
          [~~ !! (Tmp_l) ==== # 0] **
          [~~ (!! (Tmp_l) ==== # 0 //\\ !! (Tmp_r) ==== # 0)] **
          AbsUpdateWithLoc (AbsUpdateWithLoc (AbsUpdateLoc (AbsUpdateLoc (AbsExistsT
              (AbsExistsT
               (AbsExistsT
                (AbsUpdateVar (!! (P) ++++ # 1 |-> v( 2) **
                  !! (P) |-> v( 1) **
                  [!! (P) ==== v( 0)] **
                  [# 0 <<<< !! (T)] **
                  AbsExistsT
                  (AbsExistsT
                   (AbsExistsT
                    (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
                     TREE( v( 7), v( 1), # 2, # 0 :: nil) **
                     TREE( v( 4), v( 2), # 2, # 0 :: nil) **
                     AbsAll TreeRecords( v( 1)) ([ nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
                     AbsAll TreeRecords( v( 2)) ([ nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
                     [!! (T) inTree v( 0)])))) N v( 1))))) !! (P) ++++ # 1 !! (T)) !! 
                (P) !! (N)) Tmp_l !! (T) ++++ # 0) Tmp_r !! (T) ++++ # 1) N v( 1)))))) !! 
        (I) ++++ # 0 !! (N)) Tmp_l !! (T) ++++ # 1) !! (I) ++++ # 1 !! (Tmp_l)) T !! 
     (T) ++++ # 0)

    (AbsExistsT (AbsExistsT (AbsExistsT
        (TREE(!!RR,v(0),#2,(#0::#1::nil)) **
         TREE(!!I,v(1),#2,(#0::nil)) **
         TREE(!!P,AbsQVar 2,#2,(#0::nil)) **
         (AbsAll (TreeRecords(v(1)))
               ([nth(find(v(2),v(0)),#2) inTree v(1)])) **
         (AbsAll (TreeRecords(v(2)))
               ([nth(find(v(3),v(0)),#2) inTree v(1)])) **
         ( [(!!T) inTree v(0) \\// (!!T)====#0]))))).
Proof.
    eapply mergeImplies.
    mergeSimplifyLeft. mergeSimplifyRight.
    eapply stripUpdateVarLeft. compute. reflexivity.
    eapply stripUpdateVarRight. compute. reflexivity.
    mergePropagateExistsLeft. mergePropagateExistsRight.
    eapply removeUpdateLocLeft. compute. reflexivity.
    eapply removeUpdateLocLeft. compute. reflexivity.
    eapply removeUpdateLocRight. compute. reflexivity.
    eapply removeUpdateLocRight. compute. reflexivity.
    eapply removeUpdateLocRight. compute. reflexivity.
    eapply promoteConstraintsRight. compute.
    eapply stripUpdateWithLocRight. compute. reflexivity.
    eapply mergeStripVarRight. instantiate (1 := Tmp_r). compute. reflexivity.
    eapply mergeStripVarLeft. instantiate (1 := Tmp_l). compute. reflexivity.
    eapply mergeStripVarLeft. instantiate (1 := Tmp_r). compute. reflexivity.
    mergeSimplifyRight.
    eapply mergeStripVarInsideRight. instantiate (1 := Tmp_l). compute. reflexivity.
    eapply removeUpdateWithLocTraverseRight. compute.
    eapply removeUpdateLocRight.  compute. reflexivity.
    mergeSimplifyRight. mergeSimplifyRight.
    eapply stripUpdateVarRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply removeUpdateWithLocTraverseRight2. compute.
    mergeSimplifyRight.
    mergeSimplifyRight.
    mergePropagateExistsRight.
    eapply foldRight. foldHeap (!!P) (0::nil) 2.
    eapply foldAllRight. foldAll 2.
    eapply foldRight. foldHeap (!!I) (0::nil) 2.
    eapply foldAllRight. foldAll 2.
    mergeSimplifyRight.
    mergeSimplifyRight.
    eapply removeUpdateWithLocTraverseLeft2. compute.
    mergeSimplifyLeft.
    mergePropagateExistsLeft.
    eapply foldLeft. foldHeap (!!P) (0::nil) 2.
    eapply foldAllLeft. foldAll 2.
    mergeSimplifyLeft.
    mergePropagateExistsLeft.

    eapply reverseOrLeft. compute.
    eapply reverseOrRight. compute.

    startMerge.

    doMergeStates.

    finishMerge. compute. 

    intros.
    eapply stateImplication. apply H. compute. reflexivity. compute. reflexivity.
    prove_implication. compute. reflexivity. compute. reflexivity. simpl.
    intros. eapply ex_intro.
    eapply emptyRealizeState. compute. reflexivity.

    Grab Existential Variables.
    apply nil. apply nil.
Qed.

Theorem mergeTheorem3:
mergeStates 
    (AbsUpdateWithLoc ([!! (Tmp_l) ==== # 0] **
  [~~ (!! (Tmp_l) ==== # 0 //\\ !! (Tmp_r) ==== # 0)] **
  AbsUpdateWithLoc (AbsUpdateWithLoc (AbsUpdateLoc (AbsUpdateLoc (AbsExistsT
      (AbsExistsT
       (AbsExistsT
        (AbsUpdateVar (!! (P) ++++ # 1 |-> v( 2) **
          !! (P) |-> v( 1) **
          [!! (P) ==== v( 0)] **
          [# 0 <<<< !! (T)] **
          AbsExistsT
          (AbsExistsT
           (AbsExistsT
            (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
             TREE( !! (I), v( 1), # 2, # 0 :: nil) **
             TREE( v( 4), v( 2), # 2, # 0 :: nil) **
             AbsAll TreeRecords( v( 1)) ([nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
             AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
             
             [!! (T) inTree v( 0)])))) N v( 1))))) !! (P) ++++ # 1 !! (T)) !! (P) !! 
        (N)) Tmp_l !! (T) ++++ # 0) Tmp_r !! (T) ++++ # 1) T !! (T) ++++ # 1) (AbsExistsT
 (AbsExistsT
  (AbsExistsT
   (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
    TREE( !! (I), v( 1), # 2, # 0 :: nil) **
    TREE( !! (P), v( 2), # 2, # 0 :: nil) **
    AbsAll TreeRecords( v( 1)) ([nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
    AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
    [!! (T) inTree v( 0) \\// !! (T) ==== # 0]))))
 (AbsExistsT
  (AbsExistsT
  (AbsExistsT
   (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
    TREE( !! (I), v( 1), # 2, # 0 :: nil) **
    TREE( !! (P), v( 2), # 2, # 0 :: nil) **
    AbsAll TreeRecords( v( 1)) ([nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
    AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
    [!! (T) inTree v( 0) \\// !! (T) ==== # 0])))).
Proof.
    eapply mergeImplies.

    mergeSimplifyLeft.
    eapply stripUpdateVarLeft. compute. reflexivity.
    mergePropagateExistsLeft.
    eapply removeUpdateLocLeft. compute. reflexivity.
    eapply removeUpdateLocLeft. compute. reflexivity.
    eapply mergeStripVarLeft. instantiate (1 := Tmp_l). compute. reflexivity.
    eapply mergeStripVarLeft. instantiate (1 := Tmp_r). compute. reflexivity.
    eapply removeUpdateWithLocTraverseLeft2. compute.
    mergeSimplifyLeft.
    mergePropagateExistsLeft.
    eapply foldLeft. foldHeap (!!P) (0::nil) 2.
    eapply foldAllLeft. foldAll 2.
    mergeSimplifyLeft.
    mergePropagateExistsLeft.

    eapply reverseOrLeft. compute.
    eapply reverseOrRight. compute.

    startMerge.

    doMergeStates.

    finishMerge. compute. 

    intros.
    eapply stateImplication. apply H. compute. reflexivity. compute. reflexivity.
    prove_implication. compute. reflexivity. compute. reflexivity. simpl.
    intros. eapply ex_intro.
    eapply emptyRealizeState. compute. reflexivity.

    Grab Existential Variables. apply nil. apply nil.
Qed.

Theorem mergeTheorem4:
mergeStates 
    (AbsExistsT
 (AbsExistsT
  (AbsExistsT
   (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
    TREE( !! (I), v( 1), # 2, # 0 :: nil) **
    TREE( !! (P), v( 2), # 2, # 0 :: nil) **
    AbsAll TreeRecords( v( 1)) ([nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
    AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
    [!! (T) ==== # 0 \\// !! (T) inTree v( 0)])))) (AbsExistsT
 (AbsExistsT
  (AbsExistsT
   (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
    TREE( !! (I), v( 1), # 2, # 0 :: nil) **
    TREE( !! (P), v( 2), # 2, # 0 :: nil) **
    AbsAll TreeRecords( v( 1)) ([nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
    AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
    [!! (T) inTree v( 0) \\// !! (T) ==== # 0]))))
 (AbsExistsT
 (AbsExistsT
  (AbsExistsT
   (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
    TREE( !! (I), v( 1), # 2, # 0 :: nil) **
    TREE( !! (P), v( 2), # 2, # 0 :: nil) **
    AbsAll TreeRecords( v( 1)) ([nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
    AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
    [!! (T) inTree v( 0) \\// !! (T) ==== # 0])))).
Proof.
    eapply mergeImplies.

    startMerge.
    doMergeStates.
    eapply DMImplyPredicates1. compute.
    eapply PESComposeRight. eapply PESComposeRight. eapply PESComposeRight.
    eapply PESComposeRight. eapply PESComposeRight. eapply PESR.
    compute. reflexivity.

    intros.
    simplify.
    eapply stateAssertionThm in H0. simpl in H0.  crunch.
    inversion H5; subst; clear H5.

    eapply RSOrComposeR. eapply RSR. compute. Transparent basicEval.
    simpl. rewrite H0. simpl. reflexivity. eapply BTStatePredicate.
    intro X. inversion X.
    compute. reflexivity.
    eapply RSOrComposeL. eapply RSR. simpl.
    rewrite H0. simpl. reflexivity. eapply BTStatePredicate.
    intro X. inversion X.
    compute. reflexivity.

    finishMerge.

    intros.
    eapply stateImplication. apply H. compute. reflexivity. compute. reflexivity.
    prove_implication. compute. reflexivity. compute. reflexivity. simpl.
    intros. eapply ex_intro.
    eapply emptyRealizeState. compute. reflexivity.
    Grab Existential Variables. apply nil. apply nil.
Qed.

Theorem implication1:
forall s : state, realizeState 
    (AbsExistsT
 (AbsExistsT
  (AbsExistsT
   (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
    TREE( !! (I), v( 1), # 2, # 0 :: nil) **
    TREE( !! (P), v( 2), # 2, # 0 :: nil) **
    AbsAll TreeRecords( v( 1)) ([nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
    AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
    [!! (T) inTree v( 0) \\// !! (T) ==== # 0])))) nil s -> realizeState (AbsExistsT
 (AbsExistsT
  (AbsExistsT
   (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
    TREE( !! (I), v( 1), # 2, # 0 :: nil) **
    TREE( !! (P), v( 2), # 2, # 0 :: nil) **
    AbsAll TreeRecords( v( 1)) ([nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
    AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
    [!! (T) ==== # 0 \\// !! (T) inTree v( 0)])))) nil s.
Proof.
    intros.
    eapply stateImplication. apply H. compute. reflexivity. compute. reflexivity.
    prove_implication. compute. reflexivity. compute. reflexivity. simpl.
    intros. eapply ex_intro. simplify.
    eapply stateAssertionThm in H1. simpl in H1.  crunch.
    inversion H6; subst; clear H6.

    eapply RSOrComposeR. eapply RSR. Transparent basicEval.
    simpl. rewrite H7. simpl. reflexivity. eapply BTStatePredicate.
    intro X. inversion X.
    compute. reflexivity.
    eapply RSOrComposeL. eapply RSR. simpl.
    rewrite H7. simpl. reflexivity. eapply BTStatePredicate.
    intro X. inversion X.
    compute. reflexivity.
Qed.

Theorem implication2:
forall x : state, realizeState 
    (AbsExistsT
 (AbsExistsT
  (AbsExistsT
   (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
    TREE( !! (I), v( 1), # 2, # 0 :: nil) **
    TREE( !! (P), v( 2), # 2, # 0 :: nil) **
    AbsAll TreeRecords( v( 1)) ([nth( find( v( 2), v( 0)), # 2) inTree v( 1)]) **
    AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
    [!! (T) ==== # 0 \\// !! (T) inTree v( 0)])))) nil x -> realizeState loopInv nil x.
Proof.
    unfold loopInv.
    eapply mergeSame.
Qed.

Theorem implication3:
forall s : state, realizeState 
    ([~~ (convertToAbsExp (ALnot (! T === A0)))] **
 loopInv) nil s -> realizeState (AbsExistsT
 (AbsExistsT
  (AbsExistsT
   (TREE( !! (RR), v( 0), # 2, # 0 :: # 1 :: nil) **
    TREE( !! (I), v( 1), # 2, # 0 :: nil) **
    TREE( !! (P), v( 2), # 2, # 0 :: nil) **
    AbsAll TreeRecords( v( 2)) ([nth( find( v( 3), v( 0)), # 2) inTree v( 1)]) **
    [!! (T) ==== # 0])))) nil s.
Proof.
    unfold loopInv. simpl. intros.
    simplifyHyp H. propagateExistsHyp H. propagateExistsHyp H. propagateExistsHyp H.
    eapply stateImplication. apply H. compute. reflexivity. compute. reflexivity.
    prove_implication. compute. reflexivity. compute. reflexivity. simpl.
    intros. eapply ex_intro. eapply emptyRealizeState. compute. reflexivity.
    Grab Existential Variables. apply nil.
Qed.

Theorem loopInvariant :
    {{afterInitAssigns}}loop{{afterWhile return nil with AbsNone}}.
Proof.
    (* Break up the while portion of the loop *)
    unfold loop. unfold afterWhile. unfold afterInitAssigns.

    (* WHILE ALnot (!T === A0) DO *)
    eapply strengthenPost.
    eapply whileThm with (invariant := loopInv). unfold loopInv.
    eapply strengthenPost. simpl.

    (* N ::= !P; *)
    eapply compose. pcrunch.

    (* NEW P,ANum(Size_l);*)
    eapply compose. pcrunch.

    simp. simp. simp.

    (*assert (simplifyState (nil : list (Context))
    ((v(0) ++++ #0 |-> v(1) **
     [!!(P) ==== v(0)]):absState)=AbsEmpty). simpl.

    assert (buildStateContext ([!!(P)====v(0)]:absState)=buildStateContext (AbsEmpty)).
    simpl.*)

    (* CStore ((!P)+++(ANum F_p)) (!T)) *)
    eapply compose. eapply store. compute. reflexivity. compute. reflexivity.
    intros. eapply treeRef1. apply H. apply H0.


    (* CStore ((!P)+++(ANum F_n)) (!N)) *)
    eapply compose.  eapply store. compute. reflexivity. compute. reflexivity.
    eapply treeRef2. (*apply H. apply H0.*)

    simp.

    (* CLoad Tmp_l ((!T)+++ANum(F_l)) *)
    eapply compose. pcrunch.

    (* CLoad Tmp_r ((!T) +++ A1) *)
    eapply compose. pcrunch.

    (* IF (ALand (!Tmp_l === A0) (!Tmp_r === A0)) *)
    eapply if_statement. simpl.

        (* IF (!I === A0) *)
        eapply if_statement. simpl.

            (* T ::= A0 *)
            pcrunch.

        (* ELSE *)

            (* CLoad T (!I)++A1 *)
            eapply compose. pcrunch.

            (* CLoad Tmp_l (!I)++A0 *)
            eapply compose. pcrunch.

            (* DELETE !I, A2 *)
            eapply compose.
            Set Printing Depth 200. pcrunch.
            eapply deleteExists1. apply H0.

            (* I ::= !Tmp_l *)
            pcrunch.

            pcrunch. pcrunch. pcrunch. pcrunch.

        (* FI *)
        apply mergeTheorem1.

    (* ELSE *) 

        (* (CIf (!Tmp_l === A0) *)
        simpl.
        eapply if_statement.

            (* CLoad T (!T +++ A1) *)
            simpl. pcrunch.

        (* ELSE *)

            (* CIf (!Tmp_r === A0) *)
            simpl. eapply if_statement.

                (* CLoad T (!T +++ A0) *)
                simpl. pcrunch.

            (* ELSE *)

                (* N ::= !I *)
                simpl. eapply compose. pcrunch.

                (* NEW I, A2 *)
                eapply compose. pcrunch.

                (* CStore (I ++++ A0) (!N) *)
                eapply compose. eapply store. compute. reflexivity. compute. reflexivity.
                eapply storeCheck1. (*apply H. apply H0.*)

                (* CLoad Tmp_l (! T +++ A1) *)
                eapply compose. pcrunch.

                (* CStore (! I +++ A1) (! Tmp_l) *)
                eapply compose. eapply store. compute. reflexivity. compute. reflexivity.
                apply storeCheck2. (*apply H. apply H0.*)

                (* (CLoad T (! T +++ A0) *)
                pcrunch.

            (* FI *)
            Set Printing Depth 2000.
            pcrunch. pcrunch. pcrunch. pcrunch. pcrunch. pcrunch.
            apply mergeTheorem2.

        (* FI *)
        pcrunch.
        apply mergeTheorem3.

    (* FI *)
    pcrunch.
    apply mergeTheorem4.

    pcrunch. pcrunch. pcrunch. pcrunch. pcrunch. pcrunch.

    apply implication1.

    intros. inversion H.
    intros. inversion H.

    apply implication2.
    apply implication3.

    intros. apply H.
    intros. inversion H.

    Grab Existential Variables.

    apply nil.

Qed.




























































































































































































































