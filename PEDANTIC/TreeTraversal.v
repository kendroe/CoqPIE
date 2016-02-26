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
Definition precondition : absStateBasic :=
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

Definition afterInitAssigns : absStateBasic :=
    (AbsExistsT (AbsExistsT (AbsExistsT
        (TREE(!!RR,v(0),#2,(#0 :: #1 :: nil)) **
         TREE(!!I,v(1),#2,(#0::nil)) **
         TREE(!!P,v(2),#2,(#0::nil)) **
         (AbsAll (TreeRecords(v(1)))
               ([nth(find(v(1),v(3)),#2) inTree v(0)])) **
         (AbsAll (TreeRecords(v(2)))
               ([nth(find(v(2),v(3)),#2) inTree v(0)])) **
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
Theorem initialization : {{precondition}}initCode{{afterInitAssigns,NoResult}}.

Proof. simpl.
    (* Start by unfolding stuff *)
    unfold initCode. unfold afterInitAssigns. unfold precondition.

    intros. eapply strengthenPost.

    (* I ::= A0 *)
    eapply compose. pcrunch. (eapply basicAssign;pcrunch).

    (* T ::= !RR *)
    eapply compose. pcrunch. (eapply basicAssign;pcrunch).

    (* P ::= A0 *)
    (eapply basicAssign;pcrunch).

    (* Prove the state implication (which is not fully automated) *)
    crunch.

    eapply basicSimplifyEquiv1 in H. Focus 2.

 compute. reflexivity.

    stateImplication.
 
    simpl.
    intros.
    eapply ex_intro. eapply ex_intro. eapply ex_intro. clear H. intros.

    Transparent basicEval.


    reduceHyp. reduceHyp. reduceHyp. reduceHyp. reduceHyp. reduceHyp. reduceHyp. reduceHyp.
    reduceHyp. reduceHyp. reduceHyp. reduceHyp.
    reduceHypothesis. Focus 2.
 (reduceHypothesis; pcrunch; unfold env_p in *; repeat propagate; simplHyp).
    Focus 2.
    decomposeTheState. decomposeTheState.
    simpl. pcrunch. eapply BStateTree. eapply TreeBase. pcrunch.
    pcrunch. pcrunch.
    simpl. pcrunch. eapply BStateTree. eapply TreeBase. pcrunch.
    pcrunch. pcrunch.
    simpl. eapply RSAll. simplifyEval. unfold basicEval.
    simpl. reflexivity. intros. inversion H.
    simpl. eapply RSAll. simplifyEval. unfold basicEval.
    simpl. reflexivity. intros. inversion H.
    decomposeBasicState.

    destruct n. rewrite beq_nat_same. simpl. decomposeBasicState.
    simpl. unfold Rmember. inversion H17. subst. simpl. rewrite beq_nat_same. decomposeBasicState.

    Existential 1 := NoValue.
Qed.


(*
 * Now we define the abstract state that should exist after the while of
 * the main body of the program is executed.
 *
 * This is exactly the same as the state afterInitAssigns except that the
 * condition T=0 and I=0 have been added.
 *)
Definition afterWhile : absStateBasic :=
    (AbsExistsT (AbsExistsT (AbsExistsT
        (TREE(!!RR,v(0),#2,(#0::#1::nil)) **
         TREE(!!I,v(1),#2,(#0::nil)) **
         TREE(!!P,v(2),#2,(#0::nil)) **
         (AbsAll (TreeRecords(v(2)))
               ([nth(find(v(2),v(3)),#2) inTree v(0)])) **
         [(!!T)====#0])))).

Definition loopInv : absStateBasic :=
    (AbsExistsT (AbsExistsT (AbsExistsT
        (TREE(!!RR,v(0),#2,(#0::#1::nil)) **
         TREE(!!I,v(1),#2,(#0::nil)) **
         TREE(!!P,AbsQVar 2,#2,(#0::nil)) **
         (AbsAll (TreeRecords(v(1)))
               ([nth(find(v(1),v(3)),#2) inTree v(0)])) **
         (AbsAll (TreeRecords(v(2)))
               ([nth(find(v(2),v(3)),#2) inTree v(0)])) **
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

Theorem loopInvariant :
    {{afterInitAssigns}}loop{{afterWhile,NoResult}}.
Proof.
    (* Break up the while portion of the loop *)
    unfold loop. unfold afterWhile. unfold afterInitAssigns.

    (* At this point, our sequent looks something like this: (Compare this to figure 4 in
       the paper.

      {{AbsExistsT
          (AbsExistsT
             (AbsExistsT
                (TREE(!!(RR), v(0), #2, #0 :: #1 :: nil) **
                 TREE(!!(I), v(1), #2, #0 :: nil) **
                 TREE(!!(P), v(2), #2, #0 :: nil) **
                 AbsAll TreeRecords(v(1)) ([nth(find(v(1), v(3)), #2) inTree v(0)]) **
                 AbsAll TreeRecords(v(2)) ([nth(find(v(2), v(3)), #2) inTree v(0)]) **
                 [!!(T) ==== #0 \\// !!(T) inTree v(0)])))}}
      WHILE ALnot (!T === A0)
      DO N ::= !P;
         NEW P, A2;
         CStore (!P +++ A1) (!T);
         CStore (!P +++ A0) (!N);
         CLoad Tmp_l (!T +++ A0);
         CLoad Tmp_r (!T +++ A1);
         IF ALand (!Tmp_l === A0) (!Tmp_r === A0)
         THEN IF !I === A0 THEN T ::= A0
              ELSE CLoad T (!I +++ A1);
                   CLoad Tmp_l (!I +++ A0); DELETE !I, A2; I ::= !Tmp_l
         ELSE IF !Tmp_l === A0 THEN CLoad T (!T +++ A1)
              ELSE IF !Tmp_r === A0 THEN CLoad T (!T +++ A0)
                   ELSE N ::= !I;
                        NEW I, A2;
                        CStore (!I +++ A0) (!N);
                        CLoad Tmp_l (!T +++ A1);
                        CStore (!I +++ A1) (!Tmp_l); CLoad T (!T +++ A0) LOOP
      {{AbsExistsT
          (AbsExistsT
             (AbsExistsT
                (TREE(!!(RR), v(0), #2, #0 :: #1 :: nil) **
                 TREE(!!(I), v(1), #2, #0 :: nil) **
                 TREE(!!(P), v(2), #2, #0 :: nil) **
                 AbsAll TreeRecords(v(2)) ([nth(find(v(2), v(3)), #2) inTree v(0)]) **
                 [!!(T) ==== #0]))), NoResult}}*)

    (* WHILE ALnot (!T === A0) DO *)
    eapply strengthenPost.
    eapply while with (invariant := loopInv). unfold loopInv.
    eapply strengthenPost.

    (* N ::= !P; *)
    eapply compose. pcrunch. (eapply basicAssign; pcrunch).

    (* NEW P,ANum(Size_l); *)
    eapply compose. pcrunch. (eapply new_thm; pcrunch).

    simp. simp. simp.

    (*assert (simplifyState 0 (nil : list (@Context unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit)))
    ((v(0) ++++ #0 |-> v(1) **
     [!!(P) ==== v(0)]):absStateBasic)=AbsEmpty). simpl.

    assert (buildStateContext ([!!(P)====v(0)]:absStateBasic)=buildStateContext (AbsEmpty)).
    simpl.*)

    (* CStore ((!P)+++(ANum F_p)) (!T)) *)
    eapply compose. pcrunch. store.

    (* CStore ((!P)+++(ANum F_n)) (!N)) *)
    eapply compose. pcrunch. store.

    simp.

    (* CLoad Tmp_l ((!T)+++ANum(F_l)) *)
    eapply compose. pcrunch.

    (*eapply simplifyPre.
    eapply SEP. eapply SETSimplifyInExistsT. eapply SETSimplifyInExistsT. eapply SETSimplifyInExistsT.
    eapply SETResolvePredicates1. solveSPickElement. solveSPickElement.*)

    load_traverse. 

    simp.

    (* CLoad Tmp_r ((!T)+++ANum(F_r)) *)
    eapply compose. pcrunch. load_traverse.

    simp. simp.

    (* IF (ALand (!Tmp_l === A0) (!Tmp_r === A0)) *)
    eapply if_statement.
    (* IF (!I === A0) *)
        eapply if_statement.
            (* T ::= A0 *)
            (eapply basicAssign; pcrunch).

            (* ELSE *)
            simp. simp. simp. simp.

            (* Right before unfolding, we have the following:
            {{AbsExistsT
                (AbsExistsT
                   (AbsExistsT
                      ([!!(Tmp_l) ==== #0] **
                       [~~ !!(I) ==== #0] **
                       [!!(Tmp_r) ==== #0] **
                       [!!(Tmp_r) ==== #0 \\// !!(Tmp_r) inTree v(0)] **
                       [nth(nth(find(v(0), !!(T)), #2), #0) ==== !!(Tmp_r)] **
                       [nth(nth(find(v(0), !!(T)), #1), #0) ==== #0] **
                       [!!(T) inTree v(0)] **
                       !!(P) ++++ #0 |-> !!(N) **
                       !!(P) ++++ #1 |-> !!(T) **
                       [~~ !!(T) ==== #0] **
                       TREE(!!(RR), v(0), #2, #0 :: #1 :: nil) **
                       TREE(!!(I), v(1), #2, #0 :: nil) **
                       TREE(!!(N), v(2), #2, #0 :: nil) **
                       AbsAll TreeRecords(v(1)) ([nth(find(v(1), v(3)), #2) inTree v(0)]) **
                       AbsAll TreeRecords(v(2)) ([nth(find(v(2), v(3)), #2) inTree v(0)]))))}}
            CLoad T (!I +++ A1); CLoad Tmp_l (!I +++ A0); DELETE !I, A2; I ::= !Tmp_l
            {{?268448, NoResult}}
            *)

            (* Unfold the tree pointed to by !I before proceeding with the first statement *)
            eapply unfold_pre. unfoldHeap (@AbsVar unit eq_unit (@basicEval unit) I).

            simp. simp. simp.

            (* Now things look like this (and we can apply our load operator)
            {{AbsExistsT
                (AbsExistsT
                   (AbsExistsT
                      (AbsExistsT
                         (AbsExistsT
                            (!!(I) ++++ #1 |-> v(1) **
                             !!(I) ++++ #0 |-> nth(v(0), #0) **
                             TREE(nth(v(0), #0),
                             nth(list(!!(I) :: v(0) :: v(1) :: nil), #1), #2, #0 :: nil) **
                             [!!(Tmp_l) ==== #0] **
                             [~~ !!(I) ==== #0] **
                             [!!(Tmp_r) ==== #0] **
                             [!!(Tmp_r) ==== #0 \\// !!(Tmp_r) inTree v(2)] **
                             [nth(nth(find(v(2), !!(T)), #2), #0) ==== !!(Tmp_r)] **
                             [nth(nth(find(v(2), !!(T)), #1), #0) ==== #0] **
                             [!!(T) inTree v(2)] **
                             !!(P) ++++ #0 |-> !!(N) **
                             !!(P) ++++ #1 |-> !!(T) **
                             [~~ !!(T) ==== #0] **
                             TREE(!!(RR), v(2), #2, #0 :: #1 :: nil) **
                             AbsEmpty **
                             TREE(!!(N), v(4), #2, #0 :: nil) **
                             AbsAll TreeRecords(list(!!(I) :: v(0) :: v(1) :: nil))
                               ([nth(find(list(!!(I) :: v(0) :: v(1) :: nil), v(5)), #2)
                                 inTree v(2)]) **
                             AbsAll TreeRecords(v(4))
                               ([nth(find(v(4), v(5)), #2) inTree v(2)]))))))}}
            CLoad T (!I +++ A1); CLoad Tmp_l (!I +++ A0); DELETE !I, A2; I ::= !Tmp_l
            {{?268448, NoResult}}
            *)

            (* CLoad T ((!I)+++ANum(F_p)) *)
            eapply compose. pcrunch. (eapply load; pcrunch).

            (*
            {{AbsExistsT
                (AbsExistsT
                   (AbsExistsT
                      (AbsExistsT
                         (AbsExistsT
                            (AbsExistsT
                               ([!!(T) ==== v(2)] **
                                !!(I) ++++ #1 |-> v(2) **
                                !!(I) ++++ #0 |-> nth(v(1), #0) **
                                TREE(nth(v(1), #0),
                                nth(list(!!(I) :: v(1) :: v(2) :: nil), #1), #2,
                                #0 :: nil) **
                                [!!(Tmp_l) ==== #0] **
                                [~~ !!(I) ==== #0] **
                                [!!(Tmp_r) ==== #0] **
                                [!!(Tmp_r) ==== #0 \\// !!(Tmp_r) inTree v(3)] **
                                [nth(nth(find(v(3), v(0)), #2), #0) ==== !!(Tmp_r)] **
                                [nth(nth(find(v(3), v(0)), #1), #0) ==== #0] **
                                [v(0) inTree v(3)] **
                                !!(P) ++++ #0 |-> !!(N) **
                                !!(P) ++++ #1 |-> v(0) **
                                [~~ v(0) ==== #0] **
                                TREE(!!(RR), v(3), #2, #0 :: #1 :: nil) **
                                AbsEmpty **
                                TREE(!!(N), v(5), #2, #0 :: nil) **
                                AbsAll TreeRecords(list(!!(I) :: v(1) :: v(2) :: nil))
                                  ([nth(find(list(!!(I) :: v(1) :: v(2) :: nil), v(6)),
                                    #2) inTree v(3)]) **
                                AbsAll TreeRecords(v(5))
                                  ([nth(find(v(5), v(6)), #2) inTree v(3)])))))))}}
            CLoad Tmp_l (!I +++ A0); DELETE !I, A2; I ::= !Tmp_l {{?268448, NoResult}}
            *)

            (* CLoad Tmp_l ((!I)+++ANum(F_n)) *)
            eapply compose. pcrunch. (eapply load; pcrunch).

            (* DELETE !I,ANum(Size_l) *)
            eapply compose. pcrunch. (eapply @delete_thm_basic; pcrunch). simpl. reflexivity.

            (* I ::= (!Tmp_l)) *)
            (eapply assign; pcrunch). eapply VarAssignedPredicate1. simpl. reflexivity.
            solveSPickElement. solveSPickElement.

            (* Merge the left and right branches of the inner if *)
            eapply mergeSimplifyLeft. compute. reflexivity.
            eapply mergeSimplifyLeft. compute. reflexivity.
            eapply mergeSimplifyLeft. compute. reflexivity.
            eapply mergeSimplifyLeft. compute. reflexivity.
            eapply mergeSimplifyRight. compute. reflexivity.
            eapply mergeSimplifyRight. compute. reflexivity.
            eapply mergeSimplifyRight. compute. reflexivity.
            eapply mergeSimplifyRight. compute. reflexivity.

            startMerge.

                doMergeStates. DMRemoveZeroTree2 ((!!I) : absExpBasic).
                DMRemoveZeroAll2.
                (* Special case where two predicates need to be or'ed together *)
                eapply DMOrPredicates1. instantiate (2 := (!!(T) ==== #0)). solveSPickElement.
                instantiate (2 := (!!(T) inTree v(3))). solveSPickElement. pcrunch.

            finishMerge.

        (* ELSE *)

            simp. simp. simp.

            (* IF !Tmp_l === A0 THEN CLoad T (!T +++ ANum F_l) *)
            eapply if_statement. simpl.

            simp. simp. simp.

            (* LOAD T (!T +++ ANum F_r) *)
            load_traverse.

            (* ELSE *)

            (* IF !Tmp_r === A0 THEN *)
            eapply if_statement. simpl.

                simp. simp. simp.

                (* CLoad T (!T +++ ANum F_l) *)
                load_traverse.

                (* ELSE *)

                simp. simp. simp.

                (* N ::= !I *)
                eapply compose. pcrunch. (eapply basicAssign; pcrunch).

                (* NEW I, A2 *)
                eapply compose. pcrunch. (eapply new_thm; pcrunch).

                simp. simp. simp. simp.

                (* CStore (!I +++ A0) (!N) *)
                eapply compose. pcrunch. store.

                (* CLoad Tmp_l (!T +++ ANum F_r) *)
                eapply compose. pcrunch. load_traverse.

                (* CStore (!I +++ A1) (!Tmp_l) *)
                eapply compose. pcrunch. store.

                (* CLoad T (!T +++ ANum F_l) *)
                load_traverse.

            (* Merge together the ifs, there are a few steps since the simplify is not fully
               automated.  Simplify is getting completely rewritten after the ITP paper. :-) *)
            eapply mergeSimplifyLeft. compute. reflexivity.
            eapply mergeSimplifyRight. compute. reflexivity.

            (*mergeSimplifyRight.
            eapply mergeSimplifyRight.
            eapply SEP.
            eapply SETSimplifyInExistsT. eapply SETSimplifyInExistsT. eapply SETSimplifyInExistsT. eapply SETSimplifyInExistsT. eapply SETSimplifyInExistsT.
            eapply SETFunElim2. instantiate (2 := Tmp_l). solveSPickElement.
            simpl. reflexivity. intro X. inversion X.
            mergeSimplifyRight.
            eapply mergeSimplifyRight.
            eapply SEP.
            eapply SETSimplifyInExistsT. eapply SETSimplifyInExistsT. eapply SETSimplifyInExistsT. eapply SETSimplifyInExistsT. eapply SETSimplifyInExistsT.
            eapply SETResolvePredicates1.
            instantiate (3 := (!!(Tmp_l) ==== #0)). solveSPickElement. solveSPickElement.
            mergeSimplifyRight.*)

            (* Fold the P tree on both the left and right as well as the I tree on the right *)
            eapply foldRight. foldHeap (@AbsVar unit eq_unit (@basicEval unit) I) (0::nil) 2.
            eapply foldAllRight. foldAll 2.

            eapply foldRight. foldHeap (@AbsVar unit eq_unit (@basicEval unit) P) (0::nil) 2.
            eapply foldAllRight. foldAll 2.

            eapply foldLeft. foldHeap (@AbsVar unit eq_unit (@basicEval unit) P) (0::nil) 2.
            eapply foldAllLeft. foldAll 2.

            startMerge.
                doMergeStates.
            finishMerge.

        (* Second merge of two ifs, P tree needs to be folded on the left *)
        eapply foldLeft. foldHeap (@AbsVar unit eq_unit (@basicEval unit) P) (0::nil) 2.
        eapply foldAllLeft. foldAll 2.

        eapply mergeSimplifyLeft. compute. reflexivity.

        startMerge. doMergeStates. finishMerge.

    (* Third and final merge of two ifs, P tree needs to be folded on the left *)
    eapply foldLeft. foldHeap (@AbsVar unit eq_unit (@basicEval unit) P) (0::nil) 2.
    eapply foldAllLeft. foldAll 2.

    eapply mergeSimplifyLeft. compute. reflexivity.

    startMerge. doMergeStates. finishMerge.

    (* State implication proof *)
    crunch.

    simplifyHyp H. compute in H.

    stateImplication.

    compute.
    intros.
    eapply ex_intro. eapply ex_intro. eapply ex_intro. clear H. intros.

    decomposeTheState; eapply RSEmpty; compute; unfold empty_heap; reflexivity.

    (* State implication proof *)
    unfold loopInv.
    crunch.

    unfold loopInv. crunch.

    simplifyHyp H. simplifyHyp H. simplifyHyp H. compute. unfold loopInv. compute.

    stateImplication.

    crunch. eapply ex_intro. eapply ex_intro. eapply ex_intro. crunch.

    decomposeTheState; eapply RSEmpty; compute; unfold empty_heap; reflexivity.

    (* --- and we need to clean up the existential stuff here *)
    Existential 1 := NoValue.
    Existential 1 := NoValue.
    Existential 1 := NoValue.
    Existential 1 := NoValue.
    Existential 1 := NoValue.
    Existential 1 := NoValue.
    Existential 1 := nil.
    Existential 1 := nil.
    Existential 1 := nil.
    Existential 1 := nil.
    Existential 1 := sbasic.
Qed.

