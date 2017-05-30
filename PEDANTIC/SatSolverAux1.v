(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * SatSolverAux1.v
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
Require Export SatSolverDefs.
Require Export UpdateHelper.
Require Export ClosureHelper.
Require Export MagicWandExistsHelper.
Require Export StateHypHelper.
Opaque haveVarInvariant.

Set Printing Depth 200.

Theorem precond1Core :
    (exists st, realizeState
        ([!!(backtrack)] **
         AbsClosure (invariant ** ([#0 <<<< v(2)] *\/* [v(5) ==== #0]))
           (!!(clauses)
            :: !!(assignments_to_do_head)
               :: !!(stack) :: !!(assignments) :: !!(watches) :: nil)) nil
        st) ->
    (exists st, realizeState (AbsMagicWand
        ([!!(backtrack)] **
         AbsClosure (invariant ** ([#0 <<<< v(2)] *\/* [v(5) ==== #0]))
           (!!(clauses)
            :: !!(assignments_to_do_head)
               :: !!(stack) :: !!(assignments) :: !!(watches) :: nil))
        (AbsExistsT
           (AbsExistsT
              (AbsExistsT
                 (AbsExistsT
                    (!!(stack) ++++ #3 |-> v(3) **
                     !!(stack) ++++ #2 |-> v(2) **
                     !!(stack) ++++ #1 |-> v(1) ** !!(stack) |-> v(0)))))))
     nil st).
Proof.
    (*intros. destruct H.
    eapply ex_intro.
    eapply breakTopClosureThm1. unfold invariant. unfold invariantCore.
    unfold invariantCoreNoTail. compute. reflexivity.
    eapply breakTopClosureThm2 in H. Focus 2. unfold invariant. unfold invariantCore.
    unfold invariantCoreNoTail. compute. reflexivity.
    eapply breakTopClosureThm1. compute. reflexivity.
    simplify. propagateExists. propagateExists. propagateExists. propagateExists.
    propagateExists.
    eapply unfold_rs1.
    unfoldHeap (@AbsVar unit eq_unit (@basicEval unit) stack).
    eapply breakTopClosureThm2 in H. Focus 2. compute. reflexivity.
    simplifyHyp H. propagateExistsHyp H. propagateExistsHyp H. propagateExistsHyp H.
    propagateExistsHyp H. propagateExistsHyp H. eapply unfold_rs2 in H. Focus 2.
    unfoldHeap (@AbsVar unit eq_unit (@basicEval unit) stack).
    simplify. simplifyHyp H. simplify. simplifyHyp H.
 

    eapply magicWandStateExists. simpl. reflexivity. eapply ex_intro.
    apply H. simpl. reflexivity. simpl. reflexivity.
    simpl. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsId. reflexivity.
    compute. reflexivity.

    Grab Existential Variables. apply x.*)
    admit.
Admitted.

Theorem preCond1 : forall x0,
    realizeState
         (AbsUpdateWithLoc
            (AbsUpdateWithLoc
               (AbsUpdateWithLoc
                  (AbsUpdateVar
                     ([!! (backtrack)] **
                      AbsUpdateVar ([# 1] ** loopInvariant) have_var # 0)
                     backtrack # 0) varx !! (stack) ++++ # stack_var_offset)
               valuex !! (stack) ++++ # stack_val_offset) 
            ssss !! (stack) ++++ # next_offset) nil x0 ->
    exists s : state,
    realizeState
      (AbsMagicWand
         (AbsUpdateWithLoc
            (AbsUpdateWithLoc
               (AbsUpdateWithLoc
                  (AbsUpdateVar
                     ([!! (backtrack)] **
                      AbsUpdateVar ([# 1] ** loopInvariant) have_var # 0)
                     backtrack # 0) varx !! (stack) ++++ # stack_var_offset)
               valuex !! (stack) ++++ # stack_val_offset) 
            ssss !! (stack) ++++ # next_offset)
         (AbsExistsT
            (AbsExistsT
               (AbsExistsT
                  (AbsExistsT
                     (AbsExistsT
                        (v( 0) ++++ # 3 |-> v( 4) **
                         v( 0) ++++ # 2 |-> v( 3) **
                         v( 0) ++++ # 1 |-> v( 2) **
                         v( 0) ++++ # 0 |-> v( 1) ** [!! (stack) ==== v( 0)])))))))
      nil s.
Proof.
    (*intros.
    decomposeUpdates.
    simplifyTheHyp H.
    decomposeUpdates.

    eapply simplifyExists. compute. reflexivity.
    eapply simplifyExists. compute. reflexivity.
    eapply simplifyExists. compute. reflexivity.
    eapply simplifyExists. compute. reflexivity.
    eapply simplifyExists. compute. reflexivity.

    eapply existsWithLoc.
    eapply existsWithLoc.
    eapply existsWithLoc.
    eapply existsVar.
    eapply existsVar.
    eapply precond1Core.
    eapply ex_intro.
    apply H.


Grab Existential Variables.
    apply x4. apply 0. apply x4. apply 0.*)
    admit.
Admitted.

Opaque numericRange.
Opaque rangeSet.
Opaque Rmember.
Opaque In.
Opaque nth.

Theorem dumb1: forall x, x + 2 = S (S x).
Proof.
    admit.
Admitted.

Theorem dumb2: forall x, x + 2 + 1 = x + 3.
Proof.
    admit.
Admitted.

Theorem dumb3 : forall x n, S x <= n -> x < n. Proof. admit. Admitted.


Theorem preCond2: forall (s : state) (n : nat) (b : id -> nat), realizeState
        (AbsUpdateVar
           (AbsUpdateVar
              (AbsMagicWand
                 (AbsUpdateWithLoc
                    (AbsUpdateWithLoc
                       (AbsUpdateWithLoc
                          (AbsUpdateVar
                             ([!! (backtrack)] **
                              AbsUpdateVar ([# 1] ** loopInvariant) 
                                have_var # 0) backtrack 
                             # 0) varx !! (stack) ++++ # stack_var_offset)
                       valuex !! (stack) ++++ # stack_val_offset) 
                    ssss !! (stack) ++++ # next_offset)
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (AbsExistsT
                                (v( 0) ++++ # 3 |-> v( 4) **
                                 v( 0) ++++ # 2 |-> v( 3) **
                                 v( 0) ++++ # 1 |-> v( 2) **
                                 v( 0) ++++ # 0 |-> v( 1) **
                                 [!! (stack) ==== v( 0)]))))))) 
              stack !! (ssss)) have_var # 1) nil s ->
       NatValue n =
       basicEval AbsPlusId
         (NatValue (env_p s assignments) :: @NatValue unit (env_p s varx) :: nil) -> heap_p s n <> None.
Proof.
    (*intros. eapply breakTopClosureThm2 in H. Focus 2. unfold loopInvariant. unfold invariant.
    unfold invariantCore. unfold invariantCoreNoTail. compute. reflexivity.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    
    eapply breakTopClosureThm2 in H. Focus 2. compute. reflexivity.
    eapply propagateExistsEquiv1 in H. Focus 2. compute. reflexivity.
    eapply propagateExistsEquiv1 in H. Focus 2. compute. reflexivity.
    eapply propagateExistsEquiv1 in H. Focus 2. compute. reflexivity.
    eapply propagateExistsEquiv1 in H. Focus 2. compute. reflexivity.
    eapply propagateExistsEquiv1 in H. Focus 2. compute. reflexivity.

    eapply unfold_rs2 in H. Focus 2.
    unfoldHeap (@AbsVar unit eq_unit (@basicEval unit) stack).
    Transparent nth.
    simplifyTheHyp H.

    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.

    eapply clearMagicWandUpdateWithLocThm in H. Focus 2. compute. reflexivity.
    eapply removeMagicWandThm in H. Focus 2. compute. reflexivity.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.

    eapply stateAssertionThm in H. compute in H.
    crunch. 

    destruct x3. eapply dumb3 in H27. Transparent basicEval. simpl in H0.
    inversion H0; subst; clear H0. rewrite <- glue1.
    destruct x0. inversion H26. inversion H26; subst; clear H26.

    assert (exists nv, (x14 (((let (x, _) := s in x) assignments)+((let (x, _) := s in x) varx)) = Some nv /\ nth (((let (x, _) := s in x) varx)+1) l NoValue = NatValue nv)).

        eapply heapMap. apply H0. inversion H13; subst; clear H13. apply H27.

    inversion H3; subst; clear H3.

    assert(exists x, heap_p s ((let (x3, _) := s in x3) assignments + (let (x3, _) := s in x3) varx)=Some x).
        eapply ex_intro. eapply H2. eapply H4.

    inversion H3; subst; clear H3.

    rewrite H5. intro X. inversion X.

    inversion H26. inversion H26.

    inversion H27. inversion H27. inversion H27.

    clear H.
    compute. intros.
    eapply stateAssertionThm in H. compute in H. crunch.

    remember ((let (x4, _) := s0 in x4) stack). destruct n0. inversion H15.
   
    eapply ex_intro. simpl. reflexivity.*)
    admit.

Admitted.

Opaque basicEval.





Transparent haveVarInvariant.

Theorem mergeTheorem1 :

 mergeStates
    (AbsUpdateVar
       (AbsUpdateVar
          ([!! (ssss) ==== # 0] **
           AbsUpdateWithLoc
             ([~~ # var_count <<<< !! (iiii)] ** haveVarInvariant) 
             ssss !! (assignments) ++++ !! (iiii)) 
          varx !! (iiii)) have_var # 1)
    ([~~ !! (ssss) ==== # 0] **
     AbsUpdateWithLoc ([~~ # var_count <<<< !! (iiii)] ** haveVarInvariant)
       ssss !! (assignments) ++++ !! (iiii)) haveVarInvariant.
Proof.
    (*eapply mergeReductionUpdateVarLeft.
    eapply mergeReductionUpdateVarLeft2.
    eapply removeCondLeftLeft.
    eapply removeCondRightLeft.
    eapply mergeReductionUpdateWithLocLeft.
    eapply mergeReductionUpdateWithLocRight.
    eapply removeCondLeftLeft.
    eapply removeCondRightLeft.
    eapply mergeSame.

    unfold haveVarInvariant. unfold invariantCore. unfold haveVarComponent.
    unfold invariantCoreNoTail. compute. reflexivity.

    compute. reflexivity.

    unfold haveVarInvariant. unfold invariantCore. unfold haveVarComponent.
    unfold invariantCoreNoTail.
    compute. reflexivity.

    compute. reflexivity.

    unfold haveVarInvariant. unfold invariantCore. 
    unfold invariantCoreNoTail. unfold haveVarComponent. intros.
    eapply breakTopClosureThm2 in H.  Focus 2. compute. reflexivity.
    eapply breakTopClosureThm2 in H.  Focus 2. compute. reflexivity.
    eapply breakTopClosureThm1. compute. reflexivity.
    eapply breakTopClosureThm1. compute. reflexivity.
    eapply stripUpdateVarHyp in H. Focus 2. compute. reflexivity.
        propagateExists. propagateExists. propagateExists. propagateExists.
        propagateExists. propagateExists.
        propagateExistsHyp H. propagateExistsHyp H. propagateExistsHyp H.
        propagateExistsHyp H. propagateExistsHyp H. propagateExistsHyp H.
        eapply stateImplication. apply H. compute. reflexivity. compute. reflexivity.
        prove_implication. compute. reflexivity. compute. reflexivity. clear H.

    intros.
    destruct b0. compute in H. inversion H. destruct b0. compute in H. inversion H.
    destruct b0. compute in H. inversion H. destruct b0. compute in H. inversion H.
    destruct b0. compute in H. inversion H. destruct b0. compute in H. inversion H.
    destruct b0. Focus 2. simpl in H.
    inversion H. compute.
    eapply stateAssertionThm in H0. simpl in H0. crunch.
    eapply realizeStateSimplify. compute. reflexivity.
    inversion H19; subst; clear H19. unfold override in H4. compute in H4.
    eapply RSOrComposeL. eapply RSR. compute.
    inversion H4; subst; clear H4. rewrite H5. Transparent basicEval. simpl.
    reflexivity.
    eapply BTStatePredicate. intro X. inversion X. compute. reflexivity.
    Transparent nth. Opaque basicEval. simpl in H4. simpl in H3. unfold override in H2.
    simpl in H2. rewrite H0 in H3.
    eapply RSOrComposeR. eapply RSR. Transparent basicEval. Opaque nth. simpl.
    Transparent nth. simpl. Opaque nth. Transparent basicEval. simpl in H4.
    assert (match v2 with
    | NatValue _ => NoValue
    | ListValue l => nth (e varx + 1) l NoValue
    | NoValue => NoValue
    | OtherValue _ => NoValue
    end=NatValue 0).
    destruct v2. inversion H4. inversion H5.
 

    erewrite H3. reflexivity. omega. reflexivity. reflexivity. rewrite H1. reflexivity.
    inversion H4. inversion H5.
    inversion H4. inversion H5.
    rewrite H5. simpl. reflexivity.
    eapply BTStatePredicate. intro X. inversion X.
    simpl. reflexivity.

    compute. reflexivity.

    compute. reflexivity.*)
    admit.
Admitted.


Theorem noResult1 : forall x0 st st' f,
        ceval f st
        (CIf (!ssss === A0) (varx ::= !iiii; have_var ::= A1) (SKIP))
        st' x0 -> x0 = NoResult.
Proof.
    (*intros x0 st st' f H.
    inversion H; subst; clear H. inversion H8; subst; clear H8.
    inversion H6; subst; clear H6. reflexivity. inversion H5; subst; clear H5.
    inversion H5; subst; clear H5. inversion H8; subst; clear H8. reflexivity.*)
 admit.
Admitted.

Theorem entailment1 : forall s : state,
   realizeState (AbsUpdateVar haveVarInvariant iiii !!(iiii) ++++ #1) nil s ->
   realizeState haveVarInvariant nil s.
Proof.
    (*intros.
    eapply entailmentUnusedUpdated. apply H.
    Transparent haveVarInvariant. unfold haveVarInvariant. unfold invariantCore.
    unfold invariantCoreNoTail. unfold haveVarComponent. compute. reflexivity.*)
    admit.
Admitted.


Theorem entailment2 : forall x0 : state,
forall x0 : state,
  realizeState
    (AbsUpdateVar
       (AbsUpdateVar
          ([~~ !! (backtrack)] **
           AbsUpdateVar ([# 1] ** loopInvariant) have_var # 0) 
          valuex # 1) iiii # 0) nil x0 ->
  realizeState haveVarInvariant nil x0.
Proof.
    (*intros.
    eapply stripUpdateVarHyp in H. Focus 2. compute. reflexivity.
    eapply stripUpdateVarHyp in H. Focus 2. compute. reflexivity.
    eapply stripUpdateVarHyp in H. Focus 2. compute. reflexivity.
    propagateExistsHyp H. propagateExistsHyp H. propagateExistsHyp H.
    propagateExistsHyp H. propagateExistsHyp H. propagateExistsHyp H.
    propagateExistsHyp H. propagateExistsHyp H. propagateExistsHyp H.
    eapply breakTopClosureThm2 in H.  Focus 2. compute. reflexivity.
    eapply breakTopClosureThm2 in H.  Focus 2. compute. reflexivity.
    Transparent haveVarInvariant. unfold haveVarInvariant.
    unfold invariantCore. unfold haveVarComponent. unfold invariantCoreNoTail.
    eapply breakTopClosureThm1. compute. reflexivity.
    eapply breakTopClosureThm1. compute. reflexivity.

    eapply stateImplication. apply H. compute. reflexivity. compute. reflexivity.
    prove_implication. compute. reflexivity. compute. reflexivity. clear H.

    intros. eapply stateAssertionThm in H0. simpl in H0. crunch.
    eapply realizeStateSimplify. compute. reflexivity.

    eapply RSOrComposeL.  eapply RSR. compute. Transparent basicEval. unfold basicEval.
    rewrite H3. simpl. reflexivity.
    eapply BTStatePredicate. omega. unfold empty_heap. simpl. reflexivity.*)
    admit.
Admitted.

Opaque basicEval.

Fixpoint findArray v (e : absState) :=
    match e with
    | AbsStar l r => match findArray v l with
                     | Some (x,l') => Some (x,AbsStar l' r)
                     | None => match findArray v r with
                               | Some (x,r') => Some (x,AbsStar l r')
                               | None => None
                               end
                     end
    | AbsUpdateVar s vv r => match findArray v s with
                             | Some (a,s') => if hasVarState a vv then None else Some (a,AbsUpdateVar s' vv r)
                             | None => None
                             end
    | AbsUpdateWithLoc s vv r => match findArray v s with
                                 | Some (a,s') => if hasVarState a vv then None else Some (a,AbsUpdateWithLoc s' vv r)
                                 | None => None
                                 end
    | (ARRAY(l,#c,m)) => if beq_absExp l v then Some (ARRAY(l,#c,m),AbsEmpty) else None
    | _ => None
    end.

Function  stripUpdateLoc (s : absState) :=
    match s with
    | AbsUpdateLoc ss (i++++o) v => match findArray i ss with
                                    | Some (ARRAY(a,b,v(c)),ss') => Some ([nth(v(c),o)====v] ** (AbsExistsT ((replaceStateVar (S c) (replacenth(v(S c),(addExpVar 1 o),v(0))) (addStateVar 1 ss') ** ARRAY(addExpVar 1 a,addExpVar 1 b,v(S(c)))))),ss,(o<<<<b))
                                    | _ => match stripUpdateLoc ss with
                                           | Some (ss,t,p) => Some (AbsUpdateLoc ss (i++++o) v,t,p)
                                           | None => None
                                           end
                                    end
    | AbsExistsT x => match stripUpdateLoc x with
                      | Some (x,t,p) => Some (AbsExistsT x,t,p)
                      | _ => None
                      end
    | AbsMagicWand l r => match stripUpdateLoc l with
                          | Some (l,t,p) => Some (AbsMagicWand l r,t,p)
                          | None => None
                          end
    | AbsStar l r => match stripUpdateLoc r return option (absState * absState  * absExp) with
                     | Some (r,t,p) => Some (AbsStar l r,t,p)
                     | None => match stripUpdateLoc l with
                               | Some (l,t,p) => Some (AbsStar l r,t,p)
                               | None => None
                               end
                     end
    | x => None
    end.

Theorem removeUpdateLocLeft : forall l l' r m a b,
    Some (l',a,b) = stripUpdateLoc l ->
    (forall bind s, realizeState a bind s -> exists q, absEval (fst s) bind b = NatValue (S q)) ->
    mergeStates l' r m ->
    mergeStates l r m.
Proof.
    admit.
Admitted.



Theorem mergeTheorem2Index : forall bind s, realizeState
        ((([!! (ssss) ==== nth( v( 7), # 0)] **
           [!! (valuex) ==== v( 9)] **
           [!! (varx) ==== v( 8)] **
           ((((((TREE( !! (clauses), v( 0), # 21, # 0 :: nil) **
                 TREE( !! (assignments_to_do_head), v( 1), # 4, # 0 :: nil) **
                 TREE( nth( v( 7), # 0), v( 7), # 4, # 0 :: nil) **
                 ARRAY( !! (assignments), # 4, v( 2)) **
                 ARRAY( !! (watches), # 4, v( 3))) **
                ((([!! (varx) <<<< # 4] **
                   AbsAll TreeRecords( v( 7))
                     ([nth( find( v( 8), v( 0)), # 2) <<<< # 4])) **
                  (([!! (valuex) ==== # 1] *\/* [!! (valuex) ==== # 2]) **
                   AbsAll TreeRecords( v( 7))
                     ([nth( find( v( 8), v( 0)), # 3) ==== # 1] *\/*
                      [nth( find( v( 8), v( 0)), # 3) ==== # 2])) **
                  ([nth( v( 2), !! (varx)) ==== !! (valuex)] **
                   AbsAll TreeRecords( v( 7))
                     ([nth( v( 3), nth( find( v( 8), v( 0)), # 2)) ====
                       nth( find( v( 8), v( 0)), # 3)])) **
                  AbsAll TreeRecords( v( 7))
                    ([~~ !! (varx) ==== nth( find( v( 8), v( 0)), # 2)]) **
                  AbsAll TreeRecords( v( 7))
                    (AbsAll TreeRecords( nth( find( v( 8), v( 0)), # 1))
                       ([~~
                         nth( find( v( 9), v( 1)), # 2) ====
                         nth( find( nth( find( v( 9), v( 1)), # 1), v( 0)),
                         # 2)]))) **
                 AbsAll range( # 0, # 4)
                   ([nth( v( 3), v( 0)) ==== # 0] *\/*
                    [!! (varx) ==== v( 0)] *\/*
                    AbsExists TreeRecords( v( 8))
                      ([nth( find( v( 9), v( 0)), # 2) ==== v( 1)] **
                       [nth( find( v( 9), v( 0)), # 3) ====
                        nth( v( 4), v( 1))]))) **
                AbsAll TreeRecords( v( 1))
                  ([--( v( 2), v( 0) )---> # 1 ==== # 0] **
                   [nth( v( 2), v( 0)) ==== v( 0)] *\/*
                   [--( v( 2), v( 0) )---> # 1 inTree v( 0)] **
                   [--( v( 2), --( v( 2), v( 0) )---> # 1 )---> # 0 ====
                    v( 0)]) **
                AbsEach range( # 0, # 4)
                  (AbsExistsT
                     (Path( nth( list( v( 7)
                                       :: v( 9)
                                          :: !! (varx)
                                             :: !! (valuex) :: v( 12) :: nil),
                            v( 4)), v( 0), v( 5), 
                      # 21, # 13 ++++ v( 4) :: nil) **
                      AbsAll TreeRecords( v( 5))
                        ([--( v( 6), v( 0) )---> (# 17 ++++ v( 3)) ==== # 0] **
                         [nth( v( 6), v( 0)) ==== v( 0)] *\/*
                         [--( v( 6), v( 0) )---> (# 17 ++++ v( 3))
                          inTree v( 0)] **
                         [--( v( 6), --( v( 6), v( 0) )---> (# 17 ++++ v( 3))
                          )---> (# 13 ++++ v( 3)) ==== 
                          v( 0)]) **
                      AbsAll TreeRecords( v( 0))
                        (AbsExists range( # 0, # 4)
                           ([--( v( 1),
                             list( v( 9)
                                   :: v( 11)
                                      :: !! (varx)
                                         :: !! (valuex) :: v( 14) :: nil)
                             )---> (# 1 ++++ v( 0))] **
                            ([nth( v( 4), v( 0)) ==== # 2] *\/*
                             [nth( v( 4), v( 0)) ==== # 0]) *\/*
                            [--( v( 1),
                             list( v( 9)
                                   :: v( 11)
                                      :: !! (varx)
                                         :: !! (valuex) :: v( 14) :: nil)
                             )---> (# 5 ++++ v( 2))] **
                            ([nth( v( 4), v( 0)) ==== # 1] *\/*
                             [nth( v( 4), v( 0)) ==== # 0]))) **
                      AbsAll range( # 0, # 4)
                        (([--( v( 0), v( 1) )---> (# 9 ++++ v( 0)) ==== # 0] *\/*
                          [--( v( 0), v( 1) )---> (# 1 ++++ v( 0))]) *\/*
                         [--( v( 0), v( 1) )---> (# 5 ++++ v( 0))]) **
                      AbsAll range( # 0, # 4)
                        ([# 0 <<<< --( v( 1), v( 5) )---> (# 9 ++++ v( 0))] **
                         ([# 0 <<<< --( v( 1), v( 5) )---> (# 17 ++++ v( 0))] *\/*
                          [nth( v( 0), v( 2)) ==== v( 1)]) *\/*
                         ([--( v( 1), v( 5) )---> (# 9 ++++ v( 0)) ==== # 0] **
                          [--( v( 1), v( 5) )---> (# 17 ++++ v( 0)) ==== # 0]) **
                         [~~ nth( v( 4), v( 0)) ==== v( 5)]) **
                      SUM( range( # 0, # 4),
                      # 0 <<<< --( v( 0), v( 4) )---> (# 9 ++++ v( 0)), 
                      # 2) **
                      (SUM( range( # 0, # 4),
                       (--( v( 4), v( 3) )---> (# 1 ++++ v( 0)) \\//
                        --( v( 4), v( 3) )---> (# 5 ++++ v( 0))) //\\
                       nth( v( 3), v( 0)) ==== # 0, 
                       # 1) **
                       AbsAll range( # 0, # 4)
                         ([# 0 <<<< --( v( 1), v( 5) )---> (# 9 ++++ v( 0))] **
                          [nth( v( 5), v( 0)) ==== # 0] *\/*
                          [# 0 <<<< nth( v( 5), v( 0))] *\/*
                          [--( v( 1), v( 5) )---> (# 1 ++++ v( 0)) ==== # 0] **
                          [--( v( 1), v( 5) )---> (# 5 ++++ v( 0)) ==== # 0]) **
                       AbsAll range( # 0, # 4)
                         (AbsAll range( # 0, # 4)
                            ((((([--( v( 2), v( 6) )---> (# 9 ++++ v( 0))] *\/*
                                 [--( v( 2), v( 6) )---> (# 1 ++++ v( 0)) ====
                                  # 0] **
                                 [--( v( 2), v( 6) )---> (# 5 ++++ v( 0)) ====
                                  # 0]) *\/*
                                [~~ --( v( 2), v( 6) )---> (# 9 ++++ v( 1))]) *\/*
                               [nth( v( 5), v( 1)) ==== # 0]) *\/*
                              [v( 0) ==== v( 1)]) *\/*
                             AbsExists TreeRecords( v( 4))
                               ([nth( find( v( 5), v( 0)), # 2) ==== v( 2)] **
                                AbsExists TreeRecords( find( v( 5), v( 0)))
                                  ([nth( find( v( 6), v( 0)), # 2) ==== v( 1)])))) *\/*
                       AbsExists range( # 0, # 4)
                         ([--( v( 1), v( 5) )---> (# 1 ++++ v( 0))] **
                          [nth( v( 4), v( 0)) ==== # 2] *\/*
                          [--( v( 1), v( 5) )---> (# 5 ++++ v( 0))] **
                          [nth( v( 1), v( 5)) ==== # 1]) **
                       AbsAll range( # 0, # 4)
                         ([# 0 ==== nth( v( 4), v( 0))] *\/*
                          [--( v( 1), v( 5) )---> (# 9 ++++ v( 0)) ==== # 0] **
                          [# 0 <<<< nth( v( 4), v( 0))] *\/*
                          AbsExists TreeRecords( v( 3))
                            ([nth( find( v( 4), v( 0)), # 2) ==== v( 1)]) **
                          AbsExists TreeRecords( find( v( 0), v( 0)))
                            ([# 0 <<<<
                              --( v( 2), v( 6)
                              )---> (# 1 ++++ nth( find( v( 4), v( 0)), # 2))] **
                             [nth( find( v( 4), v( 0)), # 3) ==== # 2] *\/*
                             [# 0 <<<<
                              --( v( 2), v( 6)
                              )---> (# 5 ++++ nth( find( v( 4), v( 0)), # 2))] **
                             [nth( find( v( 4), v( 0)), # 3) ==== # 1])) *\/*
                       AbsAll range( # 0, # 4)
                         ([--( v( 1), v( 5) )---> (# 9 ++++ v( 0)) ==== # 0] *\/*
                          [nth( v( 4), v( 0)) ==== # 0]))))) **
               [!! (assignments_to_do_head) inTree v( 1)] **
               [nth( find( !! (assignments_to_do_head), v( 1)), # 1) ==== # 0]) **
              [# 0 <<<< v( 5)]) ** [v( 6) ==== # 0]) ** 
            [v( 4)]) ** [!! (backtrack) ==== # 0]) **
          [!! (stack) ==== !! (ssss)]) ** [!! (have_var) ==== # 1]) bind s ->
exists q : nat, absEval
    (fst s) bind !! (varx) <<<< # 4 = NatValue (S q).
Proof.
    intros bind s H.
    admit.
Admitted.

Theorem mergeImplies : forall l r m,
    (exists m', mergeStates l r m' /\ (forall s, realizeState m' nil s -> realizeState m nil s)) ->
    mergeStates l r m.
Proof.
    admit.
Admitted.

Theorem mergePredicateTheorem1 :
forall (eee : env) (hhh : heap) (bbb : list Value),
  length bbb = 12 ->
  realizeState
    (([nth( v( 4), !! (varx)) ==== # 0] **
      ((([!! (ssss) ==== nth( v( 8), # 0)] **
         [!! (valuex) ==== v( 10)] **
         [!! (varx) ==== v( 9)] **
         ((((((AbsEmpty ** AbsEmpty ** AbsEmpty ** AbsEmpty) **
              ((([!! (varx) <<<< # 4] ** AbsEmpty) **
                (([!! (valuex) ==== # 1] *\/* [!! (valuex) ==== # 2]) **
                 AbsEmpty) **
                ([v( 0) ==== !! (valuex)] **
                 AbsAll TreeRecords( v( 8))
                   ([nth( replacenth( v( 5), !! (varx), !! (valuex)),
                     nth( find( v( 9), v( 0)), # 2)) ====
                     nth( find( v( 9), v( 0)), # 3)])) ** AbsEmpty) **
               AbsAll range( # 0, # 4)
                 ([nth( v( 5), v( 0)) ==== # 0] *\/*
                  [!! (varx) ==== v( 0)] *\/*
                  AbsExists TreeRecords( v( 9))
                    ([nth( find( v( 10), v( 0)), # 2) ==== v( 1)] **
                     [nth( find( v( 10), v( 0)), # 3) ==== nth( v( 6), v( 1))]))) **
              AbsEmpty **
              AbsEach range( # 0, # 4)
                (AbsExistsT
                   (Path( nth( list( v( 9)
                                     :: v( 10)
                                        :: !! (varx)
                                           :: !! (valuex) :: v( 13) :: nil),
                          replacenth( v( 6), !! (varx), !! (valuex))), 
                    v( 0), v( 7), # 21,
                    # 13 ++++ replacenth( v( 6), !! (varx), !! (valuex))
                    :: nil) **
                    AbsAll TreeRecords( v( 7))
                      ([--( v( 8), v( 0) )---> (# 17 ++++ !! (valuex)) ====
                        # 0] ** [nth( v( 8), v( 0)) ==== v( 0)] *\/*
                       [--( v( 8), v( 0) )---> (# 17 ++++ !! (valuex))
                        inTree v( 0)] **
                       [--( v( 8),
                        --( v( 8), v( 0) )---> (# 17 ++++ !! (valuex))
                        )---> (# 13 ++++ !! (valuex)) ==== 
                        v( 0)]) **
                    AbsAll TreeRecords( v( 0))
                      (AbsExists range( # 0, # 4)
                         ([--( v( 1),
                           list( v( 11)
                                 :: v( 12)
                                    :: !! (varx)
                                       :: !! (valuex) :: v( 15) :: nil)
                           )---> (# 1 ++++ v( 0))] **
                          ([nth( !! (valuex), v( 0)) ==== # 2] *\/*
                           [nth( !! (valuex), v( 0)) ==== # 0]) *\/*
                          [--( v( 1),
                           list( v( 11)
                                 :: v( 12)
                                    :: !! (varx)
                                       :: !! (valuex) :: v( 15) :: nil)
                           )---> (# 5 ++++ v( 2))] **
                          ([nth( !! (valuex), v( 0)) ==== # 1] *\/*
                           [nth( !! (valuex), v( 0)) ==== # 0]))) **
                    AbsAll range( # 0, # 4)
                      (([--( v( 0), v( 1) )---> (# 9 ++++ v( 0)) ==== # 0] *\/*
                        [--( v( 0), v( 1) )---> (# 1 ++++ v( 0))]) *\/*
                       [--( v( 0), v( 1) )---> (# 5 ++++ v( 0))]) **
                    AbsAll range( # 0, # 4)
                      ([# 0 <<<<
                        --( v( 1), replacenth( v( 7), !! (varx), !! (valuex))
                        )---> (# 9 ++++ v( 0))] **
                       ([# 0 <<<<
                         --( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 17 ++++ v( 0))] *\/*
                        [nth( v( 0), v( 2)) ==== v( 1)]) *\/*
                       ([--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 9 ++++ v( 0)) ==== 
                         # 0] **
                        [--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 17 ++++ v( 0)) ==== 
                         # 0]) **
                       [~~
                        nth( v( 5), v( 0)) ====
                        replacenth( v( 7), !! (varx), !! (valuex))]) **
                    SUM( range( # 0, # 4),
                    # 0 <<<<
                    --( v( 0), replacenth( v( 6), !! (varx), !! (valuex))
                    )---> (# 9 ++++ v( 0)), # 2) **
                    (SUM( range( # 0, # 4),
                     (--( replacenth( v( 6), !! (varx), !! (valuex)), 
                      v( 4) )---> (# 1 ++++ v( 0)) \\//
                      --( replacenth( v( 6), !! (varx), !! (valuex)), 
                      v( 4) )---> (# 5 ++++ v( 0))) //\\
                     nth( v( 4), v( 0)) ==== # 0, 
                     # 1) **
                     AbsAll range( # 0, # 4)
                       ([# 0 <<<<
                         --( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 9 ++++ v( 0))] **
                        [nth( replacenth( v( 7), !! (varx), !! (valuex)),
                         v( 0)) ==== # 0] *\/*
                        [# 0 <<<<
                         nth( replacenth( v( 7), !! (varx), !! (valuex)),
                         v( 0))] *\/*
                        [--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 1 ++++ v( 0)) ==== 
                         # 0] **
                        [--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 5 ++++ v( 0)) ==== 
                         # 0]) **
                     AbsAll range( # 0, # 4)
                       (AbsAll range( # 0, # 4)
                          ((((([--( v( 2),
                                replacenth( v( 8), !! (varx), !! (valuex))
                                )---> (# 9 ++++ v( 0))] *\/*
                               [--( v( 2),
                                replacenth( v( 8), !! (varx), !! (valuex))
                                )---> (# 1 ++++ v( 0)) ==== 
                                # 0] **
                               [--( v( 2),
                                replacenth( v( 8), !! (varx), !! (valuex))
                                )---> (# 5 ++++ v( 0)) ==== 
                                # 0]) *\/*
                              [~~
                               --( v( 2),
                               replacenth( v( 8), !! (varx), !! (valuex))
                               )---> (# 9 ++++ v( 1))]) *\/*
                             [nth( v( 6), v( 1)) ==== # 0]) *\/*
                            [v( 0) ==== v( 1)]) *\/*
                           AbsExists (AbsConstVal (ListValue nil))
                             (AbsExists
                                TreeRecords( find( !! (valuex), v( 0)))
                                ([nth( find( !! (valuex), v( 1)), # 2) ====
                                  v( 3)] **
                                 [nth( find( !! (valuex), v( 0)), # 2) ====
                                  v( 1)])))) *\/*
                     AbsExists range( # 0, # 4)
                       (([--( v( 1),
                          replacenth( v( 7), !! (varx), !! (valuex))
                          )---> (# 1 ++++ v( 0))] **
                         [nth( v( 5), v( 0)) ==== # 2] *\/*
                         [--( v( 1),
                          replacenth( v( 7), !! (varx), !! (valuex))
                          )---> (# 5 ++++ v( 0))] **
                         [nth( v( 1),
                          replacenth( v( 7), !! (varx), !! (valuex))) ====
                          # 1]) **
                        AbsAll range( # 0, # 4)
                          ([# 0 ==== nth( v( 6), v( 0))] *\/*
                           [--( v( 2),
                            replacenth( v( 8), !! (varx), !! (valuex))
                            )---> (# 9 ++++ v( 0)) ==== 
                            # 0] ** [# 0 <<<< nth( v( 6), v( 0))] *\/*
                           AbsExists (AbsConstVal (ListValue nil))
                             ([nth( find( !! (valuex), v( 0)), # 2) ====
                               v( 1)] **
                              AbsExists TreeRecords( find( v( 1), v( 1)))
                                ([# 0 <<<<
                                  --( v( 4),
                                  replacenth( v( 10), !! (varx), !! (valuex))
                                  )---> (# 1 ++++
                                         nth( find( !! (valuex), v( 0)), # 2))] **
                                 [nth( find( !! (valuex), v( 0)), # 3) ====
                                  # 2] *\/*
                                 [# 0 <<<<
                                  --( v( 4),
                                  replacenth( v( 10), !! (varx), !! (valuex))
                                  )---> (# 5 ++++
                                         nth( find( !! (valuex), v( 0)), # 2))] **
                                 [nth( find( !! (valuex), v( 0)), # 3) ====
                                  # 1])))) *\/*
                     AbsAll range( # 0, # 4)
                       ([--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 9 ++++ v( 0)) ==== 
                         # 0] *\/* [nth( v( 5), v( 0)) ==== # 0]))))) **
             AbsEmpty ** AbsEmpty) **
            ([# 0 <<<< v( 7)] *\/* [v( 6) ==== # 0])) ** 
           [!! (valuex)]) ** [v( 3) ==== # 0]) ** 
         [!! (backtrack) ==== # 0]) ** [!! (stack) ==== !! (ssss)]) **
       [!! (have_var) ==== # 1]) ** AbsEmpty) **
     (ARRAY( !! (assignments), # 4, v( 4)) **
      [nth( find( !! (assignments_to_do_head), v( 2)), # 1) ==== # 0] **
      [!! (assignments_to_do_head) inTree v( 2)] **
      AbsAll TreeRecords( v( 2))
        ([--( v( 3), v( 0) )---> # 1 ==== # 0] **
         [nth( v( 3), v( 0)) ==== v( 0)] *\/*
         [--( v( 3), v( 0) )---> # 1 inTree v( 0)] **
         [--( v( 3), --( v( 3), v( 0) )---> # 1 )---> # 0 ==== v( 0)]) **
      AbsAll TreeRecords( v( 8))
        (AbsAll TreeRecords( nth( find( v( 9), v( 0)), # 2))
           ([~~
             nth( find( v( 10), v( 1)), # 2) ====
             nth( find( nth( find( v( 10), v( 1)), # 2), v( 0)), # 2)])) **
      AbsAll TreeRecords( v( 8))
        ([nth( find( v( 9), v( 0)), # 3) ==== # 1] *\/*
         [nth( find( v( 9), v( 0)), # 3) ==== # 2]) **
      AbsAll TreeRecords( v( 8)) ([nth( find( v( 9), v( 0)), # 2) <<<< # 4]) **
      ARRAY( !! (watches), # 4, v( 5)) **
      TREE( !! (stack), v( 8), # 4, # 0 :: nil) **
      TREE( !! (assignments_to_do_head), v( 2), # 4, # 0 :: nil) **
      TREE( !! (clauses), v( 0), # 21, # 0 :: nil) ** AbsEmpty) **
     build_equivs
       ((!! (have_var) :: # 1 :: nil)
        :: (!! (varx) :: v( 9) :: nil)
           :: (v( 10) :: v( 0) :: !! (valuex) :: nil)
              :: (nth( v( 8), # 0) :: !! (stack) :: !! (ssss) :: nil)
                 :: (nth( v( 4), !! (varx))
                     :: nth( find( !! (assignments_to_do_head), v( 2)), # 1)
                        :: v( 3) :: !! (backtrack) :: # 0 :: nil) :: nil))
    bbb (eee, hhh) ->
  realizeState
    (AbsAll TreeRecords( v( 8))
       ([nth( v( 5), nth( find( v( 9), v( 0)), # 2)) ====
         nth( find( v( 9), v( 0)), # 3)])) bbb (eee, empty_heap).
Proof.
    admit.
Admitted.

Theorem mergePredicateTheorem2 :
forall (eee : env) (hhh : heap) (bbb : list Value),
  length bbb = 12 ->
  realizeState
    (([nth( v( 4), !! (varx)) ==== # 0] **
      ((([!! (ssss) ==== nth( v( 8), # 0)] **
         [!! (valuex) ==== v( 10)] **
         [!! (varx) ==== v( 9)] **
         ((((((AbsEmpty ** AbsEmpty ** AbsEmpty ** AbsEmpty) **
              ((([!! (varx) <<<< # 4] ** AbsEmpty) **
                (([!! (valuex) ==== # 1] *\/* [!! (valuex) ==== # 2]) **
                 AbsEmpty) **
                ([v( 0) ==== !! (valuex)] **
                 AbsAll TreeRecords( v( 8))
                   ([nth( replacenth( v( 5), !! (varx), !! (valuex)),
                     nth( find( v( 9), v( 0)), # 2)) ====
                     nth( find( v( 9), v( 0)), # 3)])) ** AbsEmpty) **
               AbsAll range( # 0, # 4)
                 ([nth( v( 5), v( 0)) ==== # 0] *\/*
                  [!! (varx) ==== v( 0)] *\/*
                  AbsExists TreeRecords( v( 9))
                    ([nth( find( v( 10), v( 0)), # 2) ==== v( 1)] **
                     [nth( find( v( 10), v( 0)), # 3) ==== nth( v( 6), v( 1))]))) **
              AbsEmpty **
              AbsEach range( # 0, # 4)
                (AbsExistsT
                   (Path( nth( list( v( 9)
                                     :: v( 10)
                                        :: !! (varx)
                                           :: !! (valuex) :: v( 13) :: nil),
                          replacenth( v( 6), !! (varx), !! (valuex))), 
                    v( 0), v( 7), # 21,
                    # 13 ++++ replacenth( v( 6), !! (varx), !! (valuex))
                    :: nil) **
                    AbsAll TreeRecords( v( 7))
                      ([--( v( 8), v( 0) )---> (# 17 ++++ !! (valuex)) ====
                        # 0] ** [nth( v( 8), v( 0)) ==== v( 0)] *\/*
                       [--( v( 8), v( 0) )---> (# 17 ++++ !! (valuex))
                        inTree v( 0)] **
                       [--( v( 8),
                        --( v( 8), v( 0) )---> (# 17 ++++ !! (valuex))
                        )---> (# 13 ++++ !! (valuex)) ==== 
                        v( 0)]) **
                    AbsAll TreeRecords( v( 0))
                      (AbsExists range( # 0, # 4)
                         ([--( v( 1),
                           list( v( 11)
                                 :: v( 12)
                                    :: !! (varx)
                                       :: !! (valuex) :: v( 15) :: nil)
                           )---> (# 1 ++++ v( 0))] **
                          ([nth( !! (valuex), v( 0)) ==== # 2] *\/*
                           [nth( !! (valuex), v( 0)) ==== # 0]) *\/*
                          [--( v( 1),
                           list( v( 11)
                                 :: v( 12)
                                    :: !! (varx)
                                       :: !! (valuex) :: v( 15) :: nil)
                           )---> (# 5 ++++ v( 2))] **
                          ([nth( !! (valuex), v( 0)) ==== # 1] *\/*
                           [nth( !! (valuex), v( 0)) ==== # 0]))) **
                    AbsAll range( # 0, # 4)
                      (([--( v( 0), v( 1) )---> (# 9 ++++ v( 0)) ==== # 0] *\/*
                        [--( v( 0), v( 1) )---> (# 1 ++++ v( 0))]) *\/*
                       [--( v( 0), v( 1) )---> (# 5 ++++ v( 0))]) **
                    AbsAll range( # 0, # 4)
                      ([# 0 <<<<
                        --( v( 1), replacenth( v( 7), !! (varx), !! (valuex))
                        )---> (# 9 ++++ v( 0))] **
                       ([# 0 <<<<
                         --( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 17 ++++ v( 0))] *\/*
                        [nth( v( 0), v( 2)) ==== v( 1)]) *\/*
                       ([--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 9 ++++ v( 0)) ==== 
                         # 0] **
                        [--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 17 ++++ v( 0)) ==== 
                         # 0]) **
                       [~~
                        nth( v( 5), v( 0)) ====
                        replacenth( v( 7), !! (varx), !! (valuex))]) **
                    SUM( range( # 0, # 4),
                    # 0 <<<<
                    --( v( 0), replacenth( v( 6), !! (varx), !! (valuex))
                    )---> (# 9 ++++ v( 0)), # 2) **
                    (SUM( range( # 0, # 4),
                     (--( replacenth( v( 6), !! (varx), !! (valuex)), 
                      v( 4) )---> (# 1 ++++ v( 0)) \\//
                      --( replacenth( v( 6), !! (varx), !! (valuex)), 
                      v( 4) )---> (# 5 ++++ v( 0))) //\\
                     nth( v( 4), v( 0)) ==== # 0, 
                     # 1) **
                     AbsAll range( # 0, # 4)
                       ([# 0 <<<<
                         --( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 9 ++++ v( 0))] **
                        [nth( replacenth( v( 7), !! (varx), !! (valuex)),
                         v( 0)) ==== # 0] *\/*
                        [# 0 <<<<
                         nth( replacenth( v( 7), !! (varx), !! (valuex)),
                         v( 0))] *\/*
                        [--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 1 ++++ v( 0)) ==== 
                         # 0] **
                        [--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 5 ++++ v( 0)) ==== 
                         # 0]) **
                     AbsAll range( # 0, # 4)
                       (AbsAll range( # 0, # 4)
                          ((((([--( v( 2),
                                replacenth( v( 8), !! (varx), !! (valuex))
                                )---> (# 9 ++++ v( 0))] *\/*
                               [--( v( 2),
                                replacenth( v( 8), !! (varx), !! (valuex))
                                )---> (# 1 ++++ v( 0)) ==== 
                                # 0] **
                               [--( v( 2),
                                replacenth( v( 8), !! (varx), !! (valuex))
                                )---> (# 5 ++++ v( 0)) ==== 
                                # 0]) *\/*
                              [~~
                               --( v( 2),
                               replacenth( v( 8), !! (varx), !! (valuex))
                               )---> (# 9 ++++ v( 1))]) *\/*
                             [nth( v( 6), v( 1)) ==== # 0]) *\/*
                            [v( 0) ==== v( 1)]) *\/*
                           AbsExists (AbsConstVal (ListValue nil))
                             (AbsExists
                                TreeRecords( find( !! (valuex), v( 0)))
                                ([nth( find( !! (valuex), v( 1)), # 2) ====
                                  v( 3)] **
                                 [nth( find( !! (valuex), v( 0)), # 2) ====
                                  v( 1)])))) *\/*
                     AbsExists range( # 0, # 4)
                       (([--( v( 1),
                          replacenth( v( 7), !! (varx), !! (valuex))
                          )---> (# 1 ++++ v( 0))] **
                         [nth( v( 5), v( 0)) ==== # 2] *\/*
                         [--( v( 1),
                          replacenth( v( 7), !! (varx), !! (valuex))
                          )---> (# 5 ++++ v( 0))] **
                         [nth( v( 1),
                          replacenth( v( 7), !! (varx), !! (valuex))) ====
                          # 1]) **
                        AbsAll range( # 0, # 4)
                          ([# 0 ==== nth( v( 6), v( 0))] *\/*
                           [--( v( 2),
                            replacenth( v( 8), !! (varx), !! (valuex))
                            )---> (# 9 ++++ v( 0)) ==== 
                            # 0] ** [# 0 <<<< nth( v( 6), v( 0))] *\/*
                           AbsExists (AbsConstVal (ListValue nil))
                             ([nth( find( !! (valuex), v( 0)), # 2) ====
                               v( 1)] **
                              AbsExists TreeRecords( find( v( 1), v( 1)))
                                ([# 0 <<<<
                                  --( v( 4),
                                  replacenth( v( 10), !! (varx), !! (valuex))
                                  )---> (# 1 ++++
                                         nth( find( !! (valuex), v( 0)), # 2))] **
                                 [nth( find( !! (valuex), v( 0)), # 3) ====
                                  # 2] *\/*
                                 [# 0 <<<<
                                  --( v( 4),
                                  replacenth( v( 10), !! (varx), !! (valuex))
                                  )---> (# 5 ++++
                                         nth( find( !! (valuex), v( 0)), # 2))] **
                                 [nth( find( !! (valuex), v( 0)), # 3) ====
                                  # 1])))) *\/*
                     AbsAll range( # 0, # 4)
                       ([--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 9 ++++ v( 0)) ==== 
                         # 0] *\/* [nth( v( 5), v( 0)) ==== # 0]))))) **
             AbsEmpty ** AbsEmpty) **
            ([# 0 <<<< v( 7)] *\/* [v( 6) ==== # 0])) ** 
           [!! (valuex)]) ** [v( 3) ==== # 0]) ** 
         [!! (backtrack) ==== # 0]) ** [!! (stack) ==== !! (ssss)]) **
       [!! (have_var) ==== # 1]) ** AbsEmpty) **
     (ARRAY( !! (assignments), # 4, v( 4)) **
      [nth( find( !! (assignments_to_do_head), v( 2)), # 1) ==== # 0] **
      [!! (assignments_to_do_head) inTree v( 2)] **
      AbsAll TreeRecords( v( 2))
        ([--( v( 3), v( 0) )---> # 1 ==== # 0] **
         [nth( v( 3), v( 0)) ==== v( 0)] *\/*
         [--( v( 3), v( 0) )---> # 1 inTree v( 0)] **
         [--( v( 3), --( v( 3), v( 0) )---> # 1 )---> # 0 ==== v( 0)]) **
      AbsAll TreeRecords( v( 8))
        (AbsAll TreeRecords( nth( find( v( 9), v( 0)), # 2))
           ([~~
             nth( find( v( 10), v( 1)), # 2) ====
             nth( find( nth( find( v( 10), v( 1)), # 2), v( 0)), # 2)])) **
      AbsAll TreeRecords( v( 8))
        ([nth( find( v( 9), v( 0)), # 3) ==== # 1] *\/*
         [nth( find( v( 9), v( 0)), # 3) ==== # 2]) **
      AbsAll TreeRecords( v( 8)) ([nth( find( v( 9), v( 0)), # 2) <<<< # 4]) **
      ARRAY( !! (watches), # 4, v( 5)) **
      TREE( !! (stack), v( 8), # 4, # 0 :: nil) **
      TREE( !! (assignments_to_do_head), v( 2), # 4, # 0 :: nil) **
      TREE( !! (clauses), v( 0), # 21, # 0 :: nil) ** AbsEmpty) **
     build_equivs
       ((!! (have_var) :: # 1 :: nil)
        :: (!! (varx) :: v( 9) :: nil)
           :: (v( 10) :: v( 0) :: !! (valuex) :: nil)
              :: (nth( v( 8), # 0) :: !! (stack) :: !! (ssss) :: nil)
                 :: (nth( v( 4), !! (varx))
                     :: nth( find( !! (assignments_to_do_head), v( 2)), # 1)
                        :: v( 3) :: !! (backtrack) :: # 0 :: nil) :: nil))
    bbb (eee, hhh) ->
  realizeState
    (AbsAll range( # 0, # 4)
       ([nth( v( 5), v( 0)) ==== # 0] *\/*
        AbsExists TreeRecords( v( 9))
          ([nth( find( v( 10), v( 0)), # 2) ==== v( 1)] **
           [nth( find( v( 10), v( 0)), # 3) ==== nth( v( 6), v( 1))]))) bbb
    (eee, empty_heap).
Proof.
    admit.
Admitted.

Transparent nth.

Theorem mergeFinalImplication1: forall s,
realizeState
        (AbsExistsT
           (AbsExistsT
              (AbsExistsT
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (AbsExistsT
                                (AbsExistsT
                                   (AbsExistsT
                                      (AbsExistsT
                                         (AbsExistsT
                                            (TREE( 
                                             !! (clauses), 
                                             v( 0), 
                                             # 21, 
                                             # 0 :: nil) **
                                             TREE( 
                                             !! (assignments_to_do_head),
                                             v( 2), 
                                             # 4, 
                                             # 0 :: nil) **
                                             TREE( 
                                             !! (stack), 
                                             v( 8), 
                                             # 4, 
                                             # 0 :: nil) **
                                             ARRAY( !! (watches), # 4, v( 5)) **
                                             AbsAll 
                                               TreeRecords( v( 8))
                                               ([nth( 
                                                 find( v( 9), v( 0)), 
                                                 # 2) <<<< 
                                                 # 4]) **
                                             AbsAll 
                                               TreeRecords( v( 8))
                                               ([nth( 
                                                 find( v( 9), v( 0)), 
                                                 # 3) ==== 
                                                 # 1] *\/*
                                                [nth( 
                                                 find( v( 9), v( 0)), 
                                                 # 3) ==== 
                                                 # 2]) **
                                             AbsAll 
                                               TreeRecords( v( 8))
                                               (AbsAll
                                                 TreeRecords( 
                                                 nth( 
                                                 find( v( 9), v( 0)), 
                                                 # 2))
                                                 ([
                                                 ~~
                                                 nth( 
                                                 find( v( 10), v( 1)), 
                                                 # 2) ====
                                                 nth( 
                                                 find( 
                                                 nth( 
                                                 find( v( 10), v( 1)), 
                                                 # 2), 
                                                 v( 0)), 
                                                 # 2)])) **
                                             AbsAll 
                                               TreeRecords( v( 2))
                                               ([--( v( 3), v( 0) )---> # 1 ====
                                                 # 0] **
                                                [nth( v( 3), v( 0)) ====
                                                 v( 0)] *\/*
                                                [--( v( 3), v( 0) )---> # 1
                                                 inTree 
                                                 v( 0)] **
                                                [--( 
                                                 v( 3),
                                                 --( v( 3), v( 0) )---> # 1
                                                 )---> 
                                                 # 0 ==== 
                                                 v( 0)]) **
                                             [!! (assignments_to_do_head)
                                              inTree 
                                              v( 2)] **
                                             [nth( 
                                              find( 
                                              !! (assignments_to_do_head),
                                              v( 2)), 
                                              # 1) ==== 
                                              # 0] **
                                             ARRAY( 
                                             !! (assignments), 
                                             # 4, 
                                             v( 4)) **
                                             AbsAll 
                                               TreeRecords( v( 8))
                                               ([nth( 
                                                 v( 5),
                                                 nth( 
                                                 find( v( 9), v( 0)), 
                                                 # 2)) ====
                                                 nth( 
                                                 find( v( 9), v( 0)), 
                                                 # 3)]) **
                                             AbsAll 
                                               range( # 0, # 4)
                                               ([nth( v( 5), v( 0)) ==== # 0] *\/*
                                                AbsExists 
                                                 TreeRecords( v( 9))
                                                 ([
                                                 nth( 
                                                 find( v( 10), v( 0)), 
                                                 # 2) ==== 
                                                 v( 1)] **
                                                 [
                                                 nth( 
                                                 find( v( 10), v( 0)), 
                                                 # 3) ==== 
                                                 nth( v( 6), v( 1))])) **
                                             AbsEach 
                                               range( # 0, # 4)
                                               (AbsExistsT
                                                 (Path( 
                                                 nth( v( 10), v( 6)), 
                                                 v( 0), 
                                                 v( 7), 
                                                 # 21,
                                                 # 13 ++++ v( 6) :: nil) **
                                                 AbsAll 
                                                 TreeRecords( v( 7))
                                                 ([
                                                 --( 
                                                 v( 8), 
                                                 v( 0)
                                                 )---> 
                                                 (# 17 ++++ v( 3)) ==== 
                                                 # 0] **
                                                 [
                                                 nth( v( 8), v( 0)) ====
                                                 v( 0)] *\/*
                                                 [
                                                 --( 
                                                 v( 8), 
                                                 v( 0)
                                                 )---> 
                                                 (# 17 ++++ v( 3))
                                                 inTree 
                                                 v( 0)] **
                                                 [
                                                 --( 
                                                 v( 8),
                                                 --( 
                                                 v( 8), 
                                                 v( 0)
                                                 )---> 
                                                 (# 17 ++++ v( 3))
                                                 )---> 
                                                 (# 13 ++++ v( 3)) ==== 
                                                 v( 0)]) **
                                                 AbsAll 
                                                 TreeRecords( v( 0))
                                                 (AbsExists 
                                                 range( # 0, # 4)
                                                 ([
                                                 --( 
                                                 v( 1), 
                                                 v( 12)
                                                 )---> 
                                                 (# 1 ++++ v( 0))] **
                                                 ([
                                                 nth( v( 4), v( 0)) ==== 
                                                 # 2] *\/*
                                                 [
                                                 nth( v( 4), v( 0)) ==== # 0]) *\/*
                                                 [
                                                 --( 
                                                 v( 1), 
                                                 v( 12)
                                                 )---> 
                                                 (# 5 ++++ v( 2))] **
                                                 ([
                                                 nth( v( 4), v( 0)) ==== 
                                                 # 1] *\/*
                                                 [
                                                 nth( v( 4), v( 0)) ==== # 0]))) **
                                                 AbsAll 
                                                 range( # 0, # 4)
                                                 (([
                                                 --( 
                                                 v( 0), 
                                                 v( 1) )---> 
                                                 (# 9 ++++ v( 0)) ==== 
                                                 # 0] *\/*
                                                 [
                                                 --( 
                                                 v( 0), 
                                                 v( 1) )---> 
                                                 (# 1 ++++ v( 0))]) *\/*
                                                 [
                                                 --( 
                                                 v( 0), 
                                                 v( 1) )---> 
                                                 (# 5 ++++ v( 0))]) **
                                                 AbsAll 
                                                 range( # 0, # 4)
                                                 ([
                                                 # 0 <<<<
                                                 --( 
                                                 v( 1), 
                                                 v( 7) )---> 
                                                 (# 9 ++++ v( 0))] **
                                                 ([
                                                 # 0 <<<<
                                                 --( 
                                                 v( 1), 
                                                 v( 7)
                                                 )---> 
                                                 (# 17 ++++ v( 0))] *\/*
                                                 [
                                                 nth( v( 0), v( 2)) ====
                                                 v( 1)]) *\/*
                                                 ([
                                                 --( 
                                                 v( 1), 
                                                 v( 7) )---> 
                                                 (# 9 ++++ v( 0)) ==== 
                                                 # 0] **
                                                 [
                                                 --( 
                                                 v( 1), 
                                                 v( 7)
                                                 )---> 
                                                 (# 17 ++++ v( 0)) ==== 
                                                 # 0]) **
                                                 [
                                                 ~~
                                                 nth( v( 5), v( 0)) ====
                                                 v( 7)]) **
                                                 SUM( 
                                                 range( # 0, # 4),
                                                 # 0 <<<<
                                                 --( 
                                                 v( 0), 
                                                 v( 6) )---> 
                                                 (# 9 ++++ v( 0)), 
                                                 # 2) **
                                                 (SUM( 
                                                 range( # 0, # 4),
                                                 (--( 
                                                 v( 6), 
                                                 v( 4) )---> 
                                                 (# 1 ++++ v( 0)) \\//
                                                 --( 
                                                 v( 6), 
                                                 v( 4) )---> 
                                                 (# 5 ++++ v( 0))) //\\
                                                 nth( v( 4), v( 0)) ==== # 0,
                                                 # 1) **
                                                 AbsAll 
                                                 range( # 0, # 4)
                                                 ([
                                                 # 0 <<<<
                                                 --( 
                                                 v( 1), 
                                                 v( 7) )---> 
                                                 (# 9 ++++ v( 0))] **
                                                 [
                                                 nth( v( 7), v( 0)) ==== # 0] *\/*
                                                 [
                                                 # 0 <<<< nth( v( 7), v( 0))] *\/*
                                                 [
                                                 --( 
                                                 v( 1), 
                                                 v( 7) )---> 
                                                 (# 1 ++++ v( 0)) ==== 
                                                 # 0] **
                                                 [
                                                 --( 
                                                 v( 1), 
                                                 v( 7) )---> 
                                                 (# 5 ++++ v( 0)) ==== 
                                                 # 0]) **
                                                 AbsAll 
                                                 range( # 0, # 4)
                                                 (AbsAll 
                                                 range( # 0, # 4)
                                                 ((((([
                                                 --( 
                                                 v( 2), 
                                                 v( 8) )---> 
                                                 (# 9 ++++ v( 0))] *\/*
                                                 [
                                                 --( 
                                                 v( 2), 
                                                 v( 8) )---> 
                                                 (# 1 ++++ v( 0)) ==== 
                                                 # 0] **
                                                 [
                                                 --( 
                                                 v( 2), 
                                                 v( 8) )---> 
                                                 (# 5 ++++ v( 0)) ==== 
                                                 # 0]) *\/*
                                                 [
                                                 ~~
                                                 --( 
                                                 v( 2), 
                                                 v( 8) )---> 
                                                 (# 9 ++++ v( 1))]) *\/*
                                                 [
                                                 nth( v( 6), v( 1)) ==== # 0]) *\/*
                                                 [v( 0) ==== v( 1)]) *\/*
                                                 AbsExists
                                                 TreeRecords( v( 4))
                                                 (AbsExists
                                                 TreeRecords( 
                                                 find( 
                                                 v( 5), 
                                                 v( 0)))
                                                 ([
                                                 nth( 
                                                 find( v( 6), v( 1)), 
                                                 # 2) ==== 
                                                 v( 3)] **
                                                 [
                                                 nth( 
                                                 find( v( 6), v( 0)), 
                                                 # 2) ==== 
                                                 v( 1)])))) *\/*
                                                 AbsExists 
                                                 range( # 0, # 4)
                                                 (([
                                                 --( 
                                                 v( 1), 
                                                 v( 7) )---> 
                                                 (# 1 ++++ v( 0))] **
                                                 [
                                                 nth( v( 5), v( 0)) ==== # 2] *\/*
                                                 [
                                                 --( 
                                                 v( 1), 
                                                 v( 7) )---> 
                                                 (# 5 ++++ v( 0))] **
                                                 [
                                                 nth( v( 1), v( 7)) ==== # 1]) **
                                                 AbsAll 
                                                 range( # 0, # 4)
                                                 ([
                                                 # 0 ==== 
                                                 nth( v( 6), v( 0))] *\/*
                                                 [
                                                 --( 
                                                 v( 2), 
                                                 v( 8) )---> 
                                                 (# 9 ++++ v( 0)) ==== 
                                                 # 0] **
                                                 [
                                                 # 0 <<<< nth( v( 6), v( 0))] *\/*
                                                 AbsExists
                                                 TreeRecords( v( 4))
                                                 (AbsExists
                                                 TreeRecords( 
                                                 find( 
                                                 v( 1), 
                                                 v( 1)))
                                                 ([
                                                 nth( 
                                                 find( v( 6), v( 1)), 
                                                 # 2) ==== 
                                                 v( 2)] **
                                                 ([
                                                 # 0 <<<<
                                                 --( 
                                                 v( 4), 
                                                 v( 10)
                                                 )---> 
                                                 (# 1 ++++
                                                 nth( 
                                                 find( v( 6), v( 0)), 
                                                 # 2))] **
                                                 [
                                                 nth( 
                                                 find( v( 6), v( 0)), 
                                                 # 3) ==== 
                                                 # 2] *\/*
                                                 [
                                                 # 0 <<<<
                                                 --( 
                                                 v( 4), 
                                                 v( 10)
                                                 )---> 
                                                 (# 5 ++++
                                                 nth( 
                                                 find( v( 6), v( 0)), 
                                                 # 2))] **
                                                 [
                                                 nth( 
                                                 find( v( 6), v( 0)), 
                                                 # 3) ==== 
                                                 # 1]))))) *\/*
                                                 AbsAll 
                                                 range( # 0, # 4)
                                                 ([
                                                 --( 
                                                 v( 1), 
                                                 v( 7) )---> 
                                                 (# 9 ++++ v( 0)) ==== 
                                                 # 0] *\/*
                                                 [
                                                 nth( v( 5), v( 0)) ==== # 0])))) **
                                             AbsEmpty))))))))))))) nil s ->
realizeState
    (AbsExistsT
       (AbsExistsT
          (AbsExistsT
             (AbsExistsT
                (AbsExistsT
                   (((TREE( !! (clauses), v( 0), # 21, # 0 :: nil) **
                      TREE( !! (assignments_to_do_head), 
                      v( 1), # 4, # 0 :: nil) **
                      TREE( !! (stack), v( 2), # 4, # 0 :: nil) **
                      ARRAY( !! (assignments), # 4, v( 3)) **
                      ARRAY( !! (watches), # 4, v( 4))) **
                     (AbsAll TreeRecords( v( 2))
                        ([nth( find( v( 3), v( 0)), # 2) <<<< # 4] **
                         ([nth( find( v( 3), v( 0)), # 3) ==== # 1] *\/*
                          [nth( find( v( 3), v( 0)), # 3) ==== # 2]) **
                         [nth( v( 4), nth( find( v( 3), v( 0)), # 2)) ====
                          nth( find( v( 3), v( 0)), # 3)] **
                         AbsAll TreeRecords( nth( find( v( 3), v( 0)), # 2))
                           ([~~
                             nth( find( v( 4), v( 1)), # 2) ====
                             nth( find( nth( find( v( 4), v( 1)), # 2),
                                  v( 0)), # 2)])) **
                      AbsAll range( # 0, # 4)
                        ([nth( v( 4), v( 0)) ==== # 0] *\/*
                         AbsExists TreeRecords( v( 3))
                           ([nth( find( v( 4), v( 0)), # 2) ==== v( 1) //\\
                             nth( find( v( 4), v( 0)), # 3) ====
                             nth( v( 5), v( 1))]))) **
                     AbsAll TreeRecords( v( 1))
                       ([--( v( 2), v( 0) )---> # 1 ==== # 0 //\\
                         nth( v( 2), v( 0)) ==== v( 0) \\//
                         --( v( 2), v( 0) )---> # 1 inTree v( 0) //\\
                         --( v( 2), --( v( 2), v( 0) )---> # 1 )---> # 0 ====
                         v( 0)]) **
                     AbsEach range( # 0, # 4)
                       (AbsExistsT
                          (Path( nth( v( 4), v( 5)), 
                           v( 0), v( 6), # 21, # 13 ++++ v( 5) :: nil) **
                           AbsAll TreeRecords( v( 6))
                             ([--( v( 7), v( 0) )---> (# 17 ++++ v( 3)) ====
                               # 0 //\\ nth( v( 7), v( 0)) ==== v( 0) \\//
                               --( v( 7), v( 0) )---> (# 17 ++++ v( 3))
                               inTree v( 0) //\\
                               --( v( 7),
                               --( v( 7), v( 0) )---> (# 17 ++++ v( 3))
                               )---> (# 13 ++++ v( 3)) ==== 
                               v( 0)]) **
                           AbsAll TreeRecords( v( 0))
                             (AbsExists range( # 0, # 4)
                                ([--( v( 1), v( 6) )---> (# 1 ++++ v( 0)) //\\
                                  (nth( v( 4), v( 0)) ==== # 2 \\//
                                   nth( v( 4), v( 0)) ==== # 0) \\//
                                  --( v( 1), v( 6) )---> (# 5 ++++ v( 2)) //\\
                                  (nth( v( 4), v( 0)) ==== # 1 \\//
                                   nth( v( 4), v( 0)) ==== # 0)])) **
                           AbsAll range( # 0, # 4)
                             ([(--( v( 0), v( 1) )---> (# 9 ++++ v( 0)) ====
                                # 0 \\//
                                --( v( 0), v( 1) )---> (# 1 ++++ v( 0))) \\//
                               --( v( 0), v( 1) )---> (# 5 ++++ v( 0))]) **
                           AbsAll range( # 0, # 4)
                             ([~~
                               --( v( 1), v( 6) )---> (# 9 ++++ v( 0)) ====
                               # 0 //\\
                               (~~
                                --( v( 1), v( 6) )---> (# 17 ++++ v( 0)) ====
                                # 0 \\// nth( v( 0), v( 2)) ==== v( 1)) \\//
                               (--( v( 1), v( 6) )---> (# 9 ++++ v( 0)) ====
                                # 0 //\\
                                --( v( 1), v( 6) )---> (# 17 ++++ v( 0)) ====
                                # 0) //\\ ~~ nth( v( 4), v( 0)) ==== v( 6)]) **
                           SUM( range( # 0, # 4),
                           ite( --( v( 0), v( 5) )---> (# 9 ++++ v( 0)), 
                           # 1, # 0), # 2) **
                           (SUM( range( # 0, # 4),
                            (--( v( 5), v( 3) )---> (# 1 ++++ v( 0)) \\//
                             --( v( 5), v( 3) )---> (# 5 ++++ v( 0))) //\\
                            (ite( nth( v( 3), v( 0)) ==== # 0, # 1, # 0)),
                            # 1) **
                            AbsAll range( # 0, # 4)
                              ([# 0 <<<<
                                --( v( 1), v( 6) )---> (# 9 ++++ v( 0)) //\\
                                nth( v( 6), v( 0)) ==== # 0 \\//
                                (# 0 <<<< nth( v( 6), v( 0)) \\//
                                 --( v( 1), v( 6) )---> (# 1 ++++ v( 0)) ====
                                 # 0 //\\
                                 --( v( 1), v( 6) )---> (# 5 ++++ v( 0)) ====
                                 # 0)]) **
                            AbsAll range( # 0, # 4)
                              (AbsAll range( # 0, # 4)
                                 ([((((--( v( 2), 
                                       v( 7) )---> 
                                       (# 9 ++++ v( 0)) \\//
                                       --( v( 2), 
                                       v( 7) )---> 
                                       (# 1 ++++ v( 0)) ==== 
                                       # 0 //\\
                                       --( v( 2), 
                                       v( 7) )---> 
                                       (# 5 ++++ v( 0)) ==== 
                                       # 0) \\//
                                      ~~
                                      --( v( 2), v( 7) )---> (# 9 ++++ v( 1))) \\//
                                     nth( v( 5), v( 1)) ==== # 0) \\//
                                    nth( v( 5), v( 1)) ==== # 0) \\//
                                   v( 0) ==== v( 1)] *\/*
                                  AbsExists TreeRecords( v( 4))
                                    ([nth( find( v( 5), v( 0)), # 2) ====
                                      v( 2)] **
                                     AbsExists
                                       TreeRecords( find( v( 5), v( 0)))
                                       ([nth( find( v( 6), v( 0)), # 2) ====
                                         v( 1)])))) *\/*
                            AbsExists range( # 0, # 4)
                              ([--( v( 1), v( 6) )---> (# 1 ++++ v( 0)) //\\
                                nth( v( 4), v( 0)) ==== # 2 \\//
                                --( v( 1), v( 6) )---> (# 5 ++++ v( 0)) //\\
                                nth( v( 1), v( 6)) ==== # 1]) **
                            AbsAll range( # 0, # 4)
                              ([# 0 ==== nth( v( 4), v( 0))] *\/*
                               [--( v( 1), v( 6) )---> (# 9 ++++ v( 0)) ====
                                # 0] ** [# 0 <<<< nth( v( 4), v( 0))] *\/*
                               AbsExists TreeRecords( v( 3))
                                 ([nth( find( v( 4), v( 0)), # 2) ==== v( 1)]) **
                               AbsExists TreeRecords( find( v( 0), v( 0)))
                                 ([# 0 <<<<
                                   --( v( 2), v( 7)
                                   )---> (# 1 ++++
                                          nth( find( v( 4), v( 0)), # 2)) //\\
                                   nth( find( v( 4), v( 0)), # 3) ==== # 2 \\//
                                   # 0 <<<<
                                   --( v( 2), v( 7)
                                   )---> (# 5 ++++
                                          nth( find( v( 4), v( 0)), # 2)) //\\
                                   nth( find( v( 4), v( 0)), # 3) ==== # 1])) *\/*
                            AbsAll range( # 0, # 4)
                              ([--( v( 1), v( 6) )---> (# 9 ++++ v( 0)) ====
                                # 0 \\// nth( v( 4), v( 0)) ==== # 0]))))) **
                    [!! (assignments_to_do_head) inTree v( 1)] **
                    [nth( find( !! (assignments_to_do_head), v( 1)), # 1) ====
                     # 0])))))) nil s.
Proof.
    intros.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity. propagateExists. propagateExists.
    propagateExists.
    simplifyHyp H. simplifyHyp H. simplifyHyp H. simplifyHyp H.
    simplifyHyp H. simplifyHyp H. simplifyHyp H. simplifyHyp H. propagateExistsHyp H.

 eapply stateImplication.
        apply H. compute. reflexivity. compute. reflexivity.
        prove_implication.
        compute. reflexivity. compute. reflexivity.
        intros. simpl. eapply emptyRealizeState. simpl. reflexivity. 
Admitted.

Theorem mergePredicateTheorem3 :
forall (eee : env) (hhh : heap) (bbb : list Value),
  length bbb = 12 ->
  realizeState
    (([nth( v( 4), !! (varx)) ==== # 0] **
      ((([!! (ssss) ==== nth( v( 8), # 0)] **
         [!! (valuex) ==== v( 10)] **
         [!! (varx) ==== v( 9)] **
         ((((((AbsEmpty ** AbsEmpty ** AbsEmpty ** AbsEmpty) **
              ((([!! (varx) <<<< # 4] ** AbsEmpty) **
                (([!! (valuex) ==== # 1] *\/* [!! (valuex) ==== # 2]) **
                 AbsEmpty) **
                ([v( 0) ==== !! (valuex)] **
                 AbsAll TreeRecords( v( 8))
                   ([nth( replacenth( v( 5), !! (varx), !! (valuex)),
                     nth( find( v( 9), v( 0)), # 2)) ====
                     nth( find( v( 9), v( 0)), # 3)])) ** AbsEmpty) **
               AbsAll range( # 0, # 4)
                 ([nth( v( 5), v( 0)) ==== # 0] *\/*
                  [!! (varx) ==== v( 0)] *\/*
                  AbsExists TreeRecords( v( 9))
                    ([nth( find( v( 10), v( 0)), # 2) ==== v( 1)] **
                     [nth( find( v( 10), v( 0)), # 3) ==== nth( v( 6), v( 1))]))) **
              AbsEmpty **
              AbsEach range( # 0, # 4)
                (AbsExistsT
                   (Path( nth( list( v( 9)
                                     :: v( 10)
                                        :: !! (varx)
                                           :: !! (valuex) :: v( 13) :: nil),
                          replacenth( v( 6), !! (varx), !! (valuex))), 
                    v( 0), v( 7), # 21,
                    # 13 ++++ replacenth( v( 6), !! (varx), !! (valuex))
                    :: nil) **
                    AbsAll TreeRecords( v( 7))
                      ([--( v( 8), v( 0) )---> (# 17 ++++ !! (valuex)) ====
                        # 0] ** [nth( v( 8), v( 0)) ==== v( 0)] *\/*
                       [--( v( 8), v( 0) )---> (# 17 ++++ !! (valuex))
                        inTree v( 0)] **
                       [--( v( 8),
                        --( v( 8), v( 0) )---> (# 17 ++++ !! (valuex))
                        )---> (# 13 ++++ !! (valuex)) ==== 
                        v( 0)]) **
                    AbsAll TreeRecords( v( 0))
                      (AbsExists range( # 0, # 4)
                         ([--( v( 1),
                           list( v( 11)
                                 :: v( 12)
                                    :: !! (varx)
                                       :: !! (valuex) :: v( 15) :: nil)
                           )---> (# 1 ++++ v( 0))] **
                          ([nth( !! (valuex), v( 0)) ==== # 2] *\/*
                           [nth( !! (valuex), v( 0)) ==== # 0]) *\/*
                          [--( v( 1),
                           list( v( 11)
                                 :: v( 12)
                                    :: !! (varx)
                                       :: !! (valuex) :: v( 15) :: nil)
                           )---> (# 5 ++++ v( 2))] **
                          ([nth( !! (valuex), v( 0)) ==== # 1] *\/*
                           [nth( !! (valuex), v( 0)) ==== # 0]))) **
                    AbsAll range( # 0, # 4)
                      (([--( v( 0), v( 1) )---> (# 9 ++++ v( 0)) ==== # 0] *\/*
                        [--( v( 0), v( 1) )---> (# 1 ++++ v( 0))]) *\/*
                       [--( v( 0), v( 1) )---> (# 5 ++++ v( 0))]) **
                    AbsAll range( # 0, # 4)
                      ([# 0 <<<<
                        --( v( 1), replacenth( v( 7), !! (varx), !! (valuex))
                        )---> (# 9 ++++ v( 0))] **
                       ([# 0 <<<<
                         --( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 17 ++++ v( 0))] *\/*
                        [nth( v( 0), v( 2)) ==== v( 1)]) *\/*
                       ([--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 9 ++++ v( 0)) ==== 
                         # 0] **
                        [--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 17 ++++ v( 0)) ==== 
                         # 0]) **
                       [~~
                        nth( v( 5), v( 0)) ====
                        replacenth( v( 7), !! (varx), !! (valuex))]) **
                    SUM( range( # 0, # 4),
                    # 0 <<<<
                    --( v( 0), replacenth( v( 6), !! (varx), !! (valuex))
                    )---> (# 9 ++++ v( 0)), # 2) **
                    (SUM( range( # 0, # 4),
                     (--( replacenth( v( 6), !! (varx), !! (valuex)), 
                      v( 4) )---> (# 1 ++++ v( 0)) \\//
                      --( replacenth( v( 6), !! (varx), !! (valuex)), 
                      v( 4) )---> (# 5 ++++ v( 0))) //\\
                     nth( v( 4), v( 0)) ==== # 0, 
                     # 1) **
                     AbsAll range( # 0, # 4)
                       ([# 0 <<<<
                         --( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 9 ++++ v( 0))] **
                        [nth( replacenth( v( 7), !! (varx), !! (valuex)),
                         v( 0)) ==== # 0] *\/*
                        [# 0 <<<<
                         nth( replacenth( v( 7), !! (varx), !! (valuex)),
                         v( 0))] *\/*
                        [--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 1 ++++ v( 0)) ==== 
                         # 0] **
                        [--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 5 ++++ v( 0)) ==== 
                         # 0]) **
                     AbsAll range( # 0, # 4)
                       (AbsAll range( # 0, # 4)
                          ((((([--( v( 2),
                                replacenth( v( 8), !! (varx), !! (valuex))
                                )---> (# 9 ++++ v( 0))] *\/*
                               [--( v( 2),
                                replacenth( v( 8), !! (varx), !! (valuex))
                                )---> (# 1 ++++ v( 0)) ==== 
                                # 0] **
                               [--( v( 2),
                                replacenth( v( 8), !! (varx), !! (valuex))
                                )---> (# 5 ++++ v( 0)) ==== 
                                # 0]) *\/*
                              [~~
                               --( v( 2),
                               replacenth( v( 8), !! (varx), !! (valuex))
                               )---> (# 9 ++++ v( 1))]) *\/*
                             [nth( v( 6), v( 1)) ==== # 0]) *\/*
                            [v( 0) ==== v( 1)]) *\/*
                           AbsExists (AbsConstVal (ListValue nil))
                             (AbsExists
                                TreeRecords( find( !! (valuex), v( 0)))
                                ([nth( find( !! (valuex), v( 1)), # 2) ====
                                  v( 3)] **
                                 [nth( find( !! (valuex), v( 0)), # 2) ====
                                  v( 1)])))) *\/*
                     AbsExists range( # 0, # 4)
                       (([--( v( 1),
                          replacenth( v( 7), !! (varx), !! (valuex))
                          )---> (# 1 ++++ v( 0))] **
                         [nth( v( 5), v( 0)) ==== # 2] *\/*
                         [--( v( 1),
                          replacenth( v( 7), !! (varx), !! (valuex))
                          )---> (# 5 ++++ v( 0))] **
                         [nth( v( 1),
                          replacenth( v( 7), !! (varx), !! (valuex))) ====
                          # 1]) **
                        AbsAll range( # 0, # 4)
                          ([# 0 ==== nth( v( 6), v( 0))] *\/*
                           [--( v( 2),
                            replacenth( v( 8), !! (varx), !! (valuex))
                            )---> (# 9 ++++ v( 0)) ==== 
                            # 0] ** [# 0 <<<< nth( v( 6), v( 0))] *\/*
                           AbsExists (AbsConstVal (ListValue nil))
                             ([nth( find( !! (valuex), v( 0)), # 2) ====
                               v( 1)] **
                              AbsExists TreeRecords( find( v( 1), v( 1)))
                                ([# 0 <<<<
                                  --( v( 4),
                                  replacenth( v( 10), !! (varx), !! (valuex))
                                  )---> (# 1 ++++
                                         nth( find( !! (valuex), v( 0)), # 2))] **
                                 [nth( find( !! (valuex), v( 0)), # 3) ====
                                  # 2] *\/*
                                 [# 0 <<<<
                                  --( v( 4),
                                  replacenth( v( 10), !! (varx), !! (valuex))
                                  )---> (# 5 ++++
                                         nth( find( !! (valuex), v( 0)), # 2))] **
                                 [nth( find( !! (valuex), v( 0)), # 3) ====
                                  # 1])))) *\/*
                     AbsAll range( # 0, # 4)
                       ([--( v( 1),
                         replacenth( v( 7), !! (varx), !! (valuex))
                         )---> (# 9 ++++ v( 0)) ==== 
                         # 0] *\/* [nth( v( 5), v( 0)) ==== # 0]))))) **
             AbsEmpty ** AbsEmpty) **
            ([# 0 <<<< v( 7)] *\/* [v( 6) ==== # 0])) ** 
           [!! (valuex)]) ** [v( 3) ==== # 0]) ** 
         [!! (backtrack) ==== # 0]) ** [!! (stack) ==== !! (ssss)]) **
       [!! (have_var) ==== # 1]) ** AbsEmpty) **
     (ARRAY( !! (assignments), # 4, v( 4)) **
      [nth( find( !! (assignments_to_do_head), v( 2)), # 1) ==== # 0] **
      [!! (assignments_to_do_head) inTree v( 2)] **
      AbsAll TreeRecords( v( 2))
        ([--( v( 3), v( 0) )---> # 1 ==== # 0] **
         [nth( v( 3), v( 0)) ==== v( 0)] *\/*
         [--( v( 3), v( 0) )---> # 1 inTree v( 0)] **
         [--( v( 3), --( v( 3), v( 0) )---> # 1 )---> # 0 ==== v( 0)]) **
      AbsAll TreeRecords( v( 8))
        (AbsAll TreeRecords( nth( find( v( 9), v( 0)), # 2))
           ([~~
             nth( find( v( 10), v( 1)), # 2) ====
             nth( find( nth( find( v( 10), v( 1)), # 2), v( 0)), # 2)])) **
      AbsAll TreeRecords( v( 8))
        ([nth( find( v( 9), v( 0)), # 3) ==== # 1] *\/*
         [nth( find( v( 9), v( 0)), # 3) ==== # 2]) **
      AbsAll TreeRecords( v( 8)) ([nth( find( v( 9), v( 0)), # 2) <<<< # 4]) **
      ARRAY( !! (watches), # 4, v( 5)) **
      TREE( !! (stack), v( 8), # 4, # 0 :: nil) **
      TREE( !! (assignments_to_do_head), v( 2), # 4, # 0 :: nil) **
      TREE( !! (clauses), v( 0), # 21, # 0 :: nil) ** AbsEmpty) **
     build_equivs
       ((!! (have_var) :: # 1 :: nil)
        :: (!! (varx) :: v( 9) :: nil)
           :: (v( 10) :: v( 0) :: !! (valuex) :: nil)
              :: (nth( v( 8), # 0) :: !! (stack) :: !! (ssss) :: nil)
                 :: (nth( v( 4), !! (varx))
                     :: nth( find( !! (assignments_to_do_head), v( 2)), # 1)
                        :: v( 3) :: !! (backtrack) :: # 0 :: nil) :: nil))
    bbb (eee, hhh) ->
  realizeState
    (AbsEach range( # 0, # 4)
       (AbsExistsT
          (Path( nth( v( 10), v( 6)), v( 0), v( 7), 
           # 21, # 13 ++++ v( 6) :: nil) **
           AbsAll TreeRecords( v( 7))
             ([--( v( 8), v( 0) )---> (# 17 ++++ v( 3)) ==== # 0] **
              [nth( v( 8), v( 0)) ==== v( 0)] *\/*
              [--( v( 8), v( 0) )---> (# 17 ++++ v( 3)) inTree v( 0)] **
              [--( v( 8), --( v( 8), v( 0) )---> (# 17 ++++ v( 3))
               )---> (# 13 ++++ v( 3)) ==== v( 0)]) **
           AbsAll TreeRecords( v( 0))
             (AbsExists range( # 0, # 4)
                ([--( v( 1), v( 12) )---> (# 1 ++++ v( 0))] **
                 ([nth( v( 4), v( 0)) ==== # 2] *\/*
                  [nth( v( 4), v( 0)) ==== # 0]) *\/*
                 [--( v( 1), v( 12) )---> (# 5 ++++ v( 2))] **
                 ([nth( v( 4), v( 0)) ==== # 1] *\/*
                  [nth( v( 4), v( 0)) ==== # 0]))) **
           AbsAll range( # 0, # 4)
             (([--( v( 0), v( 1) )---> (# 9 ++++ v( 0)) ==== # 0] *\/*
               [--( v( 0), v( 1) )---> (# 1 ++++ v( 0))]) *\/*
              [--( v( 0), v( 1) )---> (# 5 ++++ v( 0))]) **
           AbsAll range( # 0, # 4)
             ([# 0 <<<< --( v( 1), v( 7) )---> (# 9 ++++ v( 0))] **
              ([# 0 <<<< --( v( 1), v( 7) )---> (# 17 ++++ v( 0))] *\/*
               [nth( v( 0), v( 2)) ==== v( 1)]) *\/*
              ([--( v( 1), v( 7) )---> (# 9 ++++ v( 0)) ==== # 0] **
               [--( v( 1), v( 7) )---> (# 17 ++++ v( 0)) ==== # 0]) **
              [~~ nth( v( 5), v( 0)) ==== v( 7)]) **
           SUM( range( # 0, # 4),
           # 0 <<<< --( v( 0), v( 6) )---> (# 9 ++++ v( 0)), 
           # 2) **
           (SUM( range( # 0, # 4),
            (--( v( 6), v( 4) )---> (# 1 ++++ v( 0)) \\//
             --( v( 6), v( 4) )---> (# 5 ++++ v( 0))) //\\
            nth( v( 4), v( 0)) ==== # 0, # 1) **
            AbsAll range( # 0, # 4)
              ([# 0 <<<< --( v( 1), v( 7) )---> (# 9 ++++ v( 0))] **
               [nth( v( 7), v( 0)) ==== # 0] *\/*
               [# 0 <<<< nth( v( 7), v( 0))] *\/*
               [--( v( 1), v( 7) )---> (# 1 ++++ v( 0)) ==== # 0] **
               [--( v( 1), v( 7) )---> (# 5 ++++ v( 0)) ==== # 0]) **
            AbsAll range( # 0, # 4)
              (AbsAll range( # 0, # 4)
                 ((((([--( v( 2), v( 8) )---> (# 9 ++++ v( 0))] *\/*
                      [--( v( 2), v( 8) )---> (# 1 ++++ v( 0)) ==== # 0] **
                      [--( v( 2), v( 8) )---> (# 5 ++++ v( 0)) ==== # 0]) *\/*
                     [~~ --( v( 2), v( 8) )---> (# 9 ++++ v( 1))]) *\/*
                    [nth( v( 6), v( 1)) ==== # 0]) *\/* 
                   [v( 0) ==== v( 1)]) *\/*
                  AbsExists TreeRecords( v( 4))
                    (AbsExists TreeRecords( find( v( 5), v( 0)))
                       ([nth( find( v( 6), v( 1)), # 2) ==== v( 3)] **
                        [nth( find( v( 6), v( 0)), # 2) ==== v( 1)])))) *\/*
            AbsExists range( # 0, # 4)
              (([--( v( 1), v( 7) )---> (# 1 ++++ v( 0))] **
                [nth( v( 5), v( 0)) ==== # 2] *\/*
                [--( v( 1), v( 7) )---> (# 5 ++++ v( 0))] **
                [nth( v( 1), v( 7)) ==== # 1]) **
               AbsAll range( # 0, # 4)
                 ([# 0 ==== nth( v( 6), v( 0))] *\/*
                  [--( v( 2), v( 8) )---> (# 9 ++++ v( 0)) ==== # 0] **
                  [# 0 <<<< nth( v( 6), v( 0))] *\/*
                  AbsExists TreeRecords( v( 4))
                    (AbsExists TreeRecords( find( v( 1), v( 1)))
                       ([nth( find( v( 6), v( 1)), # 2) ==== v( 2)] **
                        ([# 0 <<<<
                          --( v( 4), v( 10)
                          )---> (# 1 ++++ nth( find( v( 6), v( 0)), # 2))] **
                         [nth( find( v( 6), v( 0)), # 3) ==== # 2] *\/*
                         [# 0 <<<<
                          --( v( 4), v( 10)
                          )---> (# 5 ++++ nth( find( v( 6), v( 0)), # 2))] **
                         [nth( find( v( 6), v( 0)), # 3) ==== # 1]))))) *\/*
            AbsAll range( # 0, # 4)
              ([--( v( 1), v( 7) )---> (# 9 ++++ v( 0)) ==== # 0] *\/*
               [nth( v( 5), v( 0)) ==== # 0]))))) bbb 
    (eee, empty_heap).
Proof.
    admit.
Admitted.


Theorem mergeMergeTheorem2 :
mergeStates
    (AbsExistsT
       (AbsExistsT
          (AbsExistsT
             (AbsExistsT
                (AbsExistsT
                   (AbsExistsT
                      (AbsExistsT
                         (AbsExistsT
                            (AbsExistsT
                               (AbsExistsT
                                  (AbsExistsT
                                     ([nth( v( 2), !! (varx)) ==== # 0] **
                                      AbsExistsT
                                        (((([!! (ssss) ==== nth( v( 8), # 0)] **
                                            [!! (valuex) ==== v( 10)] **
                                            [!! (varx) ==== v( 9)] **
                                            ((((((TREE( 
                                                 !! (clauses), 
                                                 v( 0), 
                                                 # 21, 
                                                 # 0 :: nil) **
                                                 TREE( 
                                                 !! 
                                                 (assignments_to_do_head),
                                                 v( 2), 
                                                 # 4, 
                                                 # 0 :: nil) **
                                                 TREE( 
                                                 nth( v( 8), # 0), 
                                                 v( 8), 
                                                 # 4, 
                                                 # 0 :: nil) **
                                                 AbsEmpty **
                                                 ARRAY( 
                                                 !! (watches), 
                                                 # 4, 
                                                 v( 4))) **
                                                 ((([!! (varx) <<<< # 4] **
                                                 AbsAll 
                                                 TreeRecords( v( 8))
                                                 ([
                                                 nth( 
                                                 find( v( 9), v( 0)), 
                                                 # 2) <<<< 
                                                 # 4])) **
                                                 (([!! (valuex) ==== # 1] *\/*
                                                 [!! (valuex) ==== # 2]) **
                                                 AbsAll 
                                                 TreeRecords( v( 8))
                                                 ([
                                                 nth( 
                                                 find( v( 9), v( 0)), 
                                                 # 3) ==== 
                                                 # 1] *\/*
                                                 [
                                                 nth( 
                                                 find( v( 9), v( 0)), 
                                                 # 3) ==== 
                                                 # 2])) **
                                                 ([
                                                 nth( 
                                                 replacenth( 
                                                 v( 3), 
                                                 !! (varx), 
                                                 v( 0)), 
                                                 !! (varx)) ==== 
                                                 !! (valuex)] **
                                                 AbsAll 
                                                 TreeRecords( v( 8))
                                                 ([
                                                 nth( 
                                                 replacenth( 
                                                 v( 4), 
                                                 !! (varx), 
                                                 v( 1)),
                                                 nth( 
                                                 find( v( 9), v( 0)), 
                                                 # 2)) ====
                                                 nth( 
                                                 find( v( 9), v( 0)), 
                                                 # 3)])) **
                                                 AbsAll 
                                                 TreeRecords( v( 8))
                                                 ([
                                                 ~~
                                                 !! (varx) ====
                                                 nth( 
                                                 find( v( 9), v( 0)), 
                                                 # 2)]) **
                                                 AbsAll 
                                                 TreeRecords( v( 8))
                                                 (AbsAll
                                                 TreeRecords( 
                                                 nth( 
                                                 find( v( 9), v( 0)), 
                                                 # 1))
                                                 ([
                                                 ~~
                                                 nth( 
                                                 find( v( 10), v( 1)), 
                                                 # 2) ====
                                                 nth( 
                                                 find( 
                                                 nth( 
                                                 find( v( 10), v( 1)), 
                                                 # 1), 
                                                 v( 0)), 
                                                 # 2)]))) **
                                                 AbsAll 
                                                 range( # 0, # 4)
                                                 ([
                                                 nth( 
                                                 replacenth( 
                                                 v( 4), 
                                                 !! (varx), 
                                                 v( 1)), 
                                                 v( 0)) ==== 
                                                 # 0] *\/*
                                                 [!! (varx) ==== v( 0)] *\/*
                                                 AbsExists
                                                 TreeRecords( v( 9))
                                                 ([
                                                 nth( 
                                                 find( v( 10), v( 0)), 
                                                 # 2) ==== 
                                                 v( 1)] **
                                                 [
                                                 nth( 
                                                 find( v( 10), v( 0)), 
                                                 # 3) ====
                                                 nth( 
                                                 replacenth( 
                                                 v( 5), 
                                                 !! (varx), 
                                                 v( 2)), 
                                                 v( 1))]))) **
                                                 AbsAll 
                                                 TreeRecords( v( 2))
                                                 ([
                                                 --( v( 3), v( 0) )---> # 1 ====
                                                 # 0] **
                                                 [
                                                 nth( v( 3), v( 0)) ====
                                                 v( 0)] *\/*
                                                 [
                                                 --( v( 3), v( 0) )---> # 1
                                                 inTree 
                                                 v( 0)] **
                                                 [
                                                 --( 
                                                 v( 3),
                                                 --( v( 3), v( 0) )---> # 1
                                                 )---> 
                                                 # 0 ==== 
                                                 v( 0)]) **
                                                 AbsEach 
                                                 range( # 0, # 4)
                                                 (AbsExistsT
                                                 (Path( 
                                                 nth( 
                                                 list( 
                                                 v( 8)
                                                 :: 
                                                 v( 10)
                                                 :: 
                                                 !! (varx)
                                                 :: 
                                                 !! (valuex) :: 
                                                 v( 13) :: nil),
                                                 replacenth( 
                                                 v( 5), 
                                                 !! (varx), 
                                                 v( 2))), 
                                                 v( 0), 
                                                 v( 6), 
                                                 # 21,
                                                 # 13 ++++
                                                 replacenth( 
                                                 v( 5), 
                                                 !! (varx), 
                                                 v( 2)) :: nil) **
                                                 AbsAll 
                                                 TreeRecords( v( 6))
                                                 ([
                                                 --( 
                                                 v( 7), 
                                                 v( 0)
                                                 )---> 
                                                 (# 17 ++++ v( 3)) ==== 
                                                 # 0] **
                                                 [
                                                 nth( v( 7), v( 0)) ====
                                                 v( 0)] *\/*
                                                 [
                                                 --( 
                                                 v( 7), 
                                                 v( 0)
                                                 )---> 
                                                 (# 17 ++++ v( 3))
                                                 inTree 
                                                 v( 0)] **
                                                 [
                                                 --( 
                                                 v( 7),
                                                 --( 
                                                 v( 7), 
                                                 v( 0)
                                                 )---> 
                                                 (# 17 ++++ v( 3))
                                                 )---> 
                                                 (# 13 ++++ v( 3)) ==== 
                                                 v( 0)]) **
                                                 AbsAll 
                                                 TreeRecords( v( 0))
                                                 (AbsExists 
                                                 range( # 0, # 4)
                                                 ([
                                                 --( 
                                                 v( 1),
                                                 list( 
                                                 v( 10)
                                                 :: 
                                                 v( 12)
                                                 :: 
                                                 !! (varx)
                                                 :: 
                                                 !! (valuex) :: 
                                                 v( 15) :: nil)
                                                 )---> 
                                                 (# 1 ++++ v( 0))] **
                                                 ([
                                                 nth( v( 4), v( 0)) ==== 
                                                 # 2] *\/*
                                                 [
                                                 nth( v( 4), v( 0)) ==== # 0]) *\/*
                                                 [
                                                 --( 
                                                 v( 1),
                                                 list( 
                                                 v( 10)
                                                 :: 
                                                 v( 12)
                                                 :: 
                                                 !! (varx)
                                                 :: 
                                                 !! (valuex) :: 
                                                 v( 15) :: nil)
                                                 )---> 
                                                 (# 5 ++++ v( 2))] **
                                                 ([
                                                 nth( v( 4), v( 0)) ==== 
                                                 # 1] *\/*
                                                 [
                                                 nth( v( 4), v( 0)) ==== # 0]))) **
                                                 AbsAll 
                                                 range( # 0, # 4)
                                                 (([
                                                 --( 
                                                 v( 0), 
                                                 v( 1) )---> 
                                                 (# 9 ++++ v( 0)) ==== 
                                                 # 0] *\/*
                                                 [
                                                 --( 
                                                 v( 0), 
                                                 v( 1) )---> 
                                                 (# 1 ++++ v( 0))]) *\/*
                                                 [
                                                 --( 
                                                 v( 0), 
                                                 v( 1) )---> 
                                                 (# 5 ++++ v( 0))]) **
                                                 AbsAll 
                                                 range( # 0, # 4)
                                                 ([
                                                 # 0 <<<<
                                                 --( 
                                                 v( 1),
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3))
                                                 )---> 
                                                 (# 9 ++++ v( 0))] **
                                                 ([
                                                 # 0 <<<<
                                                 --( 
                                                 v( 1),
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3))
                                                 )---> 
                                                 (# 17 ++++ v( 0))] *\/*
                                                 [
                                                 nth( v( 0), v( 2)) ====
                                                 v( 1)]) *\/*
                                                 ([
                                                 --( 
                                                 v( 1),
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3))
                                                 )---> 
                                                 (# 9 ++++ v( 0)) ==== 
                                                 # 0] **
                                                 [
                                                 --( 
                                                 v( 1),
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3))
                                                 )---> 
                                                 (# 17 ++++ v( 0)) ==== 
                                                 # 0]) **
                                                 [
                                                 ~~
                                                 nth( v( 5), v( 0)) ====
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3))]) **
                                                 SUM( 
                                                 range( # 0, # 4),
                                                 # 0 <<<<
                                                 --( 
                                                 v( 0),
                                                 replacenth( 
                                                 v( 5), 
                                                 !! (varx), 
                                                 v( 2))
                                                 )---> 
                                                 (# 9 ++++ v( 0)), 
                                                 # 2) **
                                                 (SUM( 
                                                 range( # 0, # 4),
                                                 (--(
                                                 replacenth( 
                                                 v( 5), 
                                                 !! (varx), 
                                                 v( 2)), 
                                                 v( 4) )---> 
                                                 (# 1 ++++ v( 0)) \\//
                                                 --(
                                                 replacenth( 
                                                 v( 5), 
                                                 !! (varx), 
                                                 v( 2)), 
                                                 v( 4) )---> 
                                                 (# 5 ++++ v( 0))) //\\
                                                 nth( v( 4), v( 0)) ==== # 0,
                                                 # 1) **
                                                 AbsAll 
                                                 range( # 0, # 4)
                                                 ([
                                                 # 0 <<<<
                                                 --( 
                                                 v( 1),
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3))
                                                 )---> 
                                                 (# 9 ++++ v( 0))] **
                                                 [
                                                 nth( 
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3)), 
                                                 v( 0)) ==== 
                                                 # 0] *\/*
                                                 [
                                                 # 0 <<<<
                                                 nth( 
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3)), 
                                                 v( 0))] *\/*
                                                 [
                                                 --( 
                                                 v( 1),
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3))
                                                 )---> 
                                                 (# 1 ++++ v( 0)) ==== 
                                                 # 0] **
                                                 [
                                                 --( 
                                                 v( 1),
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3))
                                                 )---> 
                                                 (# 5 ++++ v( 0)) ==== 
                                                 # 0]) **
                                                 AbsAll 
                                                 range( # 0, # 4)
                                                 (AbsAll 
                                                 range( # 0, # 4)
                                                 ((((([
                                                 --( 
                                                 v( 2),
                                                 replacenth( 
                                                 v( 7), 
                                                 !! (varx), 
                                                 v( 4))
                                                 )---> 
                                                 (# 9 ++++ v( 0))] *\/*
                                                 [
                                                 --( 
                                                 v( 2),
                                                 replacenth( 
                                                 v( 7), 
                                                 !! (varx), 
                                                 v( 4))
                                                 )---> 
                                                 (# 1 ++++ v( 0)) ==== 
                                                 # 0] **
                                                 [
                                                 --( 
                                                 v( 2),
                                                 replacenth( 
                                                 v( 7), 
                                                 !! (varx), 
                                                 v( 4))
                                                 )---> 
                                                 (# 5 ++++ v( 0)) ==== 
                                                 # 0]) *\/*
                                                 [
                                                 ~~
                                                 --( 
                                                 v( 2),
                                                 replacenth( 
                                                 v( 7), 
                                                 !! (varx), 
                                                 v( 4))
                                                 )---> 
                                                 (# 9 ++++ v( 1))]) *\/*
                                                 [
                                                 nth( v( 6), v( 1)) ==== # 0]) *\/*
                                                 [v( 0) ==== v( 1)]) *\/*
                                                 AbsExists
                                                 TreeRecords( v( 4))
                                                 ([
                                                 nth( 
                                                 find( v( 5), v( 0)), 
                                                 # 2) ==== 
                                                 v( 2)] **
                                                 AbsExists
                                                 TreeRecords( 
                                                 find( 
                                                 v( 5), 
                                                 v( 0)))
                                                 ([
                                                 nth( 
                                                 find( v( 6), v( 0)), 
                                                 # 2) ==== 
                                                 v( 1)])))) *\/*
                                                 AbsExists 
                                                 range( # 0, # 4)
                                                 ([
                                                 --( 
                                                 v( 1),
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3))
                                                 )---> 
                                                 (# 1 ++++ v( 0))] **
                                                 [
                                                 nth( v( 5), v( 0)) ==== # 2] *\/*
                                                 [
                                                 --( 
                                                 v( 1),
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3))
                                                 )---> 
                                                 (# 5 ++++ v( 0))] **
                                                 [
                                                 nth( 
                                                 v( 1),
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3))) ==== 
                                                 # 1]) **
                                                 AbsAll 
                                                 range( # 0, # 4)
                                                 ([
                                                 # 0 ==== 
                                                 nth( v( 5), v( 0))] *\/*
                                                 [
                                                 --( 
                                                 v( 1),
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3))
                                                 )---> 
                                                 (# 9 ++++ v( 0)) ==== 
                                                 # 0] **
                                                 [
                                                 # 0 <<<< nth( v( 5), v( 0))] *\/*
                                                 AbsExists
                                                 TreeRecords( v( 3))
                                                 ([
                                                 nth( 
                                                 find( v( 4), v( 0)), 
                                                 # 2) ==== 
                                                 v( 1)]) **
                                                 AbsExists
                                                 TreeRecords( 
                                                 find( 
                                                 v( 0), 
                                                 v( 0)))
                                                 ([
                                                 # 0 <<<<
                                                 --( 
                                                 v( 2),
                                                 replacenth( 
                                                 v( 7), 
                                                 !! (varx), 
                                                 v( 4))
                                                 )---> 
                                                 (# 1 ++++
                                                 nth( 
                                                 find( v( 4), v( 0)), 
                                                 # 2))] **
                                                 [
                                                 nth( 
                                                 find( v( 4), v( 0)), 
                                                 # 3) ==== 
                                                 # 2] *\/*
                                                 [
                                                 # 0 <<<<
                                                 --( 
                                                 v( 2),
                                                 replacenth( 
                                                 v( 7), 
                                                 !! (varx), 
                                                 v( 4))
                                                 )---> 
                                                 (# 5 ++++
                                                 nth( 
                                                 find( v( 4), v( 0)), 
                                                 # 2))] **
                                                 [
                                                 nth( 
                                                 find( v( 4), v( 0)), 
                                                 # 3) ==== 
                                                 # 1])) *\/*
                                                 AbsAll 
                                                 range( # 0, # 4)
                                                 ([
                                                 --( 
                                                 v( 1),
                                                 replacenth( 
                                                 v( 6), 
                                                 !! (varx), 
                                                 v( 3))
                                                 )---> 
                                                 (# 9 ++++ v( 0)) ==== 
                                                 # 0] *\/*
                                                 [
                                                 nth( v( 5), v( 0)) ==== # 0]))))) **
                                                [!! (assignments_to_do_head)
                                                 inTree 
                                                 v( 2)] **
                                                [nth( 
                                                 find( 
                                                 !! 
                                                 (assignments_to_do_head),
                                                 v( 2)), 
                                                 # 1) ==== 
                                                 # 0]) ** 
                                               [# 0 <<<< v( 6)]) **
                                              [v( 7) ==== # 0]) ** 
                                             [v( 5)]) **
                                            [!! (backtrack) ==== # 0]) **
                                           [!! (stack) ==== !! (ssss)]) **
                                          [!! (have_var) ==== # 1]) **
                                         ARRAY( !! (assignments), # 4, v( 3)))))))))))))))
    ([~~ (convertToAbsExp (! iiii <<= ANum var_count))] ** haveVarInvariant)
    invariant
.
Proof.
    (*unfold haveVarInvariant. unfold invariant. unfold invariantCore. 
    unfold invariantCoreNoTail. unfold validTail.
    unfold validBackPointers. unfold assignmentConsistent.
    unfold watchVariablesExists. unfold watchVariablesLinkedIffSet.
    unfold twoWatchVariables. unfold allButOneAssigned. unfold satisfyingAssignmentMade.
    unfold watchAfterSatisfyingAssignment.
    unfold watchesUnassigned.
    unfold haveVarComponent.
    unfold onlyOneUnassigned. unfold unassignedVariablesAreWatches.
    unfold mostRecentAssignedIsWatch.
    unfold coreStructures.
    eapply breakRightClosureThm. simpl. reflexivity.
    eapply breakRightClosureThm. simpl. reflexivity.
    eapply breakRightClosureThm. simpl. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    mergePropagateExistsRight.
    eapply mergePropagateLeft. compute. reflexivity.
    eapply mergeImplies. eapply ex_intro. split.

    startMerge.

    doMergeStates.
    eapply DMImplyPredicates1.
    eapply PESComposeRight. eapply PESComposeLeft. eapply PESComposeLeft. eapply PESComposeRight. eapply PESComposeLeft. eapply PESComposeLeft. eapply PESComposeRight.  eapply PESComposeRight. eapply PESComposeLeft. eapply PESAll.
    compute. reflexivity.
    apply mergePredicateTheorem1.
    eapply DMImplyPredicates1.
    eapply PESComposeRight. eapply PESComposeLeft. eapply PESComposeLeft. eapply PESComposeRight. eapply PESComposeLeft. eapply PESComposeRight. eapply PESAll.
    compute. reflexivity.
    apply mergePredicateTheorem2.
    eapply DMImplyPredicates1.
    eapply PESComposeRight. eapply PESComposeLeft. eapply PESComposeLeft. eapply PESComposeRight. eapply PESComposeRight. eapply PESComposeRight. eapply PESEach.
    compute. reflexivity.
    apply mergePredicateTheorem3.
    eapply DMFinish. solveAllPredicates. solveAllPredicates.
    intros.
    eapply breakTopClosureThm1. compute. reflexivity.
    eapply breakTopClosureThm1. compute. reflexivity.
    apply mergeFinalImplication1. apply H.*)
    admit.
Admitted.

Theorem mergeTheorem2UnfoldNotNull :
  forall (s : (id -> nat) * (nat -> option nat)) (bindings : list Value),
  realizeState
        (([v( 8) ==== # 0] **
          [v( 6)] **
          [!! (backtrack) ==== # 0] **
          [!! (stack) ==== !! (ssss)] ** [!! (have_var) ==== # 1] ** AbsEmpty) **
         (((TREE( !! (clauses), v( 0), # 21, # 0 :: nil) **
            TREE( !! (assignments_to_do_head), v( 1), # 4, # 0 :: nil) **
            TREE( v( 7), v( 2), # 4, # 0 :: nil) **
            ARRAY( !! (assignments), # 4, v( 3)) **
            ARRAY( !! (watches), # 4, v( 4))) **
           (AbsAll TreeRecords( v( 2))
              ([nth( find( v( 3), v( 0)), # 2) <<<< # 4] **
               ([nth( find( v( 3), v( 0)), # 3) ==== # 1] *\/*
                [nth( find( v( 3), v( 0)), # 3) ==== # 2]) **
               [nth( v( 4), nth( find( v( 3), v( 0)), # 2)) ====
                nth( find( v( 3), v( 0)), # 3)] **
               AbsAll TreeRecords( nth( find( v( 3), v( 0)), # 1))
                 ([~~
                   nth( find( v( 4), v( 1)), # 2) ====
                   nth( find( nth( find( v( 4), v( 1)), # 1), v( 0)), # 2)])) **
            AbsAll range( # 0, # 4)
              ([nth( v( 4), v( 0)) ==== # 0] *\/*
               AbsExists TreeRecords( v( 3))
                 ([nth( find( v( 4), v( 0)), # 2) ==== v( 1) //\\
                   nth( find( v( 4), v( 0)), # 3) ==== nth( v( 5), v( 1))]))) **
           AbsAll TreeRecords( v( 1))
             ([--( v( 2), v( 0) )---> # 1 ==== # 0 //\\
               nth( v( 2), v( 0)) ==== v( 0) \\//
               --( v( 2), v( 0) )---> # 1 inTree v( 0) //\\
               --( v( 2), --( v( 2), v( 0) )---> # 1 )---> # 0 ==== v( 0)]) **
           AbsEach range( # 0, # 4)
             (AbsExistsT
                (Path( nth( v( 4), v( 5)), v( 0), 
                 v( 6), # 21, # 13 ++++ v( 5) :: nil) **
                 AbsAll TreeRecords( v( 6))
                   ([--( v( 7), v( 0) )---> (# 17 ++++ v( 3)) ==== # 0 //\\
                     nth( v( 7), v( 0)) ==== v( 0) \\//
                     --( v( 7), v( 0) )---> (# 17 ++++ v( 3)) inTree v( 0) //\\
                     --( v( 7), --( v( 7), v( 0) )---> (# 17 ++++ v( 3))
                     )---> (# 13 ++++ v( 3)) ==== 
                     v( 0)]) **
                 AbsAll TreeRecords( v( 0))
                   (AbsExists range( # 0, # 4)
                      ([--( v( 1), v( 6) )---> (# 1 ++++ v( 0)) //\\
                        (nth( v( 4), v( 0)) ==== # 2 \\//
                         nth( v( 4), v( 0)) ==== # 0) \\//
                        --( v( 1), v( 6) )---> (# 5 ++++ v( 2)) //\\
                        (nth( v( 4), v( 0)) ==== # 1 \\//
                         nth( v( 4), v( 0)) ==== # 0)])) **
                 AbsAll range( # 0, # 4)
                   ([(--( v( 0), v( 1) )---> (# 9 ++++ v( 0)) ==== # 0 \\//
                      --( v( 0), v( 1) )---> (# 1 ++++ v( 0))) \\//
                     --( v( 0), v( 1) )---> (# 5 ++++ v( 0))]) **
                 AbsAll range( # 0, # 4)
                   ([# 0 <<<< --( v( 1), v( 6) )---> (# 9 ++++ v( 0)) //\\
                     (# 0 <<<< --( v( 1), v( 6) )---> (# 17 ++++ v( 0)) \\//
                      nth( v( 0), v( 2)) ==== v( 1)) \\//
                     (--( v( 1), v( 6) )---> (# 9 ++++ v( 0)) ==== # 0 //\\
                      --( v( 1), v( 6) )---> (# 17 ++++ v( 0)) ==== # 0) //\\
                     ~~ nth( v( 4), v( 0)) ==== v( 6)]) **
                 SUM( range( # 0, # 4),
                 # 0 <<<< --( v( 0), v( 5) )---> (# 9 ++++ v( 0)), 
                 # 2) **
                 (SUM( range( # 0, # 4),
                  (--( v( 5), v( 3) )---> (# 1 ++++ v( 0)) \\//
                   --( v( 5), v( 3) )---> (# 5 ++++ v( 0))) //\\
                  nth( v( 3), v( 0)) ==== # 0, # 1) **
                  AbsAll range( # 0, # 4)
                    ([# 0 <<<< --( v( 1), v( 6) )---> (# 9 ++++ v( 0)) //\\
                      nth( v( 6), v( 0)) ==== # 0 \\//
                      (# 0 <<<< nth( v( 6), v( 0)) \\//
                       --( v( 1), v( 6) )---> (# 1 ++++ v( 0)) ==== # 0 //\\
                       --( v( 1), v( 6) )---> (# 5 ++++ v( 0)) ==== # 0)]) **
                  AbsAll range( # 0, # 4)
                    (AbsAll range( # 0, # 4)
                       ([((((--( v( 2), v( 7) )---> (# 9 ++++ v( 0)) \\//
                             --( v( 2), v( 7) )---> (# 1 ++++ v( 0)) ==== # 0 //\\
                             --( v( 2), v( 7) )---> (# 5 ++++ v( 0)) ==== # 0) \\//
                            ~~ --( v( 2), v( 7) )---> (# 9 ++++ v( 1))) \\//
                           nth( v( 5), v( 1)) ==== # 0) \\//
                          nth( v( 5), v( 1)) ==== # 0) \\// 
                         v( 0) ==== v( 1)] *\/*
                        AbsExists TreeRecords( v( 4))
                          (AbsExists TreeRecords( find( v( 5), v( 0)))
                             ([nth( find( v( 6), v( 1)), # 2) ==== v( 3)] **
                              [nth( find( v( 6), v( 0)), # 2) ==== v( 1)])))) *\/*
                  AbsExists range( # 0, # 4)
                    ([--( v( 1), v( 6) )---> (# 1 ++++ v( 0)) //\\
                      nth( v( 4), v( 0)) ==== # 2 \\//
                      --( v( 1), v( 6) )---> (# 5 ++++ v( 0)) //\\
                      nth( v( 1), v( 6)) ==== # 1] **
                     AbsAll range( # 0, # 4)
                       ([# 0 ==== nth( v( 5), v( 0))] *\/*
                        [--( v( 2), v( 7) )---> (# 9 ++++ v( 0)) ==== # 0] **
                        [# 0 <<<< nth( v( 5), v( 0))] *\/*
                        AbsExists TreeRecords( v( 4))
                          (AbsExists TreeRecords( find( v( 1), v( 1)))
                             ([nth( find( v( 6), v( 1)), # 2) ==== v( 2)] **
                              [# 0 <<<<
                               --( v( 4), v( 9)
                               )---> (# 1 ++++ nth( find( v( 6), v( 0)), # 2)) //\\
                               nth( find( v( 6), v( 0)), # 3) ==== # 2 \\//
                               # 0 <<<<
                               --( v( 4), v( 9)
                               )---> (# 5 ++++ nth( find( v( 6), v( 0)), # 2)) //\\
                               nth( find( v( 6), v( 0)), # 3) ==== # 1])))) *\/*
                  AbsAll range( # 0, # 4)
                    ([--( v( 1), v( 6) )---> (# 9 ++++ v( 0)) ==== # 0 \\//
                      nth( v( 4), v( 0)) ==== # 0]))))) **
          [!! (assignments_to_do_head) inTree v( 1)] **
          [nth( find( !! (assignments_to_do_head), v( 1)), # 1) ==== # 0]) **
         ([# 0 <<<< v( 7)] *\/* [v( 6) ==== # 0])) bindings s
 ->
     exists v : nat, nth 7 bindings NoValue = NatValue (S v).
Proof.
    (*intros. Opaque nth.
    simplifyHyp H.
    eapply stateAssertionThm in H. compute in H. crunch.
    remember (nth 7 bindings NoValue). destruct y. destruct n. omega. exists n.
    reflexivity. inversion H18. inversion H18. inversion H18.*)
    admit.
Admitted.

Theorem stripUpdateVarLeftp
    : forall left right m,
      mergeStates (stripUpdateVar left) right m -> mergeStates left right m.
Proof.
    admit.
Admitted.

Theorem breakLeftClosureThmp
    : forall left right m,
      mergeStates (breakTopClosure left) right m -> mergeStates left right m.
Proof.
    admit.
Admitted.

Theorem mergePropagateLeftp
    : forall P1 P2 P,
      mergeStates (propagateExists nil P1) P2 P -> mergeStates P1 P2 P.
Proof.
    admit.
Admitted.

Theorem mergeSimplifyLeftp
    : forall P1 P2 P,
      mergeStates (simplifyState nil P1) P2 P -> mergeStates P1 P2 P.
Proof.
    admit.
Admitted.

Theorem stripUpdateWithLocLeftp
    : forall P1 P2 P,
      mergeStates (stripUpdateWithLoc P1) P2 P -> mergeStates P1 P2 P.
Proof.
    admit.
Admitted.

Theorem localizeExistsLeftp
    : forall P1 P2 P,
      mergeStates (localizeExists P1 0) P2 P -> mergeStates P1 P2 P.
Proof.
    admit.
Admitted.

Ltac compute_left :=
match goal with
|- mergeStates ?L ?R ?M  =>
   let l' := eval vm_compute in L in
   replace L with l' ; [idtac | vm_cast_no_check (refl_equal l')]
end.

Ltac compute_right :=
match goal with
|- mergeStates ?L ?R ?M  =>
   let r' := eval vm_compute in R in
   replace R with r' ; [idtac | vm_cast_no_check (refl_equal r')]
end.


Theorem mergeTheorem2 :
mergeStates
    (AbsUpdateLoc
       (AbsUpdateVar
          (AbsUpdateVar
             (AbsMagicWand
                (AbsUpdateWithLoc
                   (AbsUpdateWithLoc
                      (AbsUpdateWithLoc
                         (AbsUpdateVar
                            ([!! (backtrack)] **
                             AbsUpdateVar ([# 1] ** loopInvariant) 
                               have_var # 0) backtrack 
                            # 0) varx !! (stack) ++++ # stack_var_offset)
                      valuex !! (stack) ++++ # stack_val_offset) 
                   ssss !! (stack) ++++ # next_offset)
                (AbsExistsT
                   (AbsExistsT
                      (AbsExistsT
                         (AbsExistsT
                            (AbsExistsT
                               (v( 0) ++++ # 3 |-> v( 4) **
                                v( 0) ++++ # 2 |-> v( 3) **
                                v( 0) ++++ # 1 |-> v( 2) **
                                v( 0) ++++ # 0 |-> v( 1) **
                                [!! (stack) ==== v( 0)]))))))) 
             stack !! (ssss)) have_var # 1) !! (assignments) ++++ !! (varx)
       # 0)
    ([~~ (convertToAbsExp (! iiii <<= ANum var_count))] ** haveVarInvariant)
    invariant.
Proof.
    eapply stripUpdateVarLeftp. compute_left.
    eapply breakLeftClosureThmp. compute_left.
    eapply breakLeftClosureThmp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply unfold_merge1.  

    unfoldHeap (AbsQVar 7).

    Transparent nth.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergeSimplifyLeftp. compute_left.
    eapply mergeSimplifyLeftp. compute_left.
    eapply mergeSimplifyLeftp. compute_left.
    eapply mergeSimplifyLeftp. compute_left.
    eapply mergeSimplifyLeftp. compute_left.
    eapply mergeSimplifyLeftp. compute_left.
    eapply mergeSimplifyLeftp. compute_left.
    eapply mergeSimplifyLeftp. compute_left.
    eapply mergeSimplifyLeftp. compute_left.
    eapply mergeSimplifyLeftp. compute_left.
    eapply mergeSimplifyLeftp. compute_left.
    eapply stripUpdateWithLocLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply mergePropagateLeftp. compute_left.
    eapply localizeExistsLeftp. compute_left.
    eapply localizeExistsLeftp. compute_left.
    eapply localizeExistsLeftp. compute_left.
    eapply localizeExistsLeftp. compute_left.
    eapply localizeExistsLeftp. compute_left.
    eapply localizeExistsLeftp. compute_left.
    eapply removeMagicWandLeft. compute. reflexivity.
    eapply mergeSimplifyLeftp. compute_left.
    eapply mergeSimplifyLeftp. compute_left.
    eapply mergeSimplifyLeftp. compute_left.

    eapply removeUpdateLocLeft. compute. reflexivity.

    intros.
    eapply mergeTheorem2Index. apply H.

    apply mergeMergeTheorem2.  Opaque nth.

    compute. intros.
    eapply mergeTheorem2UnfoldNotNull. apply H.
    admit.



Admitted.




Theorem validRefTheorem1 : forall s n b, id -> nat -> realizeState
        (AbsExistsT
           (AbsExistsT
              (AbsExistsT
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (v(0) ++++ #4 |-> v(5) **
                           v(0) ++++ #3 |-> v(4) **
                           v(0) ++++ #2 |-> v(3) **
                           v(0) ++++ #1 |-> v(2) **
                           v(0) ++++ #0 |-> v(1) **
                           [!!(todo) ==== v(0)] **
                           AbsExistsT
                             ([~~ !!(have_var) ==== #0] **
                              pushAbsVarState
                                (pushAbsVarState
                                   (pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (quantifyAbsVarState invariant
                                                  todo)))))))))))))) nil s -> NatValue n =
       basicEval AbsPlusId
         (NatValue (b todo) :: @NatValue unit next_offset :: nil) -> heap_p s n <> None.
Proof.
 admit.
Admitted.


Theorem validRefTheorem2 : forall s n b, id -> nat -> realizeState
        (AbsUpdateLoc
           (AbsExistsT
              (AbsExistsT
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (v(0) ++++ #4 |-> v(5) **
                              v(0) ++++ #3 |-> v(4) **
                              v(0) ++++ #2 |-> v(3) **
                              v(0) ++++ #1 |-> v(2) **
                              v(0) ++++ #0 |-> v(1) **
                              [!!(todo) ==== v(0)] **
                              AbsExistsT
                                ([~~ !!(have_var) ==== #0] **
                                 pushAbsVarState
                                   (pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  invariant 
                                                  todo))))))))))))))
           !!(todo) ++++ #next_offset !!(assignments_to_do_head)) nil s -> NatValue n =
       basicEval AbsPlusId
         (NatValue (b todo) :: @NatValue unit prev_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem3 : forall s n b, id -> nat -> realizeState
        ([~~ !!(assignments_to_do_tail) ==== #0] **
         AbsUpdateLoc
           (AbsUpdateLoc
              (AbsExistsT
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (AbsExistsT
                                (v(0) ++++ #4 |-> v(5) **
                                 v(0) ++++ #3 |-> v(4) **
                                 v(0) ++++ #2 |-> v(3) **
                                 v(0) ++++ #1 |-> v(2) **
                                 v(0) ++++ #0 |-> v(1) **
                                 [!!(todo) ==== v(0)] **
                                 AbsExistsT
                                   ([~~ !!(have_var) ==== #0] **
                                    pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  invariant 
                                                  todo))))))))))))))
              !!(todo) ++++ #next_offset !!(assignments_to_do_head))
           !!(todo) ++++ #prev_offset #0) nil s -> NatValue n =
       basicEval AbsPlusId
         (NatValue (b assignments_to_do_head) :: @NatValue unit prev_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem mergeTheorem3 : mergeStates
     (AbsUpdateVar
        ([!!(assignments_to_do_tail) ==== #0] **
         AbsUpdateLoc
           (AbsUpdateLoc
              (AbsExistsT
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (AbsExistsT
                                (v(0) ++++ #4 |-> v(5) **
                                 v(0) ++++ #3 |-> v(4) **
                                 v(0) ++++ #2 |-> v(3) **
                                 v(0) ++++ #1 |-> v(2) **
                                 v(0) ++++ #0 |-> v(1) **
                                 [!!(todo) ==== v(0)] **
                                 AbsExistsT
                                   ([~~ !!(have_var) ==== #0] **
                                    pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  invariant 
                                                  todo))))))))))))))
              !!(todo) ++++ #next_offset !!(assignments_to_do_head))
           !!(todo) ++++ #prev_offset #0) assignments_to_do_tail 
        !!(todo))
     (AbsUpdateLoc
        ([~~ !!(assignments_to_do_tail) ==== #0] **
         AbsUpdateLoc
           (AbsUpdateLoc
              (AbsExistsT
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (AbsExistsT
                                (v(0) ++++ #4 |-> v(5) **
                                 v(0) ++++ #3 |-> v(4) **
                                 v(0) ++++ #2 |-> v(3) **
                                 v(0) ++++ #1 |-> v(2) **
                                 v(0) ++++ #0 |-> v(1) **
                                 [!!(todo) ==== v(0)] **
                                 AbsExistsT
                                   ([~~ !!(have_var) ==== #0] **
                                    pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  invariant 
                                                  todo))))))))))))))
              !!(todo) ++++ #next_offset !!(assignments_to_do_head))
           !!(todo) ++++ #prev_offset #0)
        !!(assignments_to_do_head) ++++ #prev_offset 
        !!(todo)) invariant.
Proof.
    admit.
Admitted.




























































































































































































































































































































































































































































































