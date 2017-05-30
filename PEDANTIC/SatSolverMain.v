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
Require Export SatSolverDefs.
Require Export SatSolverAux1.

Opaque basicEval.
Opaque invariant.
Opaque haveVarInvariant.

Definition x := 1.

Theorem varNeqBacktrack : varx <> backtrack.
Proof.
    admit.
Admitted.


Theorem validRefTheorem4 : forall s n b, id -> nat -> realizeState (AbsUpdateVar invariant assignments_to_do_head !!(todo))
        nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b todo) :: @NatValue unit todo_var_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.



Theorem validRefTheorem5 : forall s n b, id -> nat -> realizeState
        (AbsUpdateLoc
           (AbsUpdateVar invariant assignments_to_do_head !!(todo))
           !!(todo) ++++ #todo_var_offset !!(varx)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b todo) :: @NatValue unit todo_val_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.

Theorem validRefTheorem7: forall s n b, id -> nat -> realizeState
        (AbsUpdateVar
           ([!!(ssss)] **
            AbsUpdateWithLoc
              (AbsUpdateWithLoc
                 (AbsUpdateWithLoc
                    (AbsUpdateWithLoc
                       ([!!(assignments_to_do_tail)] ** invariant) 
                       varx !!(assignments_to_do_tail) ++++ #todo_var_offset)
                    valuex !!(assignments_to_do_tail) ++++ #todo_val_offset)
                 prop !!(assignments_to_do_tail) ++++ #todo_unit_offset) 
              ssss !!(assignments_to_do_tail) ++++ #prev_offset)
           assignments_to_do_tail !!(ssss)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b ssss) :: @NatValue unit next_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.




Theorem existsTheorem1 : exists s : state,
     realizeState
       (AbsMagicWand
          (AbsUpdateLoc
             (AbsUpdateVar
                ([!!(ssss)] **
                 AbsUpdateWithLoc
                   (AbsUpdateWithLoc
                      (AbsUpdateWithLoc
                         (AbsUpdateWithLoc
                            ([!!(assignments_to_do_tail)] ** invariant) 
                            varx
                            !!(assignments_to_do_tail) ++++ #todo_var_offset)
                         valuex
                         !!(assignments_to_do_tail) ++++ #todo_val_offset)
                      prop !!(assignments_to_do_tail) ++++ #todo_unit_offset)
                   ssss !!(assignments_to_do_tail) ++++ #prev_offset)
                assignments_to_do_tail !!(ssss)) !!(ssss) ++++ #next_offset
             #0)
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
                             v(0) ++++ #0 |-> v(1) ** [!!(ssss) ==== v(0)]))))))))
       nil s.
Proof.
    admit.
Admitted.


Theorem existsTheorem2 : exists s : state,
     realizeState
       (AbsMagicWand
          ([~~ !!(ssss)] **
           AbsUpdateWithLoc
             (AbsUpdateWithLoc
                (AbsUpdateWithLoc
                   (AbsUpdateWithLoc
                      ([!!(assignments_to_do_tail)] ** invariant) 
                      varx !!(assignments_to_do_tail) ++++ #todo_var_offset)
                   valuex !!(assignments_to_do_tail) ++++ #todo_val_offset)
                prop !!(assignments_to_do_tail) ++++ #todo_unit_offset) 
             ssss !!(assignments_to_do_tail) ++++ #prev_offset)
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
                             v(0) ++++ #0 |-> v(1) ** [!!(ssss) ==== v(0)]))))))))
       nil s.
Proof.



    admit.
Admitted.


Theorem mergeTheorem4 : mergeStates
     (AbsMagicWand
        (AbsUpdateLoc
           (AbsUpdateVar
              ([!!(ssss)] **
               AbsUpdateWithLoc
                 (AbsUpdateWithLoc
                    (AbsUpdateWithLoc
                       (AbsUpdateWithLoc
                          ([!!(assignments_to_do_tail)] ** invariant) 
                          varx
                          !!(assignments_to_do_tail) ++++ #todo_var_offset)
                       valuex
                       !!(assignments_to_do_tail) ++++ #todo_val_offset) 
                    prop !!(assignments_to_do_tail) ++++ #todo_unit_offset)
                 ssss !!(assignments_to_do_tail) ++++ #prev_offset)
              assignments_to_do_tail !!(ssss)) !!(ssss) ++++ #next_offset 
           #0)
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
                           v(0) ++++ #0 |-> v(1) ** [!!(ssss) ==== v(0)]))))))))
     (AbsUpdateVar
        (AbsUpdateVar
           (AbsMagicWand
              ([~~ !!(ssss)] **
               AbsUpdateWithLoc
                 (AbsUpdateWithLoc
                    (AbsUpdateWithLoc
                       (AbsUpdateWithLoc
                          ([!!(assignments_to_do_tail)] ** invariant) 
                          varx
                          !!(assignments_to_do_tail) ++++ #todo_var_offset)
                       valuex
                       !!(assignments_to_do_tail) ++++ #todo_val_offset) 
                    prop !!(assignments_to_do_tail) ++++ #todo_unit_offset)
                 ssss !!(assignments_to_do_tail) ++++ #prev_offset)
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
                                 [!!(ssss) ==== v(0)]))))))))
           assignments_to_do_head #0) assignments_to_do_tail 
        #0) invariant.
Proof.
    admit.
Admitted.


Theorem existsTheorem3 : exists s : state,
     realizeState
       (AbsMagicWand
          (AbsUpdateWithLoc ([!!(assignments_to_do_head)] ** invariantNoTail)
             todo !!(assignments_to_do_head) ++++ #next_offset)
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
                             [!!(assignments_to_do_head) ==== v(0)]))))))))
       nil s.
Proof.




    admit.
Admitted.


Theorem entailment3 : forall s : state,
   realizeState
     (AbsUpdateVar
        (AbsMagicWand
           (AbsUpdateWithLoc
              ([!!(assignments_to_do_head)] ** invariantNoTail) 
              todo !!(assignments_to_do_head) ++++ #next_offset)
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
                              [!!(assignments_to_do_head) ==== v(0)]))))))))
        assignments_to_do_head !!(todo)) nil s ->
   realizeState invariantNoTail nil s.
Proof.


    admit.
Admitted.


Theorem entailment4 : forall x0 : state,
   realizeState
     ([~~ !!(ssss) ==== !!(valuex)] **
      [!!(ssss)] **
      AbsUpdateWithLoc invariant ssss !!(assignments) ++++ !!(varx)) nil x0 ->
   realizeState invariantNoTail nil x0.
Proof.


    admit.
Admitted.


Theorem validRefTheorem8 : forall s n b, id -> nat -> realizeState
        (AbsUpdateWithLoc
           (AbsUpdateWithLoc
              ([!!(stack) //\\ (!!(ssss) \\// !!(vvvv) ==== #2)] ** invariant)
              kkkk !!(stack) ++++ #next_offset) vvvv
           !!(stack) ++++ #stack_var_offset) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b assignments) :: @NatValue unit (b vvvv) :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem existsTheorem4 : exists s : state,
     realizeState
       (AbsMagicWand
          (AbsUpdateLoc
             (AbsUpdateWithLoc
                (AbsUpdateWithLoc
                   ([!!(stack) //\\ (!!(ssss) \\// !!(vvvv) ==== #2)] **
                    invariant) kkkk !!(stack) ++++ #next_offset) 
                vvvv !!(stack) ++++ #stack_var_offset)
             !!(assignments) ++++ !!(vvvv) #0)
          (AbsExistsT
             (AbsExistsT
                (AbsExistsT
                   (AbsExistsT
                      (AbsExistsT
                         (v(0) ++++ #3 |-> v(4) **
                          v(0) ++++ #2 |-> v(3) **
                          v(0) ++++ #1 |-> v(2) **
                          v(0) ++++ #0 |-> v(1) ** [!!(stack) ==== v(0)])))))))
       nil s.
Proof.
    admit.
Admitted.


Theorem entailment5: forall s : state,
   realizeState
     (AbsUpdateWithLoc
        (AbsUpdateWithLoc
           (AbsUpdateVar
              (AbsMagicWand
                 (AbsUpdateLoc
                    (AbsUpdateWithLoc
                       (AbsUpdateWithLoc
                          ([!!(stack) //\\ (!!(ssss) \\// !!(vvvv) ==== #2)] **
                           invariant) kkkk !!(stack) ++++ #next_offset) 
                       vvvv !!(stack) ++++ #stack_var_offset)
                    !!(assignments) ++++ !!(vvvv) #0)
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (AbsExistsT
                                (v(0) ++++ #3 |-> v(4) **
                                 v(0) ++++ #2 |-> v(3) **
                                 v(0) ++++ #1 |-> v(2) **
                                 v(0) ++++ #0 |-> v(1) **
                                 [!!(stack) ==== v(0)]))))))) 
              stack !!(kkkk)) ssss !!(stack) ++++ #stack_prop_offset) 
        vvvv !!(stack) ++++ #stack_val_offset) nil s ->
   realizeState invariant nil s.
Proof.



    admit.
Admitted.


Theorem entailment6 : forall x0 : state,
   realizeState
     (AbsUpdateWithLoc
        (AbsUpdateWithLoc
           (AbsUpdateVar ([~~ !!(assignments_to_do_head)] ** invariantNoTail)
              assignments_to_do_tail #0) ssss
           !!(stack) ++++ #stack_prop_offset) vvvv
        !!(stack) ++++ #stack_val_offset) nil x0 ->
   realizeState invariant nil x0.
Proof.
    admit.
Admitted.


Theorem validRefTheorem9 : forall s n b, id -> nat -> realizeState
        ([~~ !!(stack) ==== #0] **
         [~~ (convertToAbsExp (ALand (!stack) (ALor (!ssss) (!vvvv === A2))))] **
         invariant) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b stack) :: @NatValue unit stack_val_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem10 : forall s n b, id -> nat -> realizeState
        (AbsUpdateWithLoc
           (AbsUpdateLoc
              ([~~ !!(stack) ==== #0] **
               [~~
                (convertToAbsExp
                   (ALand (!stack) (ALor (!ssss) (!vvvv === A2))))] **
               invariant) !!(stack) ++++ #stack_val_offset 
              #2) vvvv !!(stack) ++++ #stack_var_offset) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b assignments) :: @NatValue unit (b vvvv) :: nil) -> heap_p s n <> None.
Proof.
    intros s n b H H0.


    admit.
Admitted.


Theorem mergeReturn1 : mergeReturnStates invariant
     ([!!(stack) ==== #0] **
      [~~ (convertToAbsExp (ALand (!stack) (ALor (!ssss) (!vvvv === A2))))] **
      invariant) invariant (#0 :: #1 :: nil) (#0 :: nil) 
     (#0 :: #1 :: nil).
Proof.



    admit.
Admitted.


Theorem mergeReturn2 : mergeReturnStates invariant invariant invariant 
     (#0 :: #1 :: nil) (#0 :: #1 :: nil) (#0 :: #1 :: nil).
Proof.
    admit.
Admitted.


Theorem mergeTheorem5 : mergeStates
     ([!!(ssss) ==== !!(valuex)] **
      [!!(ssss)] **
      AbsUpdateWithLoc invariant ssss !!(assignments) ++++ !!(varx))
     (AbsUpdateVar
        (AbsUpdateLoc
           (AbsUpdateWithLoc
              (AbsUpdateLoc
                 ([~~ !!(stack) ==== #0] **
                  [~~
                   (convertToAbsExp
                      (ALand (!stack) (ALor (!ssss) (!vvvv === A2))))] **
                  invariant) !!(stack) ++++ #stack_val_offset 
                 #2) vvvv !!(stack) ++++ #stack_var_offset)
           !!(assignments) ++++ !!(vvvv) #2) backtrack 
        #1) invariant.
Proof.


    admit.
Admitted.


Theorem validRefTheorem11 : forall s n b, id -> nat -> realizeState
        ([~~ !!(ssss)] **
         AbsUpdateWithLoc invariant ssss !!(assignments) ++++ !!(varx)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b assignments) :: @NatValue unit (b varx) :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem12 : forall s n b, id -> nat -> realizeState
        (AbsExistsT
           (AbsExistsT
              (AbsExistsT
                 (AbsExistsT
                    (AbsExistsT
                       (v(0) ++++ #3 |-> v(4) **
                        v(0) ++++ #2 |-> v(3) **
                        v(0) ++++ #1 |-> v(2) **
                        v(0) ++++ #0 |-> v(1) **
                        [!!(ssss) ==== v(0)] **
                        AbsExistsT
                          (AbsUpdateLoc
                             ([~~ v(5)] **
                              AbsUpdateWithLoc
                                (pushAbsVarState
                                   (pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (quantifyAbsVarState invariant
                                                  ssss)))))) 
                                ssss !!(assignments) ++++ !!(varx))
                             !!(assignments) ++++ !!(varx) 
                             !!(valuex)))))))) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b ssss) :: @NatValue unit next_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem13 : forall s n b, id -> nat -> realizeState
        (AbsUpdateVar
           (AbsUpdateLoc
              (AbsExistsT
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (v(0) ++++ #3 |-> v(4) **
                              v(0) ++++ #2 |-> v(3) **
                              v(0) ++++ #1 |-> v(2) **
                              v(0) ++++ #0 |-> v(1) **
                              [!!(ssss) ==== v(0)] **
                              AbsExistsT
                                (AbsUpdateLoc
                                   ([~~ v(5)] **
                                    AbsUpdateWithLoc
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  invariant 
                                                  ssss)))))) 
                                      ssss !!(assignments) ++++ !!(varx))
                                   !!(assignments) ++++ !!(varx) 
                                   !!(valuex))))))))
              !!(ssss) ++++ #next_offset !!(stack)) 
           stack !!(ssss)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b ssss) :: @NatValue unit stack_var_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem14 : forall s n b, id -> nat -> realizeState
        (AbsUpdateLoc
           (AbsUpdateVar
              (AbsUpdateLoc
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (AbsExistsT
                                (v(0) ++++ #3 |-> v(4) **
                                 v(0) ++++ #2 |-> v(3) **
                                 v(0) ++++ #1 |-> v(2) **
                                 v(0) ++++ #0 |-> v(1) **
                                 [!!(ssss) ==== v(0)] **
                                 AbsExistsT
                                   (AbsUpdateLoc
                                      ([~~ v(5)] **
                                       AbsUpdateWithLoc
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (pushAbsVarState
                                                  (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  invariant 
                                                  ssss)))))) 
                                         ssss !!(assignments) ++++ !!(varx))
                                      !!(assignments) ++++ !!(varx)
                                      !!(valuex))))))))
                 !!(ssss) ++++ #next_offset !!(stack)) 
              stack !!(ssss)) !!(ssss) ++++ #stack_var_offset 
           !!(varx)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b ssss) :: @NatValue unit stack_val_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem15 : forall s n b, id -> nat -> realizeState
        (AbsUpdateLoc
           (AbsUpdateLoc
              (AbsUpdateVar
                 (AbsUpdateLoc
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (AbsExistsT
                                (AbsExistsT
                                   (v(0) ++++ #3 |-> v(4) **
                                    v(0) ++++ #2 |-> v(3) **
                                    v(0) ++++ #1 |-> v(2) **
                                    v(0) ++++ #0 |-> v(1) **
                                    [!!(ssss) ==== v(0)] **
                                    AbsExistsT
                                      (AbsUpdateLoc
                                         ([~~ v(5)] **
                                          AbsUpdateWithLoc
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (pushAbsVarState
                                                  (pushAbsVarState
                                                  (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  invariant 
                                                  ssss)))))) 
                                            ssss
                                            !!(assignments) ++++ !!(varx))
                                         !!(assignments) ++++ !!(varx)
                                         !!(valuex))))))))
                    !!(ssss) ++++ #next_offset !!(stack)) 
                 stack !!(ssss)) !!(ssss) ++++ #stack_var_offset 
              !!(varx)) !!(ssss) ++++ #stack_val_offset 
           !!(valuex)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b ssss) :: @NatValue unit stack_prop_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem mergeTheorem6 : mergeStates
     (AbsUpdateVar
        ([!!(ssss) //\\ !!(vvvv) ==== #2] **
         AbsUpdateWithLoc
           (AbsUpdateWithLoc
              (AbsUpdateVar ([~~ #3 <<<< !!(jjjj)] ** invariantWLIT1) 
                 jjjj !!(jjjj) ++++ #1) ssss
              (!!(clause) ++++ #positive_lit_offset) ++++ !!(jjjj)) 
           vvvv !!(assignments) ++++ !!(jjjj)) skip 
        #1)
     ([~~ (!!(ssss) //\\ !!(vvvv) ==== #2)] **
      AbsUpdateWithLoc
        (AbsUpdateWithLoc
           (AbsUpdateVar ([~~ #3 <<<< !!(jjjj)] ** invariantWLIT1) 
              jjjj !!(jjjj) ++++ #1) ssss
           (!!(clause) ++++ #positive_lit_offset) ++++ !!(jjjj)) 
        vvvv !!(assignments) ++++ !!(jjjj)) invariantWLIT1.
Proof.
    admit.
Admitted.


Theorem mergeTheorem7 : mergeStates
     (AbsUpdateVar
        ([!!(ssss) //\\ !!(vvvv) ==== #1] **
         AbsUpdateWithLoc invariantWLIT1 ssss
           (!!(clause) ++++ #negative_lit_offset) ++++ !!(jjjj)) 
        skip #1)
     ([~~ (!!(ssss) //\\ !!(vvvv) ==== #1)] **
      AbsUpdateWithLoc invariantWLIT1 ssss
        (!!(clause) ++++ #negative_lit_offset) ++++ !!(jjjj)) invariantWLIT1.
Proof.


    admit.
Admitted.


Theorem mergeTheorem8 : mergeStates
     (AbsUpdateVar
        (AbsUpdateVar
           ([!!(vvvv) //\\ !!(ssss) ==== #0] **
            AbsUpdateWithLoc invariantWLIT1 ssss
              (!!(clause) ++++ #watch_var_offset) ++++ !!(jjjj)) 
           non_watch !!(jjjj)) skip #1)
     ([~~ (!!(vvvv) //\\ !!(ssss) ==== #0)] **
      AbsUpdateWithLoc invariantWLIT1 ssss
        (!!(clause) ++++ #watch_var_offset) ++++ !!(jjjj)) invariantWLIT1.
Proof.


    admit.
Admitted.


Theorem entailment7 : forall x0 : state,
   realizeState
     (AbsUpdateVar
        (AbsUpdateVar
           (AbsUpdateVar
              ([!!(valuex) ==== #2 //\\ !!(ssss) \\//
                !!(valuex) ==== #1 //\\ !!(vvvv)] **
               AbsUpdateWithLoc
                 (AbsUpdateWithLoc
                    (AbsUpdateWithLoc ([!!(clause)] ** invariantWL) 
                       nc (!!(clause) ++++ #watch_next_offset) ++++ !!(varx))
                    ssss (!!(clause) ++++ #negative_lit_offset) ++++ !!(varx))
                 vvvv (!!(clause) ++++ #positive_lit_offset) ++++ !!(varx))
              skip #0) skip #0) jjjj #0) nil x0 ->
   realizeState invariantWLIT1 nil x0.
Proof.
    admit.
Admitted.


Theorem validRefTheorem16 : forall s n b, id -> nat -> realizeState
        (AbsUpdateWithLoc
           ([!!(skip)] **
            [~~ !!(skip)] **
            [~~ (convertToAbsExp (!jjjj <<= A3))] ** invariantWLIT1) 
           ssss !!(watches) ++++ !!(non_watch)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (basicEval assignments_to_do_head
            (NatValue (b clause) :: NatValue watch_next_offset :: nil)
          :: @NatValue unit (b non_watch) :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem17 : forall s n b, id -> nat -> realizeState
        (AbsUpdateLoc
           (AbsUpdateWithLoc
              ([!!(skip)] **
               [~~ !!(skip)] **
               [~~ (convertToAbsExp (!jjjj <<= A3))] ** invariantWLIT1) 
              ssss !!(watches) ++++ !!(non_watch))
           (!!(clause) ++++ #watch_next_offset) ++++ !!(non_watch) 
           !!(ssss)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (basicEval assignments_to_do_head
            (NatValue (b clause) :: NatValue watch_var_offset :: nil)
          :: @NatValue unit (b non_watch) :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem18 : forall s n b, id -> nat -> realizeState
        ([!!(ssss)] **
         AbsUpdateLoc
           (AbsUpdateLoc
              (AbsUpdateWithLoc
                 ([!!(skip)] **
                  [~~ !!(skip)] **
                  [~~ (convertToAbsExp (!jjjj <<= A3))] ** invariantWLIT1)
                 ssss !!(watches) ++++ !!(non_watch))
              (!!(clause) ++++ #watch_next_offset) ++++ !!(non_watch)
              !!(ssss))
           (!!(clause) ++++ #watch_var_offset) ++++ !!(non_watch) 
           #1) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (basicEval assignments_to_do_head
            (NatValue (b ssss) :: NatValue watch_prev_offset :: nil)
          :: @NatValue unit (b non_watch) :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem mergeTheorem9 : mergeStates
     (AbsUpdateLoc
        ([!!(ssss)] **
         AbsUpdateLoc
           (AbsUpdateLoc
              (AbsUpdateWithLoc
                 ([!!(skip)] **
                  [~~ !!(skip)] **
                  [~~ (convertToAbsExp (!jjjj <<= A3))] ** invariantWLIT1)
                 ssss !!(watches) ++++ !!(non_watch))
              (!!(clause) ++++ #watch_next_offset) ++++ !!(non_watch)
              !!(ssss))
           (!!(clause) ++++ #watch_var_offset) ++++ !!(non_watch) 
           #1) (!!(ssss) ++++ #watch_prev_offset) ++++ !!(non_watch)
        !!(clause))
     ([~~ !!(ssss)] **
      AbsUpdateLoc
        (AbsUpdateLoc
           (AbsUpdateWithLoc
              ([!!(skip)] **
               [~~ !!(skip)] **
               [~~ (convertToAbsExp (!jjjj <<= A3))] ** invariantWLIT1) 
              ssss !!(watches) ++++ !!(non_watch))
           (!!(clause) ++++ #watch_next_offset) ++++ !!(non_watch) 
           !!(ssss)) (!!(clause) ++++ #watch_var_offset) ++++ !!(non_watch)
        #1) invariantWLIT1.
Proof.


    admit.
Admitted.


Theorem validRefTheorem19 : forall s n b, id -> nat -> realizeState invariantWLIT1 nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b watches) :: @NatValue unit (b non_watch) :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem20 : forall s n b, id -> nat -> realizeState
        (AbsUpdateLoc invariantWLIT1 !!(watches) ++++ !!(non_watch)
           !!(clause)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (basicEval assignments_to_do_head
            (NatValue (b clause) :: NatValue watch_var_offset :: nil)
          :: @NatValue unit (b varx) :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem21 : forall s n b, id -> nat -> realizeState
        ([!!(ssss)] **
         AbsUpdateWithLoc
           (AbsUpdateWithLoc
              (AbsUpdateLoc
                 (AbsUpdateLoc invariantWLIT1 !!(watches) ++++ !!(non_watch)
                    !!(clause))
                 (!!(clause) ++++ #watch_var_offset) ++++ !!(varx) 
                 #0) ssss (!!(clause) ++++ #watch_prev_offset) ++++ !!(varx))
           vvvv (!!(clause) ++++ #watch_next_offset) ++++ !!(varx)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (basicEval assignments_to_do_head
            (NatValue (b ssss) :: NatValue watch_next_offset :: nil)
          :: @NatValue unit (b varx) :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem22 : forall s n b, id -> nat -> realizeState
        ([~~ !!(ssss)] **
         AbsUpdateWithLoc
           (AbsUpdateWithLoc
              (AbsUpdateLoc
                 (AbsUpdateLoc invariantWLIT1 !!(watches) ++++ !!(non_watch)
                    !!(clause))
                 (!!(clause) ++++ #watch_var_offset) ++++ !!(varx) 
                 #0) ssss (!!(clause) ++++ #watch_prev_offset) ++++ !!(varx))
           vvvv (!!(clause) ++++ #watch_next_offset) ++++ !!(varx)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (@NatValue unit (b watches) :: NatValue (b varx) :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem mergeTheorem10 : mergeStates
     (AbsUpdateLoc
        ([!!(ssss)] **
         AbsUpdateWithLoc
           (AbsUpdateWithLoc
              (AbsUpdateLoc
                 (AbsUpdateLoc invariantWLIT1 !!(watches) ++++ !!(non_watch)
                    !!(clause))
                 (!!(clause) ++++ #watch_var_offset) ++++ !!(varx) 
                 #0) ssss (!!(clause) ++++ #watch_prev_offset) ++++ !!(varx))
           vvvv (!!(clause) ++++ #watch_next_offset) ++++ !!(varx))
        (!!(ssss) ++++ #watch_next_offset) ++++ !!(varx) 
        !!(vvvv))
     (AbsUpdateLoc
        ([~~ !!(ssss)] **
         AbsUpdateWithLoc
           (AbsUpdateWithLoc
              (AbsUpdateLoc
                 (AbsUpdateLoc invariantWLIT1 !!(watches) ++++ !!(non_watch)
                    !!(clause))
                 (!!(clause) ++++ #watch_var_offset) ++++ !!(varx) 
                 #0) ssss (!!(clause) ++++ #watch_prev_offset) ++++ !!(varx))
           vvvv (!!(clause) ++++ #watch_next_offset) ++++ !!(varx))
        !!(watches) ++++ !!(varx) !!(vvvv)) invariantWLIT1.
Proof.
    admit.
Admitted.


Theorem validRefTheorem23 : forall s n b, id -> nat -> realizeState ([!!(vvvv)] ** invariantWLIT1) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (basicEval assignments_to_do_head
            (NatValue (b vvvv) :: NatValue watch_prev_offset :: nil)
          :: @NatValue unit (b varx) :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem mergeTheorem11 : mergeStates
     (AbsUpdateLoc ([!!(vvvv)] ** invariantWLIT1)
        (!!(vvvv) ++++ #watch_prev_offset) ++++ !!(varx) 
        !!(ssss)) ([~~ !!(vvvv)] ** invariantWLIT1) invariantWLIT1.
Proof.
    admit.
Admitted.


Theorem mergeTheorem12 : mergeStates
     (AbsUpdateVar
        ([!!(ssss)] **
         AbsUpdateWithLoc
           (AbsUpdateVar
              ([!!(ssss) //\\ !!(jjjj) ==== #0] **
               AbsUpdateWithLoc
                 (AbsUpdateWithLoc ([~~ #3 <<<< !!(kkkk)] ** invariantWLIT2)
                    ssss (!!(clause) ++++ #watch_var_offset) ++++ !!(kkkk))
                 jjjj !!(assignments) ++++ !!(kkkk)) 
              vvvv !!(kkkk)) ssss
           (!!(clause) ++++ #positive_lit_offset) ++++ !!(vvvv)) 
        val #2)
     ([~~ !!(ssss)] **
      AbsUpdateWithLoc
        (AbsUpdateVar
           ([!!(ssss) //\\ !!(jjjj) ==== #0] **
            AbsUpdateWithLoc
              (AbsUpdateWithLoc ([~~ #3 <<<< !!(kkkk)] ** invariantWLIT2)
                 ssss (!!(clause) ++++ #watch_var_offset) ++++ !!(kkkk)) 
              jjjj !!(assignments) ++++ !!(kkkk)) vvvv 
           !!(kkkk)) ssss
        (!!(clause) ++++ #positive_lit_offset) ++++ !!(vvvv)) invariantWLIT2.
Proof.
    admit.
Admitted.


Theorem mergeTheorem13 : mergeStates
     (AbsUpdateVar
        ([!!(ssss)] **
         AbsUpdateWithLoc invariantWLIT2 ssss
           (!!(clause) ++++ #negative_lit_offset) ++++ !!(vvvv)) 
        val #1)
     ([~~ !!(ssss)] **
      AbsUpdateWithLoc invariantWLIT2 ssss
        (!!(clause) ++++ #negative_lit_offset) ++++ !!(vvvv)) invariantWLIT2.
Proof.
    admit.
Admitted.


Theorem mergeTheorem14 : mergeStates invariantWLIT2
     ([~~ (!!(ssss) //\\ !!(jjjj) ==== #0)] **
      AbsUpdateWithLoc
        (AbsUpdateWithLoc ([~~ #3 <<<< !!(kkkk)] ** invariantWLIT2) 
           ssss (!!(clause) ++++ #watch_var_offset) ++++ !!(kkkk)) 
        jjjj !!(assignments) ++++ !!(kkkk)) invariantWLIT2.
Proof.
    admit.
Admitted.


Theorem entailment8 : forall s : state,
   realizeState (AbsUpdateVar invariantWLIT2 kkkk !!(kkkk) ++++ #1) nil s ->
   realizeState invariantWLIT2 nil s.
Proof.
    admit.
Admitted.


Theorem entailment9 : forall x0 : state,
   realizeState
     (AbsUpdateVar
        ([~~ !!(skip)] **
         [~~ !!(skip)] **
         [~~ (convertToAbsExp (!jjjj <<= A3))] ** invariantWLIT1) 
        kkkk #0) nil x0 -> realizeState invariantWLIT2 nil x0.
Proof.


    admit.
Admitted.


Theorem validRefTheorem24 : forall s n b, id -> nat -> realizeState
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
                             (pushAbsVarState
                                (pushAbsVarState
                                   (pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (quantifyAbsVarState
                                                  ([
                                                  ~~
                                                  (convertToAbsExp
                                                  (!(kkkk) <<= A3))] **
                                                  invariantWLIT2) 
                                                  todo)))))))))))))) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (@NatValue unit (b todo) :: NatValue next_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem25 : forall s n b, id -> nat -> realizeState
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
                                (pushAbsVarState
                                   (pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  ([
                                                  ~~ (convertToAbsExp (!(kkkk) <<= A3))] **
                                                  invariantWLIT2) 
                                                  todo))))))))))))))
           !!(todo) ++++ #next_offset !!(assignments_to_do_head)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (@NatValue unit (b todo) :: NatValue prev_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem26 : forall s n b, id -> nat -> realizeState
        ([!!(assignments_to_do_tail)] **
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
                                   (pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  ([~~ (convertToAbsExp (!(kkkk) <<= A3))] ** invariantWLIT2)
                                                  todo))))))))))))))
              !!(todo) ++++ #next_offset !!(assignments_to_do_head))
           !!(todo) ++++ #prev_offset #0) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (@NatValue unit (b assignments_to_do_head) :: NatValue prev_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem mergeTheorem15 : mergeStates
     (AbsUpdateLoc
        ([!!(assignments_to_do_tail)] **
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
                                   (pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  ([~~ (convertToAbsExp (!(kkkk) <<= A3))] ** invariantWLIT2)
                                                  todo))))))))))))))
              !!(todo) ++++ #next_offset !!(assignments_to_do_head))
           !!(todo) ++++ #prev_offset #0)
        !!(assignments_to_do_head) ++++ #prev_offset 
        !!(todo))
     (AbsUpdateVar
        ([~~ !!(assignments_to_do_tail)] **
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
                                   (pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  ([~~ (convertToAbsExp (!(kkkk) <<= A3))] ** invariantWLIT2)
                                                  todo))))))))))))))
              !!(todo) ++++ #next_offset !!(assignments_to_do_head))
           !!(todo) ++++ #prev_offset #0) assignments_to_do_tail 
        !!(todo)) invariantWLIT2.
Proof.
    admit.
Admitted.


Theorem validRefTheorem27 : forall s n b, id -> nat -> realizeState
        (AbsUpdateVar invariantWLIT2 assignments_to_do_head !!(todo)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (@NatValue unit (b todo) :: NatValue todo_var_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem28 : forall s n b, id -> nat -> realizeState
        (AbsUpdateLoc
           (AbsUpdateVar invariantWLIT2 assignments_to_do_head !!(todo))
           !!(todo) ++++ #todo_var_offset !!(vvvv)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (@NatValue unit (b todo) :: NatValue todo_val_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem29 : forall s n b, id -> nat -> realizeState
        (AbsUpdateLoc
           (AbsUpdateLoc
              (AbsUpdateVar invariantWLIT2 assignments_to_do_head !!(todo))
              !!(todo) ++++ #todo_var_offset !!(vvvv))
           !!(todo) ++++ #todo_val_offset !!(val)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (@NatValue unit (b todo) :: NatValue todo_unit_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem mergeTheorem16 : mergeStates invariantWLIT1
     (AbsUpdateLoc
        (AbsUpdateLoc
           (AbsUpdateLoc
              (AbsUpdateVar invariantWLIT2 assignments_to_do_head !!(todo))
              !!(todo) ++++ #todo_var_offset !!(vvvv))
           !!(todo) ++++ #todo_val_offset !!(val))
        !!(todo) ++++ #todo_unit_offset #1) invariantWLIT1.
Proof.
    admit.
Admitted.


Theorem mergeTheorem17 : mergeStates
     ([!!(skip)] ** [~~ (convertToAbsExp (!jjjj <<= A3))] ** invariantWLIT1)
     invariantWLIT1 invariantWLIT1.
Proof.
    admit.
Admitted.


Theorem mergeReturn3 : mergeReturnStates invariant invariant invariant 
     (#0 :: #1 :: nil) (#0 :: #1 :: nil) (#0 :: #1 :: nil).
Proof.
    admit.
Admitted.

Theorem mergeTheorem18 : mergeStates invariantWLIT1
     ([~~
       (!!(valuex) ==== #2 //\\ !!(ssss) \\//
        !!(valuex) ==== #1 //\\ !!(vvvv))] **
      AbsUpdateWithLoc
        (AbsUpdateWithLoc
           (AbsUpdateWithLoc ([!!(clause)] ** invariantWL) 
              nc (!!(clause) ++++ #watch_next_offset) ++++ !!(varx)) 
           ssss (!!(clause) ++++ #negative_lit_offset) ++++ !!(varx)) 
        vvvv (!!(clause) ++++ #positive_lit_offset) ++++ !!(varx))
     invariantWL.
Proof.
    admit.
Admitted.


Theorem entailment10 : forall s : state,
   realizeState (AbsUpdateVar invariantWL clause !!(nc)) nil s ->
   realizeState invariantWL nil s.
Proof.
    admit.
Admitted.


Theorem equivEvalList1 : forall s : state,
   realizeState invariant nil s ->
   realizeState invariant nil s ->
   equivEvalList (fst s) (#0 :: #1 :: nil) (#0 :: #1 :: nil).
Proof.
    admit.
Admitted.

Set Printing Depth 1000.


Theorem entailment11 : forall x0 : state,
   realizeState
     (AbsUpdateWithLoc
        (AbsUpdateLoc
           (AbsUpdateLoc
              (AbsUpdateLoc
                 (AbsUpdateVar
                    (AbsUpdateLoc
                       (AbsExistsT
                          (AbsExistsT
                             (AbsExistsT
                                (AbsExistsT
                                   (AbsExistsT
                                      (v(0) ++++ #3 |-> v(4) **
                                       v(0) ++++ #2 |-> v(3) **
                                       v(0) ++++ #1 |-> v(2) **
                                       v(0) ++++ #0 |-> v(1) **
                                       [!!(ssss) ==== v(0)] **
                                       AbsExistsT
                                         (AbsUpdateLoc
                                            ([~~ v(5)] **
                                             AbsUpdateWithLoc
                                               (pushAbsVarState
                                                  (pushAbsVarState
                                                  (pushAbsVarState
                                                  (pushAbsVarState
                                                  (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  invariant 
                                                  ssss)))))) 
                                               ssss
                                               !!(assignments) ++++ !!(varx))
                                            !!(assignments) ++++ !!(varx)
                                            !!(valuex))))))))
                       !!(ssss) ++++ #next_offset !!(stack)) 
                    stack !!(ssss)) !!(ssss) ++++ #stack_var_offset 
                 !!(varx)) !!(ssss) ++++ #stack_val_offset 
              !!(valuex)) !!(ssss) ++++ #stack_prop_offset 
           !!(prop)) clause !!(watches) ++++ !!(varx)) nil x0 ->
   realizeState invariantWL nil x0.
Proof.



    admit.
Admitted.


Theorem mergeReturn4 : mergeReturnStates invariant invariant invariant 
     (#0 :: #1 :: nil) (#0 :: #1 :: nil) (#0 :: #1 :: nil).
Proof.
    admit.
Admitted.


Theorem mergeTheorem19 : mergeStates invariant ([~~ (convertToAbsExp (!clause))] ** invariantWL)
     invariant.
Proof.
    admit.
Admitted.


Theorem entailment12 : forall x0 : state,
   realizeState
     (AbsUpdateLoc
        (AbsUpdateLoc
           (AbsUpdateLoc
              (AbsUpdateVar invariant assignments_to_do_head !!(todo))
              !!(todo) ++++ #todo_var_offset !!(varx))
           !!(todo) ++++ #todo_val_offset !!(valuex))
        !!(todo) ++++ #todo_unit_offset #0) nil x0 ->
   realizeState invariant nil x0.
Proof.
    admit.
Admitted.


Theorem mergeReturn5 : mergeReturnStates ([!!(have_var) ==== #0] ** invariant) invariant
     invariant (#1 :: nil) (#0 :: #1 :: nil) (#0 :: #1 :: nil).
Proof.
    admit.
Admitted.


Theorem mergeReturn6 : mergeReturnStates invariant invariant invariant 
     (#0 :: #1 :: nil) (#0 :: #1 :: nil) (#0 :: #1 :: nil).
Proof.
    admit.
Admitted.


Theorem entailment13 : forall s : state,
   realizeState
     ([~~ (convertToAbsExp (!assignments_to_do_tail))] ** invariant) nil s ->
   realizeState invariant nil s.
Proof.
    admit.
Admitted.


Theorem entailment14 : forall x0 : state,
   realizeState (AbsUpdateVar invariant backtrack #0) nil x0 ->
   realizeState invariant nil x0.
Proof.
    admit.
Admitted.


Theorem mergeReturn7 : mergeReturnStates AbsNone invariant invariant (#0 :: nil)
     (#0 :: #1 :: nil) (#0 :: #1 :: nil).
Proof.
    admit.
Admitted.


Theorem entailment15 : forall s : state,
   realizeState ([~~ (convertToAbsExp A1)] ** invariant) nil s ->
   realizeState (finalState 0) nil s.
Proof.
    admit.
Admitted.


Theorem entailment16 : forall s : state,
   realizeState invariant nil s -> realizeState (finalState 0) nil s.
Proof.
    admit.
Admitted.




Theorem SatProgramWorks :
    exists x, {{(AbsClosure invariant ((!!clauses)::(!!assignments_to_do_head)::(!!stack)::(!!assignments)::(!!watches)::nil))}}Program{{(finalState x) return (#0::#1::nil) with (finalState x)}}.
Proof.
    unfold Program.
    eapply ex_intro.
    eapply strengthenPost.
    eapply compose.
    pcrunch.
    eapply while with (invariant := loopInvariant).  eapply sbasic.
    instantiate ( 1:= invariant).  

    eapply strengthenPost.
    pcrunch.
eapply preCond1. apply H0.


    eapply preCond2. apply (fun x => 0). apply H. apply H0.

    eapply while with (invariant := haveVarInvariant). eapply sbasic.  
    instantiate ( 1 := invariant ).

    eapply strengthenPost.
    pcrunch.
    apply mergeTheorem1.
    apply entailment1.

    intros. inversion H. intros. inversion H.

    apply entailment2. apply (fun x => 0, fun x => None).
    instantiate (1 := invariant).
    apply mergeTheorem2.
    eapply validRefTheorem1. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem2. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem3. apply (Id 0). apply n. apply H. apply H0.
    instantiate (1 := invariant).
    apply mergeTheorem3.

    (*eapply validRefTheorem4. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem5. apply (Id 0). apply n. apply H. apply H0.

    admit.

    eapply while with (invariant :=invariant). eapply sbasic.
    instantiate (1 := invariant). instantiate (1 := (#0::#1::nil)).
    eapply strengthenPost. pcrunch.



    eapply validRefTheorem7. apply (Id 0). apply n. apply H. apply H0.

    apply existsTheorem1.
    apply existsTheorem2.

    instantiate (1 := invariant).
    apply mergeTheorem4.

    eapply while with (invariant := invariantNoTail). eapply sbasic.
    eapply strengthenPost. pcrunch.
    eapply existsTheorem3.
    apply entailment3.

    intros. inversion H. intros. inversion H.
    apply entailment4.

    pcrunch.

    eapply while with (invariant := invariant). eapply sbasic.
    eapply strengthenPost. pcrunch.


    eapply validRefTheorem8. apply (Id 0). apply n. apply H. apply H0.
    apply existsTheorem4.
    apply entailment5.

    intros. inversion H.
    intros. inversion H.
    apply entailment6.
    eapply validRefTheorem9. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem10. apply (Id 0). apply n. apply H. apply H0.

    instantiate (1 := (#0::#1::nil)). instantiate (1 := (#0::#1::nil)).
    instantiate (1 := invariant). instantiate (1 := invariant).
    apply mergeReturn1.

    instantiate (1 := (#0::#1::nil)). instantiate (1 := (#0::#1::nil)).
    instantiate (1 := invariant). instantiate (1 := invariant).
    apply mergeReturn2.

    instantiate (1 := invariant).
    apply mergeTheorem5.
    eapply validRefTheorem11. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem12. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem13. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem14. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem15. apply (Id 0). apply n. apply H. apply H0.

    eapply while with (invariant := invariantWL). eapply sbasic.
    eapply strengthenPost. pcrunch.

    eapply while with (invariant := invariantWLIT1). eapply sbasic.
    eapply strengthenPost. pcrunch.

    instantiate (1 := invariantWLIT1).
    apply mergeTheorem6.

    instantiate (1 := invariantWLIT1).
    apply mergeTheorem7.

    instantiate (1 := invariantWLIT1).
    apply mergeTheorem8.

    intros. apply H.

    intros. inversion H.
    intros. inversion H.

    apply entailment7.
    eapply validRefTheorem16. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem17. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem18. apply (Id 0). apply n. apply H. apply H0.

    instantiate (1 := invariantWLIT1).
    apply mergeTheorem9.

    eapply validRefTheorem19. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem20. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem21. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem22. apply (Id 0). apply n. apply H. apply H0.

    instantiate (1 := invariantWLIT1).
    apply mergeTheorem10.

    eapply validRefTheorem23. apply (Id 0). apply n. apply H. apply H0.

    instantiate (1 := invariantWLIT1).
    apply mergeTheorem11.

    eapply while with (invariant := invariantWLIT2). eapply sbasic.
    eapply strengthenPost. pcrunch.

    instantiate (1 := invariantWLIT2).
    apply mergeTheorem12.

    instantiate (1 := invariantWLIT2).
    apply mergeTheorem13.

    instantiate (1 := invariantWLIT2).
    apply mergeTheorem14.

    apply entailment8.


    intros. inversion H.
    intros. inversion H.

    apply entailment9.

    eapply validRefTheorem24. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem25. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem26. apply (Id 0). apply n. apply H. apply H0.

    instantiate (1 := invariantWLIT2).
    apply mergeTheorem15.

    eapply validRefTheorem27. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem28. apply (Id 0). apply n. apply H. apply H0.
    eapply validRefTheorem29. apply (Id 0). apply n. apply H. apply H0.

    instantiate (1 := invariantWLIT1).
    apply mergeTheorem16.

    instantiate (1 := invariantWLIT1).
    apply mergeTheorem17.

    instantiate (1 := (#0)::(#1)::nil).
    instantiate (1 := (#0)::(#1)::nil).
    instantiate (1 := (#0)::(#1)::nil).
    instantiate (1 := invariant).
    instantiate (1 := invariant).
    instantiate (1 := invariant).
    apply mergeReturn3.

    instantiate (1 := invariantWL).
    apply mergeTheorem18.

    apply entailment10.

    intros. apply H.
    instantiate (1 := (#0::#1::nil)).
    apply equivEvalList1.

    apply entailment11.

    instantiate (1 := (#0)::(#1)::nil).
    instantiate (1 := invariant).
    apply mergeReturn4.
    instantiate (1 := invariant).
    apply mergeTheorem19.

    intros. apply H.
    intros. apply H.

    apply equivEvalList1.

    apply entailment12.

    instantiate (1 := (#0)::(#1)::nil). instantiate (1 := invariant).
    apply mergeReturn5.

    instantiate (1 := (#0)::(#1)::nil).
    instantiate (1 := (#0)::(#1)::nil).
    instantiate (1 := invariant).
    apply mergeReturn6.

    apply entailment13.

    intros. apply H.

    apply equivEvalList1.

    apply entailment14.

    instantiate (1 := (#0)::(#1)::nil).
    instantiate (1 := invariant).
    apply mergeReturn7. instantiate (1 := 0).

    apply entailment15.
    apply entailment16.
    intros. apply equivEvalList1. apply H. apply H.

    Grab Existential Variables.

    apply (nil).
    apply (nil).
    apply (nil).
    apply (nil).
    apply (nil).
    apply (nil).
    apply (nil).
    apply (nil).
    apply (nil).
    apply (nil).
    apply (nil).
    apply (nil).
    apply (nil).
    apply (nil).
    apply (nil).*)

    admit.
Admitted.








































