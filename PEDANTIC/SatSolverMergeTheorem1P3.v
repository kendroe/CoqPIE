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
Require Export SatSolverMergeTheorem1P1.
Require Export SatSolverMergeTheorem1P2.
Opaque basicEval.


Theorem mergeTheorem1Aux9 : forall v v0 v1 v2 l v4 x x0 eee e,
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
         ([--( v(2), v(6) )---> (#2 ++++ v(7))] **
          ([nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #2] *\/*
           [nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #0]) *\/*
          [--( v(2), v(6) )---> (#6 ++++ v(7))] **
          ([nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #1] *\/*
           [nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #0]))
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
         (eee, empty_heap) ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          (SUM(range(#0, #4), #0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8)),
           #2)) (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
          (eee, empty_heap) ->
        (forall x1 : Value,
        NatValue 0 = x1 \/
        NatValue 1 = x1 \/ NatValue 2 = x1 \/ NatValue 3 = x1 \/ False ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          (([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
            [--( v(2), v(6) )---> (#2 ++++ v(8))]) *\/*
           [--( v(2), v(6) )---> (#6 ++++ v(8))])
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: nil)
          (eee, empty_heap)) ->
       In x0 (NatValue 0 :: NatValue 1 :: NatValue 2 :: NatValue 3 :: nil) ->
       NatValue 0 = nth (eee varx) l NoValue ->
       e <> 0 ->
       NatValue e =
       (if match eee varx with
           | 0 => false
           | 1 => false
           | 2 => false
           | 3 => false
           | S (S (S (S _))) => true
           end
        then NatValue 0
        else @NatValue unit 1) ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          (SUM(range(#0, #4),
           (--( v(2), v(6) )---> (#2 ++++ v(8)) \\//
            --( v(2), v(6) )---> (#6 ++++ v(8))) //\\
           nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #0, 
           #1)) (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
          (eee, empty_heap) ->
        (forall x1 : Value,
         In x1 (NatValue 0 :: NatValue 1 :: NatValue 2 :: NatValue 3 :: nil) ->
         @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
         (AbsAll range(#0, #4)
                      (((((([--( v(2), v(6) )---> (#10 ++++ v(8))] *\/*
                            [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
                            [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0]) *\/*
                           [~~ --( v(2), v(6) )---> (#10 ++++ v(9))]) *\/*
                          [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                           #0]) *\/*
                         [nth(replacenth(v(4), !!(varx), !!(valuex)), v(9)) ====
                          #0]) *\/* [v(8) ==== v(9)]) *\/*
                       ([!!(varx) ==== v(9)] ** [!!(varx) ==== v(8)] *\/*
                        AbsExists TreeRecords(v(0))
                          ([!!(varx) ==== v(9)] **
                           [nth(find(v(0), v(10)), #3) ==== v(8)])) *\/*
                       AbsExists TreeRecords(v(0))
                         (AbsExists TreeRecords(find(v(0), v(10)))
                            ([nth(find(v(0), v(10)), #3) ==== v(9)] **
                             [nth(find(v(0), v(11)), #3) ==== v(8)]))))
          ((v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil) ++
           x1 :: nil) (eee, empty_heap)) ->
       (forall x1 : Value,
        In x1 (NatValue 0 :: NatValue 1 :: NatValue 2 :: NatValue 3 :: nil) ->
         @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          ([#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8))] **
           [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #0] *\/*
           [#0 <<<< nth(replacenth(v(4), !!(varx), !!(valuex)), v(8))] *\/*
           [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
           [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0])
          ((v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil) ++
           x1 :: nil) (eee, empty_heap)) ->
        (true =
         validPredicate
           (@absEval unit eq_unit (@basicEval unit) eee
              (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
              (#0 ==== --( v(2), v(6) )---> (#10 ++++ !!(varx))))) ->
         (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
         ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: nil) 
         (eee, empty_heap)) ->
         @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          (AbsAll range(#0, #4)
             ([nth(v(4), v(6)) ==== #0] *\/*
              [!!(varx) ==== v(6)] *\/*
              AbsExists TreeRecords(v(0))
                ([nth(find(v(0), v(7)), #3) ==== v(6)] **
                 [nth(find(v(0), v(7)), #4) ==== nth(v(4), v(6))])))
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: nil) 
          (eee, empty_heap) ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
       (AbsAll TreeRecords(v(0))
              ([~~ (!!(varx) ==== nth(find(v(0), v(6)), #3))]))
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: nil)
          (eee, empty_heap) ->
   length l = 4 ->
   @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
     ([--( v(2), v(6) )---> (#2 ++++ !!(varx)) ==== #0] **
      [--( v(2), v(6) )---> (#6 ++++ !!(varx)) ==== #0])
     (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: nil) 
     (eee, empty_heap).
Proof.
    admit.
Qed.

Theorem mergeTheorem1 : forall bbb eee hhh, length bbb=6 ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
       ((AbsEmpty **
           [#0 ==== nth(v(4), !!(varx))] **
           AbsEmpty **
           [!!(stack) ==== (!!(ssss))] **
           [!!(ssss) ==== nth(v(0), #0)] **
           AbsEmpty **
           [!!(backtrack) ==== #0] **
           [v(1)] **
           AbsEmpty **
           AbsEmpty **
           AbsEmpty **
           (([!!(varx) <<<< #4] ** AbsEmpty) **
            (([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2]) ** AbsEmpty) **
            AbsEmpty **
            AbsAll TreeRecords(v(0))
              ([~~ (!!(varx) ==== nth(find(v(0), v(6)), #3))]) ** AbsEmpty) **
           AbsAll range(#0, #4)
             ([nth(v(4), v(6)) ==== #0] *\/*
              [!!(varx) ==== v(6)] *\/*
              AbsExists TreeRecords(v(0))
                ([nth(find(v(0), v(7)), #3) ==== v(6)] **
                 [nth(find(v(0), v(7)), #4) ==== nth(v(4), v(6))])) **
           AbsEmpty **
           AbsEmpty **
           AbsAll TreeRecords(v(2))
             (AbsExists range(#0, #4)
                (([--( v(2), v(6) )---> (#2 ++++ v(7))] **
                  ([nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #2] *\/*
                   [nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #0]) *\/*
                  [--( v(2), v(6) )---> (#6 ++++ v(7))] **
                  ([nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #1] *\/*
                   [nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #0])) **
                 AbsAll range(#0, #4)
                   (([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
                     [--( v(2), v(6) )---> (#2 ++++ v(8))]) *\/*
                    [--( v(2), v(6) )---> (#6 ++++ v(8))]) **
                 AbsAll range(#0, #4)
                   ([#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8))] **
                    ([#0 <<<< --( v(2), v(6) )---> (#18 ++++ v(8))] *\/*
                     [nth(v(5), v(8)) ==== v(6)]) *\/*
                    ([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] **
                     [--( v(2), v(6) )---> (#18 ++++ v(8)) ==== #0]) **
                    [~~ nth(v(5), v(8)) ==== v(6)]) **
                 SUM(range(#0, #4),
                 #0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8)), 
                 #2) **
                 (SUM(range(#0, #4),
                  (--( v(2), v(6) )---> (#2 ++++ v(8)) \\//
                   --( v(2), v(6) )---> (#6 ++++ v(8))) //\\
                  nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #0,
                  #1) **
                  AbsAll range(#0, #4)
                    ([#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8))] **
                     [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                      #0] *\/*
                     [#0 <<<<
                      nth(replacenth(v(4), !!(varx), !!(valuex)), v(8))] *\/*
                     [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
                     [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0]) **
                  AbsAll range(#0, #4)
                    (AbsAll range(#0, #4)
                       (((((([--( v(2), v(6) )---> (#10 ++++ v(8))] *\/*
                             [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
                             [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0]) *\/*
                            [~~ --( v(2), v(6) )---> (#10 ++++ v(9))]) *\/*
                           [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                            #0]) *\/*
                          [nth(replacenth(v(4), !!(varx), !!(valuex)), v(9)) ====
                           #0]) *\/* [v(8) ==== v(9)]) *\/*
                        ([!!(varx) ==== v(9)] ** [!!(varx) ==== v(8)] *\/*
                         AbsExists TreeRecords(v(0))
                           ([!!(varx) ==== v(9)] **
                            [nth(find(v(0), v(10)), #3) ==== v(8)])) *\/*
                        AbsExists TreeRecords(v(0))
                          (AbsExists TreeRecords(find(v(0), v(10)))
                             ([nth(find(v(0), v(10)), #3) ==== v(9)] **
                              [nth(find(v(0), v(11)), #3) ==== v(8)])))) *\/*
                  AbsExists range(#0, #4)
                    (([--( v(2), v(6) )---> (#2 ++++ v(8))] **
                      [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                       #2] *\/*
                      [--( v(2), v(6) )---> (#6 ++++ v(8))] **
                      [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                       #1]) **
                     AbsAll range(#0, #4)
                       (([#0 ====
                          nth(replacenth(v(4), !!(varx), !!(valuex)), v(9))] *\/*
                         [--( v(2), v(6) )---> (#10 ++++ v(9)) ==== #0] **
                         [#0 <<<<
                          nth(replacenth(v(4), !!(varx), !!(valuex)), v(9))]) *\/*
                        ([!!(varx) ==== v(9)] **
                         ([#0 <<<< --( v(2), v(6) )---> (#2 ++++ !!(varx))] **
                          [!!(valuex) ==== #2] *\/*
                          [#0 <<<< --( v(2), v(6) )---> (#6 ++++ !!(varx))] **
                          [!!(valuex) ==== #1]) *\/*
                         AbsExists TreeRecords(v(0))
                           ([!!(varx) ==== v(9)] **
                            ([#0 <<<<
                              --( v(2), v(6)
                              )---> (#2 ++++ nth(find(v(0), v(10)), #3))] **
                             [nth(find(v(0), v(10)), #4) ==== #2] *\/*
                             [#0 <<<<
                              --( v(2), v(6)
                              )---> (#6 ++++ nth(find(v(0), v(10)), #3))] **
                             [nth(find(v(0), v(10)), #4) ==== #1]))) *\/*
                        AbsExists TreeRecords(v(0))
                          (AbsExists TreeRecords(find(v(0), v(10)))
                             ([nth(find(v(0), v(10)), #3) ==== v(9)] **
                              ([#0 <<<<
                                --( v(2), v(6)
                                )---> (#2 ++++ nth(find(v(0), v(11)), #3))] **
                               [nth(find(v(0), v(11)), #4) ==== #2] *\/*
                               [#0 <<<<
                                --( v(2), v(6)
                                )---> (#6 ++++ nth(find(v(0), v(11)), #3))] **
                               [nth(find(v(0), v(11)), #4) ==== #1]))))) *\/*
                  AbsAll range(#0, #4)
                    ([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
                     [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                      #0]))))) **
          (AbsEach range(#0, #4)
             (AbsExistsT
                (Path(nth(v(5), v(6)), v(2), v(7), #21, #14 ++++ v(6) :: nil) **
                 AbsAll TreeRecords(v(7))
                   ([--( nth(v(5), v(6)), v(8) )---> (#18 ++++ v(6)) ==== #0] **
                    [nth(v(5), v(6)) ==== v(7)] *\/*
                    [--( v(7), --( v(7), v(8) )---> (#18 ++++ v(6))
                     )---> (#14 ++++ v(6)) ==== v(8)]))) **
           AbsAll TreeRecords(v(3))
             ([nth(find(v(3), !!(assignments_to_do_head)), #3) ==== #0] **
              [!!(assignments_to_do_head) ==== v(6)] *\/*
              [nth(find(v(3), v(6)), #3) inTree v(3)] **
              [nth(find(v(3), nth(find(v(3), v(6)), #3)), #2) ==== v(6)]) **
           AbsAll TreeRecords(v(0))
             (AbsAll TreeRecords(nth(find(v(0), v(6)), #2))
                ([~~
                  nth(find(v(0), v(6)), #3) ====
                  nth(find(nth(find(v(0), v(6)), #2), v(7)), #3)])) **
           AbsAll TreeRecords(v(0))
             ([nth(v(4), nth(find(v(0), v(6)), #3)) ====
               nth(find(v(0), v(6)), #4)]) **
           AbsAll TreeRecords(v(0))
             ([nth(find(v(0), v(6)), #4) ==== #1] *\/*
              [nth(find(v(0), v(6)), #4) ==== #2]) **
           AbsAll TreeRecords(v(0)) ([nth(find(v(0), v(6)), #3) <<<< #4]) **
           ARRAY(!!(watches), #4, v(5)) **
           TREE(!!(assignments_to_do_head), v(3), #4, #1 :: nil) **
           TREE(!!(clauses), v(2), #21, #1 :: nil) **
           TREE(!!(stack), v(0), #4, #1 :: nil) **
           [#1 ==== #1] ** ARRAY(!!(assignments), #4, v(4)) ** AbsEmpty) **
          build_equivs
            ((!!(stack) :: (!!(ssss)) :: nth(v(0), #0) :: nil)
             :: (!!(have_var) :: #1 :: nil)
                :: (nth(v(4), (!!(varx))) :: (!!(backtrack)) :: #0 :: nil) :: nil))
         bbb (eee, hhh) ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
    (AbsAll TreeRecords(v(2))
        (AbsExists range(#0, #4)
           (([--( v(2), v(6) )---> (#2 ++++ v(7))] **
             ([nth(v(4), v(7)) ==== #2] *\/* [nth(v(4), v(7)) ==== #0]) *\/*
             [--( v(2), v(6) )---> (#6 ++++ v(7))] **
             ([nth(v(4), v(7)) ==== #1] *\/* [nth(v(4), v(7)) ==== #0])) **
            AbsAll range(#0, #4)
              (([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
                [--( v(2), v(6) )---> (#2 ++++ v(8))]) *\/*
               [--( v(2), v(6) )---> (#6 ++++ v(8))]) **
            AbsAll range(#0, #4)
              ([#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8))] **
               ([#0 <<<< --( v(2), v(6) )---> (#18 ++++ v(8))] *\/*
                [nth(v(5), v(8)) ==== v(6)]) *\/*
               ([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] **
                [--( v(2), v(6) )---> (#18 ++++ v(8)) ==== #0]) **
               [~~ nth(v(5), v(8)) ==== v(6)]) **
            SUM(range(#0, #4), #0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8)),
            #2) **
            (SUM(range(#0, #4),
             (--( v(2), v(6) )---> (#2 ++++ v(8)) \\//
              --( v(2), v(6) )---> (#6 ++++ v(8))) //\\
             nth(v(4), v(8)) ==== #0, #1) **
             AbsAll range(#0, #4)
               ([#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8))] **
                [nth(v(4), v(8)) ==== #0] *\/*
                [#0 <<<< nth(v(4), v(8))] *\/*
                [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
                [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0]) **
             AbsAll range(#0, #4)
               (AbsAll range(#0, #4)
                  (((((([--( v(2), v(6) )---> (#10 ++++ v(8))] *\/*
                        [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
                        [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0]) *\/*
                       [~~ --( v(2), v(6) )---> (#10 ++++ v(9))]) *\/*
                      [nth(v(4), v(8)) ==== #0]) *\/*
                     [nth(v(4), v(9)) ==== #0]) *\/* 
                    [v(8) ==== v(9)]) *\/*
                   AbsExists TreeRecords(v(0))
                     (AbsExists TreeRecords(find(v(0), v(10)))
                        ([nth(find(v(0), v(10)), #3) ==== v(9)] **
                         [nth(find(v(0), v(11)), #3) ==== v(8)])))) *\/*
             AbsExists range(#0, #4)
               (([--( v(2), v(6) )---> (#2 ++++ v(8))] **
                 [nth(v(4), v(8)) ==== #2] *\/*
                 [--( v(2), v(6) )---> (#6 ++++ v(8))] **
                 [nth(v(4), v(8)) ==== #1]) **
                AbsAll range(#0, #4)
                  (([#0 ==== nth(v(4), v(9))] *\/*
                    [--( v(2), v(6) )---> (#10 ++++ v(9)) ==== #0] **
                    [#0 <<<< nth(v(4), v(9))]) *\/*
                   AbsExists TreeRecords(v(0))
                     (AbsExists TreeRecords(find(v(0), v(10)))
                        ([nth(find(v(0), v(10)), #3) ==== v(9)] **
                         ([#0 <<<<
                           --( v(2), v(6)
                           )---> (#2 ++++ nth(find(v(0), v(11)), #3))] **
                          [nth(find(v(0), v(11)), #4) ==== #2] *\/*
                          [#0 <<<<
                           --( v(2), v(6)
                           )---> (#6 ++++ nth(find(v(0), v(11)), #3))] **
                          [nth(find(v(0), v(11)), #4) ==== #1]))))) *\/*
             AbsAll range(#0, #4)
               ([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
                [nth(v(4), v(8)) ==== #0]))))) bbb (eee,empty_heap).
Proof.
    intros.

    assert(@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) (AbsAll TreeRecords(v(2))
             (AbsExists range(#0, #4)
                (([--( v(2), v(6) )---> (#2 ++++ v(7))] **
                  ([nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #2] *\/*
                   [nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #0]) *\/*
                  [--( v(2), v(6) )---> (#6 ++++ v(7))] **
                  ([nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #1] *\/*
                   [nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #0])) **
                 AbsAll range(#0, #4)
                   (([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
                     [--( v(2), v(6) )---> (#2 ++++ v(8))]) *\/*
                    [--( v(2), v(6) )---> (#6 ++++ v(8))]) **
                 AbsAll range(#0, #4)
                   ([#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8))] **
                    ([#0 <<<< --( v(2), v(6) )---> (#18 ++++ v(8))] *\/*
                     [nth(v(5), v(8)) ==== v(6)]) *\/*
                    ([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] **
                     [--( v(2), v(6) )---> (#18 ++++ v(8)) ==== #0]) **
                    [~~ nth(v(5), v(8)) ==== v(6)]) **
                 SUM(range(#0, #4),
                 #0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8)), 
                 #2) **
                 (SUM(range(#0, #4),
                  (--( v(2), v(6) )---> (#2 ++++ v(8)) \\//
                   --( v(2), v(6) )---> (#6 ++++ v(8))) //\\
                  nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #0,
                  #1) **
                  AbsAll range(#0, #4)
                    ([#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8))] **
                     [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                      #0] *\/*
                     [#0 <<<<
                      nth(replacenth(v(4), !!(varx), !!(valuex)), v(8))] *\/*
                     [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
                     [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0]) **
                  AbsAll range(#0, #4)
                    (AbsAll range(#0, #4)
                       (((((([--( v(2), v(6) )---> (#10 ++++ v(8))] *\/*
                             [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
                             [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0]) *\/*
                            [~~ --( v(2), v(6) )---> (#10 ++++ v(9))]) *\/*
                           [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                            #0]) *\/*
                          [nth(replacenth(v(4), !!(varx), !!(valuex)), v(9)) ====
                           #0]) *\/* [v(8) ==== v(9)]) *\/*
                        ([!!(varx) ==== v(9)] ** [!!(varx) ==== v(8)] *\/*
                         AbsExists TreeRecords(v(0))
                           ([!!(varx) ==== v(9)] **
                            [nth(find(v(0), v(10)), #3) ==== v(8)])) *\/*
                        AbsExists TreeRecords(v(0))
                          (AbsExists TreeRecords(find(v(0), v(10)))
                             ([nth(find(v(0), v(10)), #3) ==== v(9)] **
                              [nth(find(v(0), v(11)), #3) ==== v(8)])))) *\/*
                  AbsExists range(#0, #4)
                    (([--( v(2), v(6) )---> (#2 ++++ v(8))] **
                      [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                       #2] *\/*
                      [--( v(2), v(6) )---> (#6 ++++ v(8))] **
                      [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                       #1]) **
                     AbsAll range(#0, #4)
                       (([#0 ====
                          nth(replacenth(v(4), !!(varx), !!(valuex)), v(9))] *\/*
                         [--( v(2), v(6) )---> (#10 ++++ v(9)) ==== #0] **
                         [#0 <<<<
                          nth(replacenth(v(4), !!(varx), !!(valuex)), v(9))]) *\/*
                        ([!!(varx) ==== v(9)] **
                         ([#0 <<<< --( v(2), v(6) )---> (#2 ++++ !!(varx))] **
                          [!!(valuex) ==== #2] *\/*
                          [#0 <<<< --( v(2), v(6) )---> (#6 ++++ !!(varx))] **
                          [!!(valuex) ==== #1]) *\/*
                         AbsExists TreeRecords(v(0))
                           ([!!(varx) ==== v(9)] **
                            ([#0 <<<<
                              --( v(2), v(6)
                              )---> (#2 ++++ nth(find(v(0), v(10)), #3))] **
                             [nth(find(v(0), v(10)), #4) ==== #2] *\/*
                             [#0 <<<<
                              --( v(2), v(6)
                              )---> (#6 ++++ nth(find(v(0), v(10)), #3))] **
                             [nth(find(v(0), v(10)), #4) ==== #1]))) *\/*
                        AbsExists TreeRecords(v(0))
                          (AbsExists TreeRecords(find(v(0), v(10)))
                             ([nth(find(v(0), v(10)), #3) ==== v(9)] **
                              ([#0 <<<<
                                --( v(2), v(6)
                                )---> (#2 ++++ nth(find(v(0), v(11)), #3))] **
                               [nth(find(v(0), v(11)), #4) ==== #2] *\/*
                               [#0 <<<<
                                --( v(2), v(6)
                                )---> (#6 ++++ nth(find(v(0), v(11)), #3))] **
                               [nth(find(v(0), v(11)), #4) ==== #1]))))) *\/*
                  AbsAll range(#0, #4)
                    ([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
                     [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                      #0]))))) bbb (eee,empty_heap)).
        solvePickTerm H0.

        assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) ([#0 ==== nth(v(4), !!(varx))]) bbb (eee,empty_heap)). solvePickTerm H0.

        assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) ([!!(varx) <<<< #4]) bbb (eee,empty_heap)). solvePickTerm H0.

        destruct_bindings. simpl.

        Transparent basicEval.
        destructState.
        eapply RSAll. simpl. reflexivity. simpl. rewrite H6. reflexivity.
        Opaque basicEval.

        intros. assert (In x rl). apply H. apply H9 in H1. clear H9.
        Transparent basicEval.
        destructState. hypSimp. destruct v3; inversion H7; subst; clear H7; hypSimp. Opaque basicEval.
        remember (nth (eee varx) l NoValue). destruct y; inversion HeqH7; subst; clear HeqH7.
        Transparent basicEval.
        destruct n0; inversion H1; subst; clear H1; hypSimp. Opaque basicEval. Focus 2. elim H3. reflexivity.

        eapply RSExists. simpl. reflexivity. Transparent basicEval. simpl. reflexivity. Opaque basicEval.
        eapply ex_intro.
        split. apply H2. simpl. simpl in H11. simpl in H19. simpl in H17.
        simpl in H9.

        Transparent basicEval.

        inversion H8; subst; clear H8.

        eapply RSCompose.

        eapply mergeTheorem1Aux5.
            apply H9. apply H2. apply H7. apply H1. apply Heqy.


        Focus 2. apply concreteComposeEmpty. split. reflexivity. reflexivity.

        eapply RSCompose. eapply RSAll. simpl. reflexivity. Transparent basicEval. reflexivity. Opaque basicEval.
        intros. simpl in H8. apply H17 in H8. apply H8.

        Focus 2. apply concreteComposeEmpty. split. reflexivity. reflexivity.

        eapply RSCompose. eapply RSAll. simpl. reflexivity. Transparent basicEval. reflexivity. Opaque basicEval.
        intros. simpl in H8. apply H19 in H8. apply H8.

        Focus 2. apply concreteComposeEmpty. split. reflexivity. reflexivity.

        eapply RSCompose. apply H4.

        Focus 2. apply concreteComposeEmpty. split. reflexivity. reflexivity.

        inversion H11. subst. clear H11.

        Transparent basicEval. destructState.
        hypSimp. Opaque basicEval.
        (*remember (beq_nat 0 match (nth (10+(eee varx)) (match (@findRecord unit (match v1 with | NatValue z => z | _ => 0 end) x) with | ListValue l => l | _ => nil end) NoValue) with | NatValue x => x | _ => 1 end).*)
        remember (validPredicate (@absEval unit eq_unit (@basicEval unit) eee (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil) (#0 ==== --( v(2), v(6) )---> (#10 ++++ !!varx)))).
        destruct b.

        eapply RSOrComposeL.
        eapply RSCompose.

        Focus 3. apply concreteComposeEmpty. split. reflexivity. reflexivity.

        assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
            ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
            (v::v0::v1::v2::ListValue l::v4::nil) (eee, empty_heap)). solvePickTerm H0.

        assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
             (AbsAll range(#0, #4)
             ([nth(v(4), v(6)) ==== #0] *\/*
              [!!(varx) ==== v(6)] *\/*
              AbsExists TreeRecords(v(0))
                ([nth(find(v(0), v(7)), #3) ==== v(6)] **
                 [nth(find(v(0), v(7)), #4) ==== nth(v(4), v(6))])))
            (v::v0::v1::v2::ListValue l::v4::nil) (eee, empty_heap)). solvePickTerm H0.

        assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
                ([--( v(2), v(6) )--->(#2 ++++ (!!varx))====#0] **
                 [--( v(2), v(6) )--->(#6 ++++ (!!varx))====#0])
            (v::v0::v1::v2::ListValue l::v4::x::nil) (eee, empty_heap)). eapply mergeTheorem1Aux9.
            apply H9. apply H4. apply H17. apply H2. apply Heqy. apply H7. apply H1. apply H12.
            apply H22. apply H21. apply Heqb. apply H8. apply H11.
            solvePickTerm H0.
            assert (exists hh, @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) (ARRAY(!!(assignments), #4, v(4)))  (v::v0::v1::v2::ListValue l::v4::nil) (eee, hh)).
            solvePickData H0. inversion H13. subst. clear H13.
            eapply arrayLength. apply H14. simpl. reflexivity.

        eapply mergeTheorem1Aux1. apply H12. apply H21. apply Heqb. apply H8.
            destruct (eee varx). simpl. reflexivity.
            destruct n. reflexivity. destruct n. reflexivity. destruct n. reflexivity.
            inversion H1. subst. elim H7. reflexivity.
            assert (exists hh, @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) (ARRAY(!!(assignments), #4, v(4)))  (v::v0::v1::v2::ListValue l::v4::nil) (eee, hh)).
            solvePickData H0. inversion H14. subst. clear H14.
            eapply arrayLength. apply H15. simpl. reflexivity.
            apply Heqy. apply H13.

        eapply RSCompose.
        Focus 3. apply concreteComposeEmpty. split. reflexivity. reflexivity.

        eapply RSAll. simpl. reflexivity. Transparent basicEval. simpl. reflexivity. Opaque basicEval. intros. eapply H21 in H8.

        simpl. eapply mergeTheorem1Aux2. apply Heqb. apply H8. apply Heqy.

        assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
            ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
            (v::v0::v1::v2::ListValue l::v4::nil) (eee, empty_heap)). solvePickTerm H0. apply H11.
            assert (exists hh, @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) (ARRAY(!!(assignments), #4, v(4)))  (v::v0::v1::v2::ListValue l::v4::nil) (eee, hh)).
            solvePickData H0. inversion H11. subst. clear H11.
            eapply arrayLength. apply H13. simpl. reflexivity.
           assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
                ([--( v(2), v(6) )--->(#2 ++++ (!!varx))====#0] **
                 [--( v(2), v(6) )--->(#6 ++++ (!!varx))====#0])
            (v::v0::v1::v2::ListValue l::v4::x::nil) (eee, empty_heap)). eapply mergeTheorem1Aux9.
            apply H9. apply H4. apply H17. apply H2. apply Heqy. apply H7. apply H1. apply H12.
            apply H22. apply H21. apply Heqb.
        assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
            ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
            (v::v0::v1::v2::ListValue l::v4::nil) (eee, empty_heap)). solvePickTerm H0.
           apply H11.
        assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
             (AbsAll range(#0, #4)
             ([nth(v(4), v(6)) ==== #0] *\/*
              [!!(varx) ==== v(6)] *\/*
              AbsExists TreeRecords(v(0))
                ([nth(find(v(0), v(7)), #3) ==== v(6)] **
                 [nth(find(v(0), v(7)), #4) ==== nth(v(4), v(6))])))
            (v::v0::v1::v2::ListValue l::v4::nil) (eee, empty_heap)). solvePickTerm H0.
        apply H11.
            solvePickTerm H0.
            assert (exists hh, @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) (ARRAY(!!(assignments), #4, v(4)))  (v::v0::v1::v2::ListValue l::v4::nil) (eee, hh)).
            solvePickData H0. inversion H11. subst. clear H11.
            eapply arrayLength. apply H13. simpl. reflexivity.
apply H11.


        eapply RSAll. simpl. reflexivity. Transparent basicEval. simpl. reflexivity. Opaque basicEval. intros. eapply H22 in H8. clear H22.

        inversion H8. subst. clear H8. Transparent basicEval. simpl in H15. inversion H15. subst. clear H15.
        Opaque basicEval. simpl in H20.
        eapply RSAll. simpl. reflexivity. Transparent basicEval. reflexivity. Opaque basicEval. intros. simpl in H8. eapply H20 in H8. clear H20. simpl.

        assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
            ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
            (v::v0::v1::v2::ListValue l::v4::nil) (eee, empty_heap)). solvePickTerm H0.

        eapply mergeTheorem1Aux3.
            destruct (eee varx). reflexivity. destruct n. reflexivity. destruct n. reflexivity.
            destruct n. reflexivity. inversion H1. subst. elim H7. reflexivity.
            apply Heqy. apply Heqb. apply H8.
            assert (exists hh, @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) (ARRAY(!!(assignments), #4, v(4)))  (v::v0::v1::v2::ListValue l::v4::nil) (eee, hh)).
            solvePickData H0. inversion H13. subst. clear H13.
            eapply arrayLength. apply H14. simpl. reflexivity.
            apply H11.

        eapply RSOrComposeR. eapply RSOrComposeR.

        assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
            ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
            (v::v0::v1::v2::ListValue l::v4::nil) (eee, empty_heap)). solvePickTerm H0.
      
        eapply mergeTheorem1Aux4.
            apply H4.
            simpl. apply H17.
            apply H2.
            destruct (eee varx). reflexivity. destruct n. reflexivity. destruct n. reflexivity.
            destruct n. reflexivity. inversion H1. subst. clear H1. elim H7. reflexivity.
            apply Heqy. apply H12. apply H22. apply H21. apply Heqb. apply H8.
            assert (exists hh, @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) (ARRAY(!!(assignments), #4, v(4)))  (v::v0::v1::v2::ListValue l::v4::nil) (eee, hh)).
            solvePickData H0. inversion H11. subst. clear H11.
            eapply arrayLength. apply H13. simpl. reflexivity.

        subst. clear H11.

        inversion H15. subst. clear H15.
 
        eapply RSOrComposeR.

        remember (@mapSum unit eq_unit (@basicEval unit) eee (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil) (NatValue 0::NatValue 1::NatValue 2::NatValue 3::nil) 
             ((--( v(2), v(6) )---> (#2 ++++ v(8)) //\\ nth(v(4), v(8)) ==== #2) \\//
              (--( v(2), v(6) )---> (#6 ++++ v(8)) //\\ nth(v(4), v(8)) ==== #1))).

        destruct n.

        eapply RSOrComposeR.

        assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
            ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
            (v::v0::v1::v2::ListValue l::v4::nil) (eee, empty_heap)). solvePickTerm H0.

            eapply mergeTheorem1Aux7.
            apply H9. apply H4. apply H17. apply H2. apply Heqy. apply H7. apply H1. apply H14.
            apply Heqn. apply H8.
            assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
                (AbsAll TreeRecords(v(0)) ([nth(find(v(0), v(6)), #3) <<<< #4]))
                (v::v0::v1::v2::ListValue l::v4::nil) (eee, empty_heap)). solvePickTerm H0.
            simpl.
            eapply dumpVar2. instantiate (2 := 6). Focus 2. simpl. reflexivity. Focus 2. simpl.
            reflexivity. simpl.
            eapply dumpVar2. instantiate (2 := 6). Focus 2. simpl. reflexivity. Focus 2. simpl.
            reflexivity. simpl.
            inversion H11. subst. clear H11.
            Transparent basicEval. simpl in H16. Opaque basicEval.
            eapply RSAll. Transparent basicEval. simpl. reflexivity. apply H16.
            intros. apply H21 in H11. simpl in H11. simpl. apply H11.
            assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
                (AbsAll TreeRecords(v(0))
             ([nth(v(4), nth(find(v(0), v(6)), #3)) ====
               nth(find(v(0), v(6)), #4)]))
                (v::v0::v1::v2::ListValue l::v4::nil) (eee, empty_heap)). solvePickTerm H0.
            simpl.
            eapply dumpVar2. instantiate (2 := 6). Focus 2. simpl. reflexivity. Focus 2. simpl.
            reflexivity. simpl.
            eapply dumpVar2. instantiate (2 := 6). Focus 2. simpl. reflexivity. Focus 2. simpl.
            reflexivity. simpl.
            inversion H11. subst. clear H11.
            Transparent basicEval. simpl in H16. Opaque basicEval.
            eapply RSAll. Transparent basicEval. simpl. reflexivity. apply H16.
            intros. apply H21 in H11. simpl in H11. simpl. apply H11.

        eapply RSOrComposeL.
      
        assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
            ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
            (v::v0::v1::v2::ListValue l::v4::nil) (eee, empty_heap)). solvePickTerm H0.

        eapply mergeTheorem1Aux8.
            apply H9. apply H4. apply H17. apply H2. apply Heqy. apply H7. apply H1. apply H14.
            apply Heqn. apply H8.

        eapply RSOrComposeR. eapply RSOrComposeR.
        subst. clear H15. 
        assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
            ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
            (v::v0::v1::v2::ListValue l::v4::nil) (eee, empty_heap)). solvePickTerm H0.

        eapply mergeTheorem1Aux6.
            apply H2. apply H7. apply H1. apply  Heqy. apply H14. apply H8.
            assert (exists hh, @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) (ARRAY(!!(assignments), #4, v(4)))  (v::v0::v1::v2::ListValue l::v4::nil) (eee, hh)).
            solvePickData H0. inversion H11. subst. clear H11.
            eapply arrayLength. apply H12. simpl. reflexivity.
Qed.

