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
Opaque basicEval.

Theorem mergeTheorem1Aux9b : forall v v0 v1 v2 l v4 x x0 eee e x1 x2 x3,
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
        ([--( v(2), v(6) )---> (#2 ++++ v(7))] **
         ([nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #2] *\/*
          [nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #0]) *\/*
         [--( v(2), v(6) )---> (#6 ++++ v(7))] **
         ([nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #1] *\/*
          [nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #0]))
        (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
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
       true =
       validPredicate
         (@absEval unit eq_unit (@basicEval unit) eee
            (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
            (#0 ==== --( v(2), v(6) )---> (#10 ++++ !!(varx)))) ->
       @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
       ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: nil) 
          (eee, empty_heap) ->
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
       @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          (SUM(range(!!(varx) ++++ #1, #4),
           #0 <<<< --( v(2), v(6) )---> (#10 ++++ v(10)) //\\
           ((--( v(2), v(6) )---> (#2 ++++ v(10)) \\//
             --( v(2), v(6) )---> (#6 ++++ v(10))) //\\
            nth(v(4), v(10)) ==== #0), v(9)))
          (v
           :: v0
              :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)
          (eee, fun _ : nat => None) ->
       @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
  ([#1 ==== v(8) ++++ v(9)])
          (v
           :: v0
              :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)
          (eee, fun _ : nat => None) ->
       @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          (SUM(range(#0, #4),
           #0 <<<< --( v(2), v(6) )---> (#10 ++++ v(10)) //\\
           nth(v(4), v(10)) ==== #0, #1))
          (v
           :: v0
              :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)
          (eee, fun _ : nat => None) ->
       @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
         (((((([--( v(2), v(6) )---> (#10 ++++ !!(varx))] *\/*
               [--( v(2), v(6) )---> (#2 ++++ !!(varx)) ==== #0] **
               [--( v(2), v(6) )---> (#6 ++++ !!(varx)) ==== #0]) *\/*
              [~~ --( v(2), v(6) )---> (#10 ++++ v(9))]) *\/*
             [nth(replacenth(v(4), !!(varx), !!(valuex)), !!(varx)) ==== #0]) *\/*
            [nth(replacenth(v(4), !!(varx), !!(valuex)), v(9)) ==== #0]) *\/*
           [!!(varx) ==== v(9)]) *\/*
          ([!!(varx) ==== v(9)] ** [!!(varx) ==== (!!(varx))] *\/*
           AbsExists TreeRecords(v(0))
             ([!!(varx) ==== v(9)] **
              [nth(find(v(0), v(10)), #3) ==== (!!(varx))])) *\/*
          AbsExists TreeRecords(v(0))
            (AbsExists TreeRecords(find(v(0), v(10)))
               ([nth(find(v(0), v(10)), #3) ==== v(9)] **
                [nth(find(v(0), v(11)), #3) ==== (!!(varx))])))
         ((v
           :: v0
              :: v1
                 :: v2
                    :: ListValue l
                       :: v4 :: x :: x0 :: NatValue (eee varx) :: nil) ++
          x3 :: nil) (eee, empty_heap) ->
       @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
   ([#0 <<<< nth(v(4), v(8))])
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x3 :: nil)
          (eee, empty_heap) ->
       @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          ([#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8))])
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x3 :: nil)
          (eee, empty_heap) ->
    In x3 (NatValue 0 :: NatValue 1 :: NatValue 2 :: NatValue 3 :: nil) ->
    length l = 4 ->
       @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
  ([--( v(2), v(6) )---> (#2 ++++ !!(varx)) ==== #0] **
      [--( v(2), v(6) )---> (#6 ++++ !!(varx)) ==== #0])
     (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: nil) 
     (eee, empty_heap).
Proof.
    admit.
Qed.

