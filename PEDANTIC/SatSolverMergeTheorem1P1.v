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
Opaque basicEval.

Set Printing Depth 200.

Theorem mergeTheorem1Aux8 : forall eee v v0 v1 v2 l v4 x x0 e n,
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
          (AbsExists range(#0, #4)
             (([--( v(2), v(6) )---> (#2 ++++ v(8))] **
               [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #2] *\/*
               [--( v(2), v(6) )---> (#6 ++++ v(8))] **
               [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #1]) **
              AbsAll range(#0, #4)
                (([#0 ==== nth(replacenth(v(4), !!(varx), !!(valuex)), v(9))] *\/*
                  [--( v(2), v(6) )---> (#10 ++++ v(9)) ==== #0] **
                  [#0 <<<< nth(replacenth(v(4), !!(varx), !!(valuex)), v(9))]) *\/*
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
                        [nth(find(v(0), v(11)), #4) ==== #1]))))))
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
          (eee, empty_heap) ->
  (S n = @mapSum unit eq_unit (@basicEval unit) eee
           (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
           (@NatValue unit 0 :: NatValue 1 :: NatValue 2 :: NatValue 3 :: nil)
           (--( v(2), v(6) )---> (#2 ++++ v(8)) //\\ nth(v(4), v(8)) ==== #2 \\//
           --( v(2), v(6) )---> (#6 ++++ v(8)) //\\ nth(v(4), v(8)) ==== #1)) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
       ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: nil) 
         (eee, empty_heap) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
     (AbsExists range(#0, #4)
        (([--( v(2), v(6) )---> (#2 ++++ v(8))] ** [nth(v(4), v(8)) ==== #2] *\/*
          [--( v(2), v(6) )---> (#6 ++++ v(8))] ** [nth(v(4), v(8)) ==== #1]) **
         AbsAll range(#0, #4)
           (([#0 ==== nth(v(4), v(9))] *\/*
             [--( v(2), v(6) )---> (#10 ++++ v(9)) ==== #0] **
             [#0 <<<< nth(v(4), v(9))]) *\/*
            AbsExists TreeRecords(v(0))
              (AbsExists TreeRecords(find(v(0), v(10)))
                 ([nth(find(v(0), v(10)), #3) ==== v(9)] **
                  ([#0 <<<<
                    --( v(2), v(6) )---> (#2 ++++ nth(find(v(0), v(11)), #3))] **
                   [nth(find(v(0), v(11)), #4) ==== #2] *\/*
                   [#0 <<<<
                    --( v(2), v(6) )---> (#6 ++++ nth(find(v(0), v(11)), #3))] **
                   [nth(find(v(0), v(11)), #4) ==== #1]))))))
     (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
     (eee, empty_heap).
Proof.
    intros.

    inversion H6. subst. clear H6. inversion H15. subst. clear H15. inversion H6. subst. clear H6.
    Transparent basicEval. simpl in H12. Opaque basicEval. inversion H12. subst. clear H12.

    inversion H10. subst. clear H10.
    eapply concreteComposeEmpty in H16. inversion H16. subst. clear H16.
    simpl in H12. simpl in H13.
    inversion H13. subst. clear H13.
    Transparent basicEval. simpl in H14. Opaque basicEval. inversion H14. subst. clear H14.

    eapply mapSumExists in H7.
    inversion H7. subst. clear H7.
    inversion H6. subst. clear H6.
    simplifyHyp H10. simplifyHyp H10.

    eapply RSExists. Transparent basicEval. simpl. Opaque basicEval. reflexivity. reflexivity.
    eapply ex_intro. split. apply H7.

    eapply RSCompose.
    Focus 3. eapply concreteComposeEmpty. split. reflexivity. reflexivity.

    simpl. apply H10.

    simpl in H17.

    eapply RSAll. Transparent basicEval. simpl. Opaque basicEval. reflexivity. reflexivity.
    intros. simpl. apply H17 in H6.

    destruct x3; hypSimp.
    remember (beq_nat n0 (eee varx)).
    destruct b.

    eapply RSOrComposeL. eapply RSOrComposeL.
    eapply RSR. Transparent basicEval. simpl. Opaque basicEval.
    apply beq_nat_eq in Heqb. subst.
    rewrite <- H3. reflexivity.

    apply BTStatePredicate. omega. unfold empty_heap. reflexivity.

    eapply removeReplace in H6. Focus 2. instantiate (1 := !!varx). instantiate (1 := v(9)).
    instantiate (1 := (v
          :: v0
             :: v1
                :: v2
                   :: ListValue l
                      :: v4 :: x :: x0 :: x1 :: NatValue n0 :: nil)). instantiate (1 := eee).
    Transparent basicEval. simpl. rewrite <- Heqb. simpl. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. reflexivity. Focus 2. simpl. reflexivity.

    inversion H6. subst. clear H6.
    eapply RSOrComposeL.
    eapply dumpVar in H16. Focus 2. instantiate (1 := 8). simpl. reflexivity.
    Focus 2. simpl. reflexivity. simpl in H16.
    eapply dumpVar2. Focus 2. instantiate (1 := 8). simpl. reflexivity.
    Focus 2. simpl. reflexivity. simpl.
    apply H16.

    subst. clear H6.
    inversion H16. subst. clear H16.
    inversion H15. subst. clear H15.
    inversion H16. subst. clear H16.
    apply concreteComposeEmpty in H19. inversion H19. subst. clear H19.
    apply RSOrComposeL. apply RSOrComposeL.

    inversion H13. subst. clear H13.
    Transparent basicEval. simpl in H19. Opaque basicEval.
    remember (beq_nat (eee varx) n0). destruct b. apply beq_nat_eq in Heqb0. subst.
    rewrite <- beq_nat_refl in Heqb. inversion Heqb.
    inversion H19. elim H11. reflexivity.
    subst.
    inversion H16. subst. clear H16.
    inversion H20. subst. clear H20.
    inversion H6. subst. clear H6.
    inversion H13. subst. clear H13.
    eapply concreteComposeEmpty in H22. inversion H22. subst. clear H22.
    inversion H18. subst. clear H18.
    Transparent basicEval. simpl in H22. Opaque basicEval.
    remember (beq_nat (eee varx) n0).
    destruct b. eapply beq_nat_eq in Heqb0. subst. rewrite <- beq_nat_refl in Heqb. inversion Heqb.
    inversion H22. subst. clear H22. elim H13. reflexivity.

    subst. eapply RSOrComposeR.
    eapply dumpVar in H15. Focus 2. instantiate (1 := 8). simpl. reflexivity.
    Focus 2. simpl. reflexivity. simpl in H15.
    eapply dumpVar2. Focus 2. instantiate (1 := 8). simpl. reflexivity.
    Focus 2. simpl. reflexivity. simpl.
    apply H15.

    inversion H6. subst. clear H6.
    inversion H16. subst. clear H16.
    inversion H15. subst. clear H15.
    Transparent basicEval. simpl in H18. Opaque basicEval. inversion H18.
    subst. clear H16.
    inversion H15. subst. clear H15.
    eapply concreteComposeEmpty in H19. inversion H19. subst. clear H19.
    inversion H13. subst. clear H13.
    Transparent basicEval. simpl in H19. Opaque basicEval.
    destruct x; inversion H19.
    destruct (findRecord n0 v1); inversion H6.
    subst. clear H6.
    inversion H16. subst. clear H16.
    inversion H15. subst. clear H15.
    inversion H16. subst. clear H16.
    eapply concreteComposeEmpty in H19. inversion H19. subst. clear H19.
    inversion H13. subst. clear H13.
    Transparent basicEval. simpl in H19. Opaque basicEval.
    inversion H19.
    subst. clear H15.
    inversion H16. subst. clear H16.
    Transparent basicEval. simpl in H14.
    inversion H19. subst. clear H19. inversion H6. subst. clear H6.
    inversion H13. subst. clear H13.
    eapply concreteComposeEmpty in H21. inversion H21. subst. clear H21.
    inversion H16. subst. clear H16.
    Transparent basicEval. simpl in H21. Opaque basicEval.
    inversion H21.
    subst. clear H16.
    inversion H15. subst. clear H15.
    inversion H19. subst. clear H19.
    inversion H6. subst. clear H6.
    inversion H13. subst. clear H13.
    inversion H21. subst. clear H21.
    inversion H6. subst. clear H6.
    inversion H15. subst. clear H15.
    eapply concreteComposeEmpty in H23. inversion H23. subst. clear H23.
    inversion H19. subst. clear H19.
    Transparent basicEval. simpl in H23.
    destruct x3; inversion H23.
    destruct (findRecord n0 v); inversion H6.
    destruct (nth 3 l1 NoValue); inversion H22.

    inversion H6. subst. clear H6.
    inversion H16. subst. clear H16.
    inversion H15. subst. clear H15.
    Transparent basicEval. simpl in H18. Opaque basicEval. inversion H18.
    subst. clear H16.
    inversion H15. subst. clear H15.
    eapply concreteComposeEmpty in H19. inversion H19. subst. clear H19.
    inversion H13. subst. clear H13.
    Transparent basicEval. simpl in H19. Opaque basicEval.
    destruct x; inversion H19.
    destruct (findRecord n0 v1); inversion H6.
    subst. clear H6.
    inversion H16. subst. clear H16.
    inversion H15. subst. clear H15.
    inversion H16. subst. clear H16.
    eapply concreteComposeEmpty in H19. inversion H19. subst. clear H19.
    inversion H13. subst. clear H13.
    Transparent basicEval. simpl in H19. Opaque basicEval.
    inversion H19.
    subst. clear H15.
    inversion H16. subst. clear H16.
    Transparent basicEval. simpl in H14.
    inversion H19. subst. clear H19. inversion H6. subst. clear H6.
    inversion H13. subst. clear H13.
    eapply concreteComposeEmpty in H21. inversion H21. subst. clear H21.
    inversion H16. subst. clear H16.
    Transparent basicEval. simpl in H21. Opaque basicEval.
    inversion H21.
    subst. clear H16.
    inversion H15. subst. clear H15.
    inversion H19. subst. clear H19.
    inversion H6. subst. clear H6.
    inversion H13. subst. clear H13.
    inversion H21. subst. clear H21.
    inversion H6. subst. clear H6.
    inversion H15. subst. clear H15.
    eapply concreteComposeEmpty in H23. inversion H23. subst. clear H23.
    inversion H19. subst. clear H19.
    Transparent basicEval. simpl in H23.
    destruct x3; inversion H23.
    destruct (findRecord n0 v); inversion H6.
    destruct (nth 3 l0 NoValue); inversion H22.

    inversion H6. subst. clear H6.
    inversion H16. subst. clear H16.
    inversion H15. subst. clear H15.
    Transparent basicEval. simpl in H18. Opaque basicEval. inversion H18.
    subst. clear H16.
    inversion H15. subst. clear H15.
    eapply concreteComposeEmpty in H19. inversion H19. subst. clear H19.
    inversion H13. subst. clear H13.
    Transparent basicEval. simpl in H19. Opaque basicEval.
    destruct x; inversion H19.
    destruct (findRecord n0 v1); inversion H6.
    subst. clear H6.
    inversion H16. subst. clear H16.
    inversion H15. subst. clear H15.
    inversion H16. subst. clear H16.
    eapply concreteComposeEmpty in H19. inversion H19. subst. clear H19.
    inversion H13. subst. clear H13.
    Transparent basicEval. simpl in H19. Opaque basicEval.
    inversion H19.
    subst. clear H15.
    inversion H16. subst. clear H16.
    Transparent basicEval. simpl in H14.
    inversion H19. subst. clear H19. inversion H6. subst. clear H6.
    inversion H13. subst. clear H13.
    eapply concreteComposeEmpty in H21. inversion H21. subst. clear H21.
    inversion H16. subst. clear H16.
    Transparent basicEval. simpl in H21. Opaque basicEval.
    inversion H21.
    subst. clear H16.
    inversion H15. subst. clear H15.
    inversion H19. subst. clear H19.
    inversion H6. subst. clear H6.
    inversion H13. subst. clear H13.
    inversion H21. subst. clear H21.
    inversion H6. subst. clear H6.
    inversion H15. subst. clear H15.
    eapply concreteComposeEmpty in H23. inversion H23. subst. clear H23.
    inversion H19. subst. clear H19.
    Transparent basicEval. simpl in H23.
    destruct x3; inversion H23.
    destruct (findRecord n0 v); inversion H6.
    destruct (nth 3 l0 NoValue); inversion H22.
Qed.

Theorem mergeTheorem1Aux7 : forall eee v v0 v1 v2 l v4 x x0 e,
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
  @NatValue unit 0 = nth (eee varx) l NoValue ->
  e <> 0 ->
  @NatValue unit e =
       (if match eee varx with
           | 0 => false
           | 1 => false
           | 2 => false
           | 3 => false
           | S (S (S (S _))) => true
           end
        then NatValue 0
        else NatValue 1) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
       (AbsExists range(#0, #4)
             (([--( v(2), v(6) )---> (#2 ++++ v(8))] **
               [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #2] *\/*
               [--( v(2), v(6) )---> (#6 ++++ v(8))] **
               [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #1]) **
              AbsAll range(#0, #4)
                (([#0 ==== nth(replacenth(v(4), !!(varx), !!(valuex)), v(9))] *\/*
                  [--( v(2), v(6) )---> (#10 ++++ v(9)) ==== #0] **
                  [#0 <<<< nth(replacenth(v(4), !!(varx), !!(valuex)), v(9))]) *\/*
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
                        [nth(find(v(0), v(11)), #4) ==== #1])))))) 
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
          (eee, empty_heap) ->
  0 =
         @mapSum unit eq_unit (@basicEval unit) eee
           (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
           (NatValue 0 :: NatValue 1 :: NatValue 2 :: NatValue 3 :: nil)
           (--( v(2), v(6) )---> (#2 ++++ v(8)) //\\ nth(v(4), v(8)) ==== #2 \\//
           --( v(2), v(6) )---> (#6 ++++ v(8)) //\\ nth(v(4), v(8)) ==== #1) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
         ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: nil) 
         (eee, empty_heap) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
        (AbsAll TreeRecords(v(0))
            ([--(v(0),v(8))-->stack_var_offset <<<< #var_count]))
     (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
     (eee, empty_heap) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
        (AbsAll TreeRecords(v(0))
             ([nth(v(4),--(v(0),v(8))-->stack_var_offset)====--(v(0),v(8))-->stack_val_offset]))
     (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
     (eee, empty_heap) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
     (AbsAll range(#0, #4)
        ([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
         [nth(v(4), v(8)) ==== #0]))
     (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
     (eee, empty_heap).
Proof.
    intros.

    eapply RSAll. Transparent basicEval. simpl. Opaque basicEval. reflexivity. reflexivity.
    intros. simpl.
    destruct x1; hypSimp.
    remember (beq_nat n (eee varx)).
    destruct b.
    apply beq_nat_eq in Heqb. subst.
    eapply RSOrComposeR. eapply RSR.
    Transparent basicEval. simpl. Opaque basicEval. rewrite <- H3. simpl.
    reflexivity. apply BTStatePredicate. intro X. inversion X. unfold empty_heap. reflexivity.

    inversion H6. subst. clear H6. inversion H18. subst. clear H18.
    inversion H6. subst. clear H6. Transparent basicEval. simpl in H15. inversion H15. subst. clear H15.
    simpl in H13.
    inversion H13. subst. clear H13.
    eapply concreteComposeEmpty in H19. inversion H19. subst. clear H19.
    inversion H16. subst. clear H16. Transparent basicEval. simpl in H17. Opaque basicEval.
    inversion H17. subst. clear H17. simpl in H20.
    apply H20 in H11. clear H20.

    eapply removeReplace in H11. Focus 2.
    instantiate (1 := (!!varx)). instantiate (1 := v(9)). instantiate (1 := (v
          :: v0
             :: v1
                :: v2
                   :: ListValue l :: v4 :: x :: x0 :: x1 :: NatValue n :: nil)).
    instantiate (1 := eee). Transparent basicEval. simpl. Opaque basicEval.
    rewrite <- Heqb. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    inversion H11. subst. clear H11.
    inversion H17. subst. clear H17.
    eapply RSOrComposeR.
    eapply dumpVar in H16. Focus 2. instantiate (1 := 8). simpl. reflexivity.
    Focus 2. simpl. reflexivity. simpl in H16.
    eapply expressionSubGRSRL. apply H16. simpl. reflexivity. simpl. reflexivity.
    simpl. reflexivity.
    eapply RSR. Transparent basicEval. simpl. reflexivity. apply BTStatePredicate.
    omega. unfold empty_heap. reflexivity.

    subst. clear H17.
    inversion H16. subst. clear H16.
    eapply concreteComposeEmpty in H19. inversion H19. subst. clear H19.
    eapply RSOrComposeL.
    eapply dumpVar in H13. Focus 2. instantiate (1 := 8). simpl. reflexivity.
    Focus 2. simpl. reflexivity. simpl in H13.
    apply H13.

    subst. clear H11.
    inversion H17. subst. clear H17.
    inversion H16. subst. clear H16.
    inversion H17. subst. clear H17.
    inversion H13. subst. clear H13.
    eapply concreteComposeEmpty in H19. inversion H19. subst. clear H19.
    Transparent basicEval. simpl in H20. Opaque basicEval.
    remember (beq_nat (eee varx) n). destruct b.
    apply beq_nat_eq in Heqb0. subst.
    erewrite <- beq_nat_refl in Heqb. inversion Heqb.
    inversion H20. elim H11. reflexivity.

    subst. clear H16.
    inversion H17. subst. clear H17.
    inversion H19. subst. clear H19.
    inversion H6. subst. clear H6.
    inversion H13. subst. clear H13.
    eapply concreteComposeEmpty in H21. inversion H21. subst. clear H21.
    inversion H17. subst. clear H17.
    Transparent basicEval. simpl in H21. Opaque basicEval.
    remember (beq_nat (eee varx) n). destruct b.
    apply beq_nat_eq in Heqb0. subst.
    erewrite <- beq_nat_refl in Heqb. inversion Heqb.
    inversion H21. elim H13. reflexivity.

    subst. clear H17.
    inversion H16. subst. clear H16.
    inversion H19. subst. clear H19.
    inversion H6. subst. clear H6.
    Transparent basicEval. simpl in H14. Opaque basicEval.
    inversion H13. subst. clear H13.
    Transparent basicEval. simpl in H18. Opaque basicEval. simpl in H21.
    inversion H21. subst. clear H21.
    inversion H6. subst. clear H6.
    destruct x2; hypSimp.
    inversion H16. subst. clear H16.
    apply concreteComposeEmpty in H23. inversion H23. subst. clear H23.

    eapply mapSumNeg in H7. Focus 2.
    instantiate (1 :=
        @absEval unit eq_unit (@basicEval unit) eee (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x3 :: nil)
                 nth(find(v(0),v(8)),#3)).
    eapply subRangeSet in H13. Focus 2. apply H18. Focus 2. apply H11. Focus 2. apply H14.
    inversion H9. subst. clear H9.
    Transparent basicEval. simpl in H21. Opaque basicEval.
    rewrite H14 in H21. inversion H21. subst. clear H21. simpl in H24.
    apply H24 in H13.
    Transparent basicEval. simpl.
    inversion H13. subst. clear H13. Transparent basicEval. simpl in H22. Opaque basicEval.
    destruct (match
               match x3 with
               | NatValue x => findRecord x v
               | ListValue _ => NoValue
               | NoValue => NoValue
               | OtherValue _ => NoValue
               end
             with
             | NatValue _ => NoValue
             | ListValue l => nth 3 l NoValue
             | NoValue => NoValue
             | OtherValue _ => NoValue
             end); hypSimp.
    destruct n1. left. reflexivity. destruct n1. right. left. reflexivity.
    destruct n1. right. right. left. reflexivity. destruct n1. right. right. right. left. reflexivity.
    inversion H22. elim H9. reflexivity.
    Opaque absEval. simpl in H7. Transparent absEval.

    eapply subBoundVar in H7.
    Focus 2. instantiate (3 := 8). Opaque absEval. simpl. Transparent absEval. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    simplifyHyp H7. simplifyHyp H7.

    inversion H10. subst. clear H10. Transparent basicEval. simpl in H21. Opaque basicEval.
    rewrite H14 in H21. inversion H21. subst. clear H21.

    eapply expressionSubRSLR in H7. Focus 2. eapply H24.

    eapply subRangeSet in H13. Focus 2. apply H18. Focus 2. apply H11. apply H13. apply H14.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    inversion H7. subst. clear H7.
    eapply concreteComposeEmpty in H23. inversion H23. subst. clear H23.
    inversion H20. subst. clear H20.
    inversion H22. subst. clear H22.
    eapply concreteComposeEmpty in H25. inversion H25. subst. clear H25.
    inversion H16.
    eapply dumpVar in H10. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H10.
    eapply dumpVar in H10. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H10.
    eapply dumpVar in H10. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H10.
    eapply expressionSubRSNeg in H10. Focus 2. apply H23. Focus 2. simpl. reflexivity. Focus 2.
    simpl. reflexivity. Focus 2. simpl. reflexivity.
    inversion H10. subst. clear H10. Transparent basicEval. simpl in H30. Opaque basicEval.
    inversion H30. subst. clear H30. elim H7. reflexivity.
    eapply dumpVar in H20. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H20.
    eapply dumpVar in H20. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H20.
    eapply dumpVar in H20. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H20.
    eapply expressionSubRSLR in H23. Focus 2. apply H20. Focus 2. simpl. reflexivity. Focus 2.
    simpl. reflexivity. Focus 2. simpl. reflexivity.
    inversion H23. subst. clear H23. Transparent basicEval. simpl in H30. Opaque basicEval.
    inversion H30. subst. clear H30. elim H7. reflexivity.

    subst. clear H20.
    inversion H22. subst. clear H22.
    eapply concreteComposeEmpty in H25. inversion H25. subst. clear H25.
    inversion H17. subst. clear H17.
    eapply dumpVar in H10. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H10.
    eapply dumpVar in H10. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H10.
    eapply dumpVar in H10. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H10.
    eapply expressionSubRSNeg in H10. Focus 2. apply H23. Focus 2. simpl. reflexivity. Focus 2.
    simpl. reflexivity. Focus 2. simpl. reflexivity.
    inversion H10. subst. clear H10. Transparent basicEval. simpl in H25. Opaque basicEval.
    inversion H25. subst. clear H25. elim H7. reflexivity.
    eapply dumpVar in H20. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H20.
    eapply dumpVar in H20. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H20.
    eapply dumpVar in H20. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H20.
    eapply expressionSubRSLR in H23. Focus 2. apply H20. Focus 2. simpl. reflexivity. Focus 2.
    simpl. reflexivity. Focus 2. simpl. reflexivity.
    inversion H23. subst. clear H23. Transparent basicEval. simpl in H30. Opaque basicEval.
    inversion H30. subst. clear H30. elim H7. reflexivity.
Qed.

Theorem mergeTheorem1Aux6 : forall e v v0 v1 v2 l v4 x x0 eee,
  In x0 (NatValue 0 :: NatValue 1 :: NatValue 2 :: NatValue 3 :: nil) ->
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
  NatValue 0 = nth (eee varx) l NoValue ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          (AbsAll range(#0, #4)
             ([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
              [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #0]))
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
          (eee, empty_heap) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
         ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: nil) 
         (eee, empty_heap) ->
         length l=4 ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
     (AbsAll range(#0, #4)
        ([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
         [nth(v(4), v(8)) ==== #0]))
     (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
     (eee, empty_heap).
Proof.
    intros.

    inversion H3. subst. clear H3. Transparent basicEval. simpl in H9. Opaque basicEval.
    inversion H9. subst. clear H9.

    eapply RSAll. Transparent basicEval. simpl. Opaque basicEval. simpl. reflexivity. reflexivity.
    intros.
    apply H12 in H3. clear H12.
    simpl in H3. simpl.

    inversion H3. subst. clear H3.
    eapply RSOrComposeL. apply H10.

    subst. clear H3.
    inversion H10. subst. clear H10. Transparent basicEval. simpl in H11. Opaque basicEval.

    destruct x1.

    remember (beq_nat n (eee varx)).
    destruct b.

    apply beq_nat_eq in Heqb. subst.
    rewrite nth_replace_same in H11.

    inversion H4. subst. clear H4.
    inversion H9. subst. clear H9. Transparent basicEval. simpl in H10. Opaque basicEval.
    destruct (eee valuex). simpl in H10. inversion H10.

    elim H4. reflexivity.

    simpl in H11. inversion H11. subst. clear H11. elim H4. reflexivity.

    subst. clear H4.

    inversion H9. subst. clear H9. Transparent basicEval. simpl in H10. Opaque basicEval.
    destruct (eee valuex). simpl in H10. inversion H10.
    elim H4. reflexivity.

    simpl in H11. inversion H11. subst. clear H11. elim H4. reflexivity.

    reflexivity. rewrite H5.
    destruct (eee varx). omega. destruct n. omega. destruct n. omega. destruct n. omega.
    inversion H1. subst. elim H0. reflexivity.

    apply beq_nat_neq in Heqb.

    rewrite nth_replace_diff in H11.
    inversion H11. subst. clear H11.

    eapply RSOrComposeR.
    eapply RSR. Transparent basicEval. simpl. Opaque basicEval.

    rewrite <- H3. reflexivity. eapply BTStatePredicate. apply H6.

    unfold empty_heap. simpl. reflexivity.
    apply Heqb.

    inversion H11. inversion H11. inversion H11.
Qed.

Theorem mergeTheorem1Aux5 : forall eee v v0 v1 v2 l v4 x x0 e,
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
         ([--( v(2), v(6) )---> (#2 ++++ v(7))] **
          ([nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #2] *\/*
           [nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #0]) *\/*
          [--( v(2), v(6) )---> (#6 ++++ v(7))] **
          ([nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #1] *\/*
           [nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #0]))
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
         (eee, empty_heap) ->
  In x0 (NatValue 0 :: NatValue 1 :: NatValue 2 :: NatValue 3 :: nil) ->
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
  NatValue 0 = nth (eee varx) l NoValue ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
     ([--( v(2), v(6) )---> (#2 ++++ v(7))] **
      ([nth(v(4), v(7)) ==== #2] *\/* [nth(v(4), v(7)) ==== #0]) *\/*
      [--( v(2), v(6) )---> (#6 ++++ v(7))] **
      ([nth(v(4), v(7)) ==== #1] *\/* [nth(v(4), v(7)) ==== #0]))
     (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil) 
     (eee, empty_heap).
Proof.
        Transparent basicEval.
        intros.
        destructState. hypSimp. inversion H; subst; clear H; hypSimp.
        inversion H8. subst. clear H8.
        eapply concreteComposeEmpty in H10. inversion H10; subst; clear H10.
        eapply RSOrComposeL.
        eapply RSCompose. apply H5.
        inversion H6. subst. clear H6. destructState. hypSimp.
        destruct x0; hypSimp.
        remember (beq_nat n (eee varx)). destruct b. apply beq_nat_eq in Heqb. subst.
        eapply RSOrComposeR. eapply RSR. simpl. reflexivity.
        rewrite <- H3. simpl.
        eapply BTStatePredicate. intro X. inversion X. instantiate (1 := (eee,empty_heap)).
        unfold empty_heap. reflexivity.
        apply beq_nat_neq in Heqb.
        erewrite nth_replace_diff in HeqH.
        apply RSOrComposeL. eapply RSR. simpl. reflexivity.
        rewrite <- HeqH. simpl.
        apply BTStatePredicate. intro X. inversion X.
        unfold empty_heap. reflexivity. apply Heqb.

        subst. clear H6. destructState. hypSimp.
        destruct x0; hypSimp.
        remember (beq_nat n (eee varx)). destruct b. apply beq_nat_eq in Heqb. subst.
        eapply RSOrComposeR. eapply RSR. simpl. reflexivity.
        rewrite <- H3. simpl.
        eapply BTStatePredicate. intro X. inversion X.
        unfold empty_heap. reflexivity.
         apply beq_nat_neq in Heqb.
        erewrite nth_replace_diff in HeqH.
        apply RSOrComposeR. eapply RSR. Transparent basicEval. simpl. reflexivity.
        rewrite <- HeqH. simpl.
        apply BTStatePredicate. intro X. inversion X.
        unfold empty_heap. reflexivity. apply Heqb.
        apply concreteComposeEmpty. split. reflexivity. reflexivity.

        inversion H8. subst. clear H8.
        eapply concreteComposeEmpty in H10. inversion H10; subst; clear H10.
        eapply RSOrComposeR.
        eapply RSCompose. apply H5. 
        inversion H6. subst. clear H6. destructState. hypSimp.
        destruct x0; hypSimp.
        remember (beq_nat n (eee varx)). destruct b. apply beq_nat_eq in Heqb. subst.
        eapply RSOrComposeR. eapply RSR. simpl. reflexivity.
        rewrite <- H3. simpl.
        eapply BTStatePredicate. intro X. inversion X. instantiate (1 := (eee,empty_heap)).
        unfold empty_heap. reflexivity.
        apply beq_nat_neq in Heqb.
        erewrite nth_replace_diff in HeqH.
        apply RSOrComposeL. eapply RSR. Transparent basicEval. simpl. reflexivity.
        rewrite <- HeqH. simpl.
        apply BTStatePredicate. intro X. inversion X.
        unfold empty_heap. reflexivity. apply Heqb.

        subst. clear H6. Transparent basicEval. destructState.
        hypSimp.
        destruct x0; hypSimp.
        remember (beq_nat n (eee varx)). destruct b. apply beq_nat_eq in Heqb. subst.
        eapply RSOrComposeR. eapply RSR. simpl. reflexivity.
        rewrite <- H3. simpl.
        eapply BTStatePredicate. intro X. inversion X.
        unfold empty_heap. reflexivity.
         apply beq_nat_neq in Heqb.
        erewrite nth_replace_diff in HeqH.
        apply RSOrComposeR. eapply RSR. Transparent basicEval. simpl. reflexivity. Opaque basicEval.
        rewrite <- HeqH. simpl.
        apply BTStatePredicate. intro X. inversion X.
        unfold empty_heap. reflexivity. apply Heqb.
        apply concreteComposeEmpty. split. reflexivity. reflexivity.
        Opaque basicEval.
Qed.

Theorem mergeTheorem1Aux4b : forall v v0 v1 v2 l v4 x x0 eee x1 x2,
  (forall x1 : Value,
       In x1 (NatValue 0 :: NatValue 1 :: NatValue 2 :: NatValue 3 :: nil) ->
       @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          (([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
            [--( v(2), v(6) )---> (#2 ++++ v(8))]) *\/*
           [--( v(2), v(6) )---> (#6 ++++ v(8))])
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: nil)
         (eee, empty_heap)) ->
  (In x0 (NatValue 0 :: NatValue 1 :: NatValue 2 :: NatValue 3 :: nil)) ->
  (@NatValue unit 1 =
       (if match eee varx with
           | 0 => false
           | 1 => false
           | 2 => false
           | 3 => false
           | S (S (S (S _))) => true
           end
        then NatValue 0
        else NatValue 1)) ->
  (@NatValue unit 0 = nth (eee varx) l NoValue) ->
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
         (*([#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8))] **
          [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #0] *\/*
          [#0 ==== nth(replacenth(v(4), !!(varx), !!(valuex)), v(8))] *\/*
          [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
          [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0])*)
         ((v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil) ++
          x1 :: nil) (eee, empty_heap)) ->
  (false =
       validPredicate
         (@absEval unit eq_unit (@basicEval unit) eee
            (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
            (#0 ==== --( v(2), v(6) )---> (#10 ++++ !!(varx))))) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
       ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: nil) 
         (eee, empty_heap) ->
  length l = 4 ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
         (SUM(range(#0, #4),
          #0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8)) //\\
          ((--( v(2), v(6) )---> (#2 ++++ v(8)) \\//
            --( v(2), v(6) )---> (#6 ++++ v(8))) //\\
           nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #0), 
          #1)) (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
         (eee, fun _ : nat => None) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          ([#1 ====
            (v(8) ++++ v(9)) ++++
            (#0 <<<< --( v(2), v(6) )---> (#10 ++++ !!(varx)) //\\
             (~~ --( v(2), v(6) )---> (#2 ++++ !!(varx)) //\\
              ~~ --( v(2), v(6) )---> (#6 ++++ !!(varx)) \\//
              #0 <<<< nth(replacenth(v(4), !!(varx), !!(valuex)), !!(varx))))])
          (v
           :: v0
              :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)
          (eee, empty_heap) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          ([#0 ==== v(9)])
          (v
           :: v0
              :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)
          (eee, empty_heap) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          ([#0 ==== v(8)])
          (v
           :: v0
              :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)
          (eee, empty_heap) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          (SUM(range(!!(varx) ++++ #1, #4),
           #0 <<<< --( v(2), v(6) )---> (#10 ++++ v(10)) //\\
           (~~ --( v(2), v(6) )---> (#2 ++++ v(10)) //\\
            ~~ --( v(2), v(6) )---> (#6 ++++ v(10)) \\//
            #0 <<<< nth(v(4), v(10))), #0))
          (v
           :: v0
              :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)
          (eee, fun _ : nat => None) ->
  @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          (SUM(range(#0, #4),
           #0 <<<< --( v(2), v(6) )---> (#10 ++++ v(10)) //\\
           (~~ --( v(2), v(6) )---> (#2 ++++ v(10)) //\\
            ~~ --( v(2), v(6) )---> (#6 ++++ v(10)) \\//
            #0 <<<< nth(v(4), v(10))),
           #0 <<<< --( v(2), v(6) )---> (#10 ++++ !!(varx)) //\\
           (~~ --( v(2), v(6) )---> (#2 ++++ !!(varx)) //\\
            ~~ --( v(2), v(6) )---> (#6 ++++ !!(varx)))))
          (v
           :: v0
              :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)
          (eee, fun _ : nat => None) ->
        @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
     (AbsAll range(#0, #4)
        ([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
         [nth(v(4), v(8)) ==== #0]))
     (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
     (eee, empty_heap).
Proof.
    intros.

    assert (forall x1 : Value,
      In x1 (NatValue 0 :: NatValue 1 :: NatValue 2 :: NatValue 3 :: nil) ->
      @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
        (([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
          [--( v(2), v(6) )---> (#2 ++++ v(8))]) *\/*
         [--( v(2), v(6) )---> (#6 ++++ v(8))])
        (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: nil)
        (eee, empty_heap)).
    apply H.

    eapply expressionSubEvalEval in H.
    Focus 2. instantiate (1 := v(8)). instantiate (2 := eee). instantiate (2 := (!!varx)).
    Transparent basicEval. simpl. Opaque basicEval. reflexivity.
    Focus 2.
    destruct (eee varx). simpl. left. reflexivity. destruct n. simpl. right. left. reflexivity.
    destruct n. simpl. right. right. left. reflexivity. destruct n. simpl. right. right. right. left.
    reflexivity. inversion H1.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    eapply expressionNotEqualZero3 in H. Focus 2. apply H5. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. reflexivity. Focus 2. simpl. reflexivity.

    simplifyHyp H.

    assert (@absEval unit eq_unit (@basicEval unit) eee
                     (v :: v0 :: v1 :: v2 :: ListValue l
                        :: v4 :: x :: x0 :: NatValue (eee varx) :: nil)
              (~~ --( v(2), v(6) )---> (#2 ++++ !!(varx)) //\\
               ~~ --( v(2), v(6) )---> (#6 ++++ !!(varx)))=NatValue 0).
    inversion H. subst. clear H.
    erewrite expressionSubGRSNeg. Focus 2. apply H19. Focus 2. simpl. reflexivity. Focus 2.
    simpl. reflexivity. Focus 2. simpl. reflexivity.

    Transparent basicEval. simpl. Opaque basicEval. reflexivity.
    simpl. reflexivity.

    erewrite expressionSubGRSNeg. Focus 2. apply H19. Focus 2. simpl. reflexivity. Focus 2.
    simpl. reflexivity. Focus 2. simpl. reflexivity.

    erewrite <- simplifyAbsEval. Focus 2. compute. reflexivity.
    Transparent basicEval. simpl. Opaque basicEval. reflexivity.

    simpl. reflexivity.

    eapply expressionSubEval in H13.

    Focus 2. instantiate (4 := 0). rewrite <- H15. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    simplifyHyp H13.

    eapply resolveSum8x10 in H13.
    Focus 2. intros. eapply H14. apply H16. Focus 2. simpl. reflexivity. Focus 2.
    instantiate (1 := (#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(10)) //\\
         #0 <<<< nth(v(4), v(10)))).
    simpl. intros.
    simplifyHyp H17. simplifyHyp H17.
    inversion H17. subst. clear H17. inversion H22. subst. clear H22.
    eapply expressionSubGRSLR. apply H21. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply RSEmpty. unfold empty_heap. reflexivity.
    subst. clear H22.
    eapply expressionSubGRSNeg1. apply H21. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity.
    simpl. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply RSEmpty. unfold empty_heap. reflexivity.
    subst. clear H17.
    eapply expressionSubGRSNeg1. apply H22. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity.
    simpl. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply RSEmpty. unfold empty_heap. reflexivity.

    eapply sumAllConv in H13.
    simplifyHyp H13. simplifyHyp H13. simplifyHyp H13. simplifyHyp H13.

    eapply dumpVar in H13. Focus 2. instantiate (1 := 8). simpl. reflexivity.
    Focus 2. simpl. reflexivity. simpl in H13.
    eapply dumpVar in H13. Focus 2. instantiate (1 := 8). simpl. reflexivity.
    Focus 2. simpl. reflexivity. simpl in H13. simpl.
    unfold empty_heap. apply H13.

    Transparent basicEval. simpl. reflexivity. Opaque basicEval.
Grab Existential Variables.
    apply (fun a b c d e f => a=a). apply (fun a b c => a=a).
Qed.

Theorem mergeTheorem1Aux4 : forall v v0 v1 v2 l v4 x x0 eee,
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
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: nil) (eee, empty_heap)) ->
      In x0 (NatValue 0 :: NatValue 1 :: NatValue 2 :: NatValue 3 :: nil) ->
      NatValue 1 =
      (if match eee varx with
          | 0 => false
          | 1 => false
          | 2 => false
          | 3 => false
          | S (S (S (S _))) => true
          end
       then @NatValue unit 0
       else NatValue 1) ->
       NatValue 0 = nth (eee varx) l NoValue ->
       @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
           (SUM(range(#0, #4),
           (--( v(2), v(6) )---> (#2 ++++ v(8)) \\//
            --( v(2), v(6) )---> (#6 ++++ v(8))) //\\
           nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #0, 
           #1))
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
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
     false =
         validPredicate
           (@absEval unit eq_unit (@basicEval unit) eee
              (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
              (#0 ==== --( v(2), v(6) )---> (#10 ++++ !!(varx)))) ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
     ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: nil) 
         (eee, empty_heap) ->
     length l=4 ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
     (AbsAll range(#0, #4)
        ([--( v(2), v(6) )---> (#10 ++++ v(8)) ==== #0] *\/*
         [nth(v(4), v(8)) ==== #0]))
     (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
     (eee, empty_heap).
Proof.
    intros.

    eapply andSum8 in H4. Focus 2. apply H6. Focus 2. simpl. reflexivity. Focus 2.
    Transparent basicEval. simpl. Opaque basicEval. reflexivity.

    simplifyHyp H4. simplifyHyp H4. simplifyHyp H4.
    simplifyHyp H.

    eapply sumDiff in H. Focus 2. eapply H4. Focus 2. simpl. reflexivity.

    simplifyHyp H. simplifyHyp H.

    eapply unfoldSum in H. Focus 2. simpl. reflexivity. Focus 2. instantiate (1 := (!!varx)). simpl. reflexivity.
    Focus 2. Transparent basicEval. simpl. Opaque basicEval.
    destruct (eee varx). reflexivity. destruct n. reflexivity. destruct n. reflexivity.
    destruct n. reflexivity. destruct n. reflexivity. inversion H2.

    simpl in H. inversion H. subst. clear H. inversion H11. subst. clear H11.
    inversion H. subst. clear H. inversion H11. subst. clear H11. inversion H. subst. clear H.
    inversion H13. subst. clear H13.
    eapply concreteComposeEmpty in H16. inversion H16. subst. clear H16.
    eapply concreteComposeEmpty in H18. inversion H18. subst. clear H18.
    simpl in H14.
    assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
           ([#1 ====
            (v(8) ++++ v(9)) ++++
            (#0 <<<< --( v(2), v(6) )---> (#10 ++++ !!(varx)))])
           (v
         :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)
        (eee, empty_heap)).
    eapply removeReplaceSame in H14. Focus 2. instantiate (1 := !!(varx)). instantiate (1 := v(4)).
    simpl. reflexivity. Focus 2. Transparent basicEval. simpl. reflexivity. Focus 2.
    simpl. reflexivity. Opaque basicEval.

    inversion H8. subst. clear H8.
    eapply expressionSubRSLR in H14. Focus 2. apply H16. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    simplifyHyp H14. simplifyHyp H14. simplifyHyp H14.
    apply H14.
    subst. clear H8.
    eapply expressionSubRSLR in H14. Focus 2. apply H16. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    simplifyHyp H14. simplifyHyp H14. simplifyHyp H14.
    apply H14.
    rewrite H9. destruct (eee varx). omega. destruct n. omega. destruct n. omega. destruct n. omega.
    inversion H2.

    simplifyHyp H11. simplifyHyp H12.

    eapply expressionNotEqualZero1 in H. Focus 2. apply H7. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. reflexivity. Focus 2. simpl. reflexivity.

    simplifyHyp H. simplifyHyp H.

    inversion H. subst. clear H.
    eapply concreteComposeEmpty in H19. inversion H19. subst. clear H19.

    eapply expressionSubRSRL in H11. Focus 2. apply H16. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    eapply expressionSubRSRL in H12. Focus 2. apply H15. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    eapply foldSum in H12. Focus 2. apply H11. Focus 2. simpl. reflexivity.
    simplifyHyp H12.

    eapply expressionSubEval in H12.
    Focus 2. instantiate (1 := (nth(v(4), !!(varx)))). instantiate (2 := eee).
    instantiate (1 := (v
           :: v0
              :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)).
    Transparent basicEval. simpl. rewrite <- H3. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    simplifyHyp H12.

    eapply mergeTheorem1Aux4b. apply H0. apply H1. apply H2. apply H3. apply H5. apply H6.
    apply H7. apply H8. apply H9. apply H4. apply H14. apply H16. apply H15. apply H11.
    apply H12.
Qed.

Theorem mergeTheorem1Aux3 : forall eee l v v0 v1 v2 v4 x x0 x1 x2,
        (match eee varx with
          | 0 => true
          | 1 => true
          | 2 => true
          | 3 => true
          | S (S (S (S _))) => false
          end=true) ->
        NatValue 0 = nth (eee varx) l NoValue ->
        true =
         validPredicate
           (@absEval unit eq_unit (@basicEval unit) eee
              (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
              (#0 ==== --( v(2), v(6) )---> (#10 ++++ !!(varx)))) ->
        @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
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
                             [nth(find(v(0), v(11)), #3) ==== v(8)])))
         (v
          :: v0
             :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)
         (eee, empty_heap) ->
        length l=4 ->
        @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
         ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: nil) 
         (eee, empty_heap) ->
        @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
     (((((([--( v(2), v(6) )---> (#10 ++++ v(8))] *\/*
           [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
           [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0]) *\/*
          [~~ --( v(2), v(6) )---> (#10 ++++ v(9))]) *\/*
         [nth(v(4), v(8)) ==== #0]) *\/* [nth(v(4), v(9)) ==== #0]) *\/*
       [v(8) ==== v(9)]) *\/*
      AbsExists TreeRecords(v(0))
        (AbsExists TreeRecords(find(v(0), v(10)))
           ([nth(find(v(0), v(10)), #3) ==== v(9)] **
            [nth(find(v(0), v(11)), #3) ==== v(8)])))
     (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)
     (eee, empty_heap).
Proof.
    intros.

    inversion H2. subst. clear H2.
    inversion H9. subst. clear H9.
    inversion H8. subst. clear H8.
    inversion H9. subst. clear H9.
    inversion H8. subst. clear H8.

    eapply RSOrComposeL. eapply RSOrComposeL. eapply RSOrComposeL. eapply RSOrComposeL. eapply RSOrComposeL.
    apply H9.

    subst. clear H8.
    eapply RSOrComposeL. eapply RSOrComposeL. eapply RSOrComposeL. eapply RSOrComposeL. eapply RSOrComposeR.
    apply H9.

    subst. clear H9.

    eapply RSOrComposeL. eapply RSOrComposeL. eapply RSOrComposeL. eapply RSOrComposeR.

    remember (validPredicate (@absEval unit eq_unit (@basicEval unit) eee
                             (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)
                             ( (!!varx) ==== (v(8)) ))).
    destruct b.

    eapply expressionSubRL in H8. Focus 2. rewrite Heqb. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    inversion H8. subst. clear H8. Transparent basicEval. simpl in H10. Opaque basicEval.

    erewrite nth_replace_same in H10.

    inversion H4. subst. clear H4. inversion H8. subst. clear H8. Transparent basicEval. simpl in H9.
    Opaque basicEval.

    destruct (eee valuex). simpl in H9. inversion H9. elim H4. reflexivity.
    simpl in H10. inversion H10. elim H4. reflexivity.

    inversion H8. subst. clear H8. Transparent basicEval. simpl in H15.
    Opaque basicEval.

    destruct (eee valuex). simpl in H15. inversion H15. elim H5. reflexivity.
    simpl in H10. inversion H10. elim H5. reflexivity. reflexivity.

    rewrite H3.
    destruct (eee varx). omega. destruct n. omega. destruct n. omega. destruct n. omega.
    inversion H.

    eapply removeReplace in H8. Focus 6. instantiate (1 := (!!varx)). instantiate (1 := v(8)).
    simpl. reflexivity. Focus 2. rewrite validPredicateSymmetry. rewrite Heqb. reflexivity.

    apply H8. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity.

    subst. clear H8.

    eapply RSOrComposeL. eapply RSOrComposeL. eapply RSOrComposeR.

    remember (validPredicate (@absEval unit eq_unit (@basicEval unit) eee
                             (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: x2 :: nil)
                             ( (!!varx) ==== (v(9)) ))).
    destruct b.

    eapply expressionSubRL in H9. Focus 2. rewrite Heqb. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    inversion H9. subst. clear H9. Transparent basicEval. simpl in H10. Opaque basicEval.

    erewrite nth_replace_same in H10.

    inversion H4. subst. clear H4. inversion H8. subst. clear H8. Transparent basicEval. simpl in H9.
    Opaque basicEval.

    destruct (eee valuex). simpl in H9. inversion H9. elim H4. reflexivity.
    simpl in H10. inversion H10. elim H4. reflexivity.

    inversion H8. subst. clear H8. Transparent basicEval. simpl in H15.
    Opaque basicEval.

    destruct (eee valuex). simpl in H15. inversion H15. elim H5. reflexivity.
    simpl in H10. inversion H10. elim H5. reflexivity. reflexivity.

    rewrite H3.
    destruct (eee varx). omega. destruct n. omega. destruct n. omega. destruct n. omega.
    inversion H.

    eapply removeReplace in H9. Focus 6. instantiate (1 := (!!varx)). instantiate (1 := v(9)).
    simpl. reflexivity. Focus 2. rewrite validPredicateSymmetry. rewrite Heqb. reflexivity.

    apply H9. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity.

    eapply RSOrComposeL. eapply RSOrComposeR. apply H8.

    subst.

    inversion H9. subst. clear H9.
    inversion H10. subst. clear H10.

    inversion H9. subst. clear H9.

    apply concreteComposeEmpty in H12. inversion H12. subst. clear H12.

    apply RSOrComposeL. apply RSOrComposeL. eapply RSOrComposeL. eapply RSOrComposeL.
    apply RSOrComposeR.

    eapply expressionSubGRSRL. apply H8. simpl. reflexivity. simpl. reflexivity.
    simpl. reflexivity.

    eapply expressionSubGRSRL. apply H7.  simpl. reflexivity. simpl. reflexivity.
    simpl. reflexivity.

    eapply expressionSubGRL. rewrite H1. reflexivity.  simpl. reflexivity. simpl. reflexivity.
    simpl. reflexivity. simpl. reflexivity.

    eapply RSR. Transparent basicEval. simpl.

 reflexivity. eapply BTStatePredicate. omega. Opaque basicEval.
    simpl. unfold empty_heap. reflexivity.

    subst. clear H10.

    eapply RSOrComposeL. eapply RSOrComposeL. eapply RSOrComposeR.

    inversion H9. subst. clear H9. inversion H12. subst. clear H12. inversion H5. subst. clear H5.
    inversion H7. subst. clear H7.

    apply concreteComposeEmpty in H14. inversion H14. subst. clear H14.

    eapply expressionSubGRSRL. apply H10. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity.

    Transparent basicEval. eapply RSR. simpl. rewrite <- H0. simpl. reflexivity.
    apply BTStatePredicate. omega. unfold empty_heap. reflexivity.

    subst. eapply RSOrComposeR. apply H10.

    Opaque basicEval.
Qed.

Theorem mergeTheorem1Aux2 : forall v v0 v1 v2 l v4 x x0 x1 eee,
    true = validPredicate
           (@absEval unit eq_unit (@basicEval unit) eee
              (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
              (#0 ==== --( v(2), v(6) )---> (#10 ++++ !!varx))) ->

    @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
         ([#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8))] **
          [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #0] *\/*
          [#0 <<<< nth(replacenth(v(4), !!(varx), !!(valuex)), v(8))] *\/*
          [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
          [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0])
    (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: nil) (eee, empty_heap) ->
    NatValue 0 = nth (eee varx) l NoValue ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
     ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: nil) 
         (eee, empty_heap) ->
    length l=4 ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          ([--( v(2), v(6) )---> (#2 ++++ !!(varx)) ==== #0] **
           [--( v(2), v(6) )---> (#6 ++++ !!(varx)) ==== #0])
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: nil) 
          (eee, empty_heap) ->
    @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) 
     ([#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8))] **
      [nth(v(4), v(8)) ==== #0] *\/*
      [#0 <<<< nth(v(4), v(8))] *\/*
      [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
      [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0])
      (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: nil) (eee, empty_heap).
Proof.
    intros.

    inversion H0. subst. clear H0. inversion H9. subst. clear H9.
    apply concreteComposeEmpty in H11. inversion H11. subst. clear H11.

    remember (validPredicate (@absEval unit eq_unit (@basicEval unit) eee (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: nil)
                                      ((!!varx)====v(8)))).
    destruct b.

    eapply expressionSubRL in H6. Focus 2. rewrite Heqb. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    eapply expressionSubRL in H6. Focus 2. rewrite H. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    inversion H6. subst. clear H6. Transparent basicEval. simpl in H11. Opaque basicEval.
    inversion H11. elim H5. reflexivity.

    eapply removeReplace in H7. Focus 2. rewrite Heqb. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    eapply RSOrComposeL. eapply RSCompose. apply H6. apply H7. apply concreteComposeEmpty.
    split. reflexivity. reflexivity.

    subst.

    eapply expressionSubRL in H9. Focus 2. rewrite H. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    eapply RSOrComposeR.

    inversion H9. subst. clear H9.

    remember (validPredicate (@absEval unit eq_unit (@basicEval unit) eee (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 :: nil)
                                      ((!!varx)====v(8)))).
    destruct b.

    eapply expressionSubGRL. rewrite Heqb. reflexivity. simpl. reflexivity.
    simpl. reflexivity. simpl. reflexivity. simpl. reflexivity.

    eapply RSOrComposeR.
    eapply dumpVar2. Focus 2. instantiate (1 := 7). simpl. reflexivity. simpl.
    eapply dumpVar2. Focus 2. instantiate (1 := 7). simpl. reflexivity. simpl.
    apply H4.
    Focus 2. simpl. reflexivity. simpl. reflexivity.

    eapply removeReplace in H10. Focus 2. rewrite Heqb. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    eapply RSOrComposeL. apply H10.

    subst.

    eapply RSOrComposeR. apply H10.
Qed.

Theorem mergeTheorem1Aux1 : forall eee v v0 v1 v2 l v4 x x0,
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          (SUM(range(#0, #4),
           (--( v(2), v(6) )---> (#2 ++++ v(8)) \\//
            --( v(2), v(6) )---> (#6 ++++ v(8))) //\\
           (nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #0), #1))
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
          (eee, empty_heap) ->
     (forall x1, In x1 (NatValue 0 :: NatValue 1 :: NatValue 2 :: NatValue 3 :: nil) ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          ([#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8))] **
           [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #0] *\/*
           [#0 <<<< nth(replacenth(v(4), !!(varx), !!(valuex)), v(8))] *\/*
           [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
           [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0])
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x1 ::nil) (eee, empty_heap)) ->
   true = validPredicate
           (@absEval unit eq_unit (@basicEval unit) eee
              (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
              (#0 ==== --( v(2), v(6) )---> (#10 ++++ !!(varx)))) ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
         ([!!(valuex) ==== #1] *\/* [!!(valuex) ==== #2])
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: nil) 
         (eee, empty_heap) ->
     ble_nat 4 (eee varx)=false ->
     length l = 4 ->
     NatValue 0 = nth (eee varx) l NoValue ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          ([--( v(2), v(6) )---> (#2 ++++ !!(varx)) ==== #0] **
           [--( v(2), v(6) )---> (#6 ++++ !!(varx)) ==== #0])
          (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: nil) 
          (eee, empty_heap) ->
     @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
     (SUM(range(#0, #4),
      (--( v(2), v(6) )---> (#2 ++++ v(8)) \\//
       --( v(2), v(6) )---> (#6 ++++ v(8))) //\\ nth(v(4), v(8)) ==== #0, 
      #1))
     (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: nil)
     (eee, empty_heap).
Proof.
    intros.

    eapply unfoldSum in H.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. instantiate (1 := (!!varx)) in H.
    simpl in H.
    destructState1.

    simplifyHyp H8.
    simplifyHyp H7.

    eapply unfoldSum.
    simpl. reflexivity. simpl. reflexivity. instantiate (1 := !!(varx)).

    Transparent basicEval. simpl. Opaque basicEval.
    simpl in H3. destruct (eee varx). reflexivity. destruct n. reflexivity. destruct n. reflexivity.
    destruct n. reflexivity. inversion H3.
    eapply RSExistsU. eapply ex_intro. eapply RSExistsU. eapply ex_intro. simpl.
    eapply RSCompose. apply H8. eapply RSCompose. apply H7.

    clear H8. clear H7.

    assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          ([#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(8))] **
          [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #0] *\/*
          ([#0 <<<< nth(replacenth(v(4), !!(varx), !!(valuex)), v(8))] *\/*
           [--( v(2), v(6) )---> (#2 ++++ v(8)) ==== #0] **
           [--( v(2), v(6) )---> (#6 ++++ v(8)) ==== #0]))
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: NatValue (eee varx) :: nil)
         (eee, empty_heap)).
    eapply H0.
    destruct (eee varx). simpl. left. reflexivity. destruct n. simpl. right. left. reflexivity.
    destruct n. right. right. left. reflexivity. destruct n. right. right. right. left. reflexivity.
    simpl in H3. inversion H3.
    assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
          ([#0 <<<< --( v(2), v(6) )---> (#10 ++++ (!!varx))] **
          [nth(replacenth(v(4), !!(varx), !!(valuex)), (!!varx)) ==== #0] *\/*
          ([#0 <<<< nth(replacenth(v(4), !!(varx), !!(valuex)), (!!varx))] *\/*
           [--( v(2), v(6) )---> (#2 ++++ (!!varx)) ==== #0] **
           [--( v(2), v(6) )---> (#6 ++++ (!!varx)) ==== #0]))
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: NatValue (eee varx) :: nil)
         (eee, empty_heap)).
    eapply removeQuantVar. apply H. instantiate (2 := 8). simpl. reflexivity. simpl. reflexivity.

    eapply expressionSubRSLR in H12. Focus 2. apply H10. Focus 2. simpl. reflexivity. Focus 2. simpl.
    reflexivity. Focus 2. simpl. reflexivity.
    eapply expressionSubRSLR in H12. Focus 2. apply H9. Focus 2. simpl. reflexivity. Focus 2. simpl.
    reflexivity. Focus 2. simpl. reflexivity.
    simplifyHyp H12.
    eapply expressionSubGRSLR. apply H9. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity.
    eapply expressionSubGRSLR. apply H10. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity.
    eapply simplifyEquiv2.
    compute. reflexivity. apply H12.
    apply concreteComposeEmpty. split. reflexivity. reflexivity.
    apply concreteComposeEmpty. split. reflexivity. reflexivity.


    Transparent basicEval. simpl. Opaque basicEval. destruct (eee varx).
    reflexivity. destruct n. reflexivity. destruct n. reflexivity. destruct n. reflexivity.
    destruct n. reflexivity. simpl in H3. inversion H3.
Qed.

