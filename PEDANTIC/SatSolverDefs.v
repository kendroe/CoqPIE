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

(* **************************************************************************
 *
 * Here is the example from the paper.  We start with some definitions for
 * the variables in the program.
 *
 ***************************************************************************)

Notation "'clauses'" := (Id 1001) (at level 1).
Notation "'assignments_to_do_head'" := (Id 1002) (at level 1).
Notation "'assignments_to_do_tail'" := (Id 1003) (at level 1).
Notation "'stack'" := (Id 1004) (at level 1).
Notation "'assignments'" := (Id 1005) (at level 1).
Notation "'watches'" := (Id 1006) (at level 1).
Notation "'backtrack'" := (Id 1007) (at level 1).
Notation "'iiii'" := (Id 1008) (at level 1).
Notation "'varx'" := (Id 1009) (at level 1).
Notation "'valuex'" := (Id 1010) (at level 1).
Notation "'have_var'" := (Id 1011) (at level 1).
Notation "'prop'" := (Id 1012) (at level 1).
Notation "'todo'" := (Id 1013) (at level 1).
Notation "'clause'" := (Id 1014) (at level 1).
Notation "'ssss'" := (Id 1015) (at level 1).
Notation "'vvvv'" := (Id 1016) (at level 1).
Notation "'val'" := (Id 1017) (at level 1).
Notation "'kkkk'" := (Id 1018) (at level 1).
Notation "'nc'" := (Id 1019) (at level 1).
Notation "'jjjj'" := (Id 1020) (at level 1).
Notation "'non_watch'" := (Id 1021) (at level 1).
Notation "'has_non_watch'" := (Id 1022) (at level 1).
Notation "'skip'" := (Id 1022) (at level 1).

Definition var_count := 4.

Definition next_offset := 0.
Definition positive_lit_offset := 1.
Definition negative_lit_offset := var_count + 1.
Definition watch_var_offset := var_count * 2 + 1.
Definition watch_next_offset := var_count * 3 + 1.
Definition watch_prev_offset := var_count * 4 + 1.

Definition sizeof_clause := var_count * 5 + 1.

Definition prev_offset := 1.
Definition todo_var_offset := 2.
Definition todo_val_offset := 3.
Definition todo_unit_offset := 4.

Definition sizeof_assignments_to_do := 5.

Definition stack_var_offset := 1.
Definition stack_val_offset := 2.
Definition stack_prop_offset := 3.

Definition sizeof_assignment_stack := 4.

Definition level := 0.
Definition domain (x : absExp) : absExp := #0.

(*Notation "'ForAllRecords' x 'in' r ',' y" :=
    (match level+1,v(level),(fun x => if beq_absExp x v(level) then r else domain x) with
     | level,x,domain => (AbsAll TreeRecords(r) y)
     | _,_,_ => AbsEmpty
     end) (at level 10).

Definition D := ForAllRecords a in v(0), ([find(a,@domain ev eq f a)====#0]).*)

(*Notation "x '====' y" := (AbsFun (Id 5) (x::y::nil))
  (at level 6).*)

Definition coreStructures : absState (* clauses assignments_to_do_head,stack,assignments,watches  *) :=
        TREE(v(5),v(0),#sizeof_clause,(#(next_offset)::nil)) **
        TREE(v(6),v(1),#sizeof_assignment_stack,(#(next_offset)::nil)) **
        TREE(v(7),v(2),#sizeof_assignment_stack,(#(next_offset)::nil)) **
        ARRAY(v(8),#var_count,v(3)) **
        ARRAY(v(9),#var_count,v(4)).

Definition treeInArray (* tr,ar,l *) : absState :=
        (AbsAll TreeRecords(v(0))
            ([--(v(S(0)),v(0))-->stack_var_offset <<<< #var_count] **
             ([--(v(S(0)),v(0))-->stack_val_offset ==== #1] *\/* [--(v(S(0)),v(0))-->stack_val_offset ==== #2]) **
             ([nth(v(S(1)),--(v(S(0)),v(0))-->stack_var_offset)====--(v(S(0)),v(0))-->stack_val_offset]) **
             (AbsAll TreeRecords(nth(find(v(S(0)),v(0)),#1))
                 ([~~(--(v(S(S(0))),v(1))-->stack_var_offset====--(nth(find(v(S(S(0))),v(1)),#1),v(0))-->stack_var_offset)])))).

Definition arrayInTree (* tr ar *) : absState :=
        (AbsAll range(#0,#(var_count))
            ([nth(v(S(1)),v(0))====#0] *\/*
             AbsExists (TreeRecords(v(S(0))))
                  ([(--(v(S(S(0))),v(0))-->stack_var_offset====v(1) //\\
                   --(v(S(S(0))),v(0))-->stack_val_offset====nth(v(S(S(1))),v(1)))]) )).

Definition treeEquivArray (* tr ar l *) : absState :=
    treeInArray **
    arrayInTree.

Definition validBackPointers (* tr *) prev_offset next_offset : absState :=
        (AbsAll TreeRecords(v(0))
            ([
              (--(v(S(0)),v(0))--->(prev_offset)====#0 //\\ (nth(v(S(0)),v(0))====v(0)) \\//
               (--(v(S(0)),v(0))--->(prev_offset) inTree v(0) //\\
                --(v(S(0)),--(v(S(0)),v(0))--->(prev_offset))--->(next_offset)====v(0)))
             ])).

Definition assignmentConsistent (*cl c a*) : absState :=
    (AbsExists range(#0,#(var_count))
        ([
(--(N(v(0)),N(v(1)))--->(#positive_lit_offset++++v(0)) //\\
           (nth(N(v(2)),v(0))====#2 \\// nth(N(v(2)),v(0))====#0)) \\//
          (--(N(v(0)),N(v(1)))--->(#negative_lit_offset++++v(6)) //\\
           (nth(N(v(2)),v(0))====#1 \\// nth(N(v(2)),v(0))====#0))
])).

Definition watchVariablesExists (*tr c*) : absState :=
            (AbsAll range(#0,#(var_count))
                ([
                 (--(v(0),v(1))--->(#watch_var_offset++++v(0))====#0) \\//
                  (--(v(0),v(1))--->(#positive_lit_offset++++v(0))) \\//
                  (--(v(0),v(1))--->(#negative_lit_offset++++v(0)))])).

Definition watchVariablesLinkedIffSet (*tr c a*) : absState :=
    (AbsAll range(#0,#(var_count))
        ([
             (~~(--(N(v(0)),N(v(1)))--->(#watch_var_offset++++v(0))====#0) //\\
             (~~(--(N(v(0)),N(v(1)))--->(#watch_prev_offset++++v(0))====#0) \\//
               nth(v(4),v(6))====v(5))) \\//
             (--(N(v(0)),N(v(1)))--->(#watch_var_offset++++v(0))====#0 //\\
              --(N(v(0)),N(v(1)))--->(#watch_prev_offset++++v(0))====#0 //\\
              ~~(nth(N(v(2)),v(0))====(N(v(1)))))])).

Definition twoWatchVariables (*tr c*) : absState :=
    (SUM(range(#0,#(var_count)),ite((--(v(0),v(1))--->(#watch_var_offset++++v(0))),(#1),(#0)),#2)).

Definition onlyOneUnassigned (*tr c a*) : absState :=
    SUM(range(#0,#(var_count)),
     (((--(N(v(0)),N(v(1)))--->(#positive_lit_offset++++v(0))) \\// (--(N(v(0)),N(v(1)))--->(#negative_lit_offset++++v(0)))) //\\
       ite(nth(v(2),v(0))====#0,#1,#0)),
     #1).

Definition unassignedVariablesAreWatches (*tr c a*) : absState :=
    (AbsAll range(#0,#(var_count))
       ([(#0<<<<--(N(v(0)),N(v(1)))--->(#watch_var_offset++++v(0)) //\\
         (nth(v(2),v(0))====#0)) \\//
         (
             ((#0<<<<nth(v(2),v(0))) \\// ((--(N(v(0)),N(v(1)))--->(#positive_lit_offset++++v(0))====#0 //\\
             --(N(v(0)),N(v(1)))--->(#negative_lit_offset++++v(0))====#0))))])).

Definition mostRecentAssignedIsWatch (*tr c a st*) : absState :=
    (AbsAll range(#0,#(var_count))
        (AbsAll range(#0,#(var_count))
            (([--(N(N(v(0))),N(N(v(1))))--->(#watch_var_offset++++v(0)) \\//
               ((((--(N(N(v(0))),N(N(v(1))))--->(#positive_lit_offset++++v(0)))====#0 //\\ (--(N(N(v(0))),N(N(v(1))))--->(#negative_lit_offset++++v(0))====#0)))) \\//
                        ~~(--(N(N(v(0))),N(N(v(1))))--->(#watch_var_offset++++v(1))) \\//
                        nth(N(N(v(2))),v(1))====#0 \\// nth(N(N(v(2))),v(1))====#0 \\// v(0)====v(1)]) *\/*
                      (AbsExists TreeRecords(N(N(v(3))))
                          (([--(N(N(N(v(3)))),v(0))-->stack_var_offset====v(2)]) **
                           (AbsExists TreeRecords(find(N(N(N(v(3)))),v(0)))
                              ([--(N(N(N(N(v(3))))),v(0))-->stack_var_offset====v(1)]))))))).

Definition allButOneAssigned (*tr c a st*) : absState :=
    onlyOneUnassigned **
    (* The one unassigned literal is a watch--needs fixing? *)
    unassignedVariablesAreWatches **
    mostRecentAssignedIsWatch.

Definition satisfyingAssignmentMade (*tr c a*) : absState :=
    (AbsExists range(#0,#(var_count))
        ([(--(N(v(0)),N(v(1)))--->(#positive_lit_offset++++v(0)) //\\ nth(N(v(2)),v(0))====#2) \\//
        (--(N(v(0)),N(v(1)))--->(#negative_lit_offset++++v(0)) //\\ nth(N(v(0)),N(v(1)))====#1)])).

Definition watchAfterSatisfyingAssignment (*tr c a st*) : absState :=
    (AbsAll range(#0,#(var_count))
        ([#0====nth(N(v(2)),v(0))] *\/*
         ([--(N(v(0)),N(v(1)))--->(#watch_var_offset++++v(0))====#0] **
          [#0<<<<nth(N(v(2)),v(0))]) *\/*
         (AbsExists TreeRecords(N(v(3)))
             ([--(N(N(v(3))),v(0))-->stack_var_offset====v(1)]) **
             (AbsExists TreeRecords(find(N(N(v(3))),v(0)))
                 ([
((#0 <<<< (--(N(N(v(0))),N(N(v(1))))--->(#positive_lit_offset++++ --(N(N(v(3))),v(0))-->stack_var_offset))) //\\ (--(N(N(v(3))),v(0))-->stack_val_offset====#2))
                      
\\//
((#0 <<<< (--(N(N(v(0))),N(N(v(1))))--->(#negative_lit_offset++++ --(N(N(v(3))),v(0))-->stack_var_offset))) //\\
                      (--(N(N(v(3))),v(0))-->stack_val_offset====#1))

]))
))).

Definition watchesUnassigned (*tr c a*) : absState :=
    (AbsAll range(#0,#(var_count))
        ([--(N(v(0)),N(v(1)))--->(#watch_var_offset++++v(0))====#0 \\// nth(N(v(2)),v(0))====#0])).

Definition watchesUnassignedOrV (*tr c a v*) : absState :=
    (AbsAll range(#0,#(var_count))
        ([--(N(v(0)),N(v(1)))--->(#watch_var_offset++++v(0))====#0 \\// v(0)====v(3) \\// nth(N(v(2)),v(0))====#0])).

Definition validTail (*t v*) : absState :=
    [v(1) inTree v(0)] ** [--(v(1),v(0))-->next_offset====#0].

Definition invariantCoreNoTail (* v0 v1 v2 v3 v4 clauses assignments_to_do stack assignments watches *): absState := (
        (AbsClosure coreStructures (v(0)::v(1)::v(2)::v(3)::v(4)::v(5)::v(6)::v(7)::v(8)::v(9)::nil)) **
        (* Assertions that the stack and assignments array contain the same set
           of assignments *)
        (AbsClosure treeEquivArray (v(2)::v(3)::nil)) **
        (* Assertion defining the prev pointer in the assignments_to_do
           doubly linked list *)
        (AbsClosure (validBackPointers (#prev_offset) (#next_offset)) (v(1)::nil)) **
        (AbsEach range(#0,#(var_count))
            (* Define the basic linked list connecting the watch variables
               inside the clauses linked list *)
            (AbsExistsT
                ((Path((nth(v(4),v(5))), v(0), v(6), #sizeof_clause, ((#watch_next_offset++++v(5))::nil))) **
                 (* Define the prev variable and the fact that if null we are at
                    the head of the list *)
                 (AbsClosure (validBackPointers (#watch_prev_offset++++v(5)) (#watch_next_offset++++v(5))) (v(6)::nil)) **
        (AbsAll TreeRecords(v(0))
            (* The current assignment is consistent with the clause *)
           (AbsClosure assignmentConsistent (v(0)::v(5)::v(3)::nil)) **
            (*
             * make sure that if the watch_var field is non-zero (pointing to
             * a variable) that watch_next and watch_prev put this clause into
             * the linked list for the watch variable.
             * Also, for all watch variables, either positive_lit or negative_lit
             * is true.
             *)
            (AbsClosure watchVariablesExists (v(0)::v(5)::nil)) **
            (AbsClosure watchVariablesLinkedIffSet (v(0)::v(5)::v(3)::nil)) **
            (* Make sure there are precisely two watch variables per clause or all variables are watches,
               needs fixing? *)
            (AbsClosure twoWatchVariables (v(0)::v(5)::nil)) **
            (* Watch variable invariant--case 1:  All but one variable in the
               clause are assigned, any watch variable pointing to an assigned
               variable is pointing to a variable that was assigned after all
               other assigned variables in the clause.  Also, one of the two
               watch variables points to the one unassigned variable *)
            ((AbsClosure allButOneAssigned (v(0)::v(5)::v(3)::v(2)::nil)) *\/*
            (* Watch variable invariant case 2: One of the assignments already
               satisfies the clause, if a watch variable is assigned a value,
               then that value must be a satisfying assignment or occured
               after a satisfying assignment *)
            ( (AbsClosure satisfyingAssignmentMade (v(0)::v(5)::v(3)::nil)) **
              (AbsClosure watchAfterSatisfyingAssignment (v(0)::v(5)::v(3)::v(2)::nil))) *\/*

            (* Watch variable invariant case 3: both watch variables point to
               unassigned variables *)
            (AbsClosure watchesUnassigned (v(0)::v(5)::v(3)::nil)))))))).

Definition invariantCoreNoTailWL (* v0 v1 v2 v3 v4 clauses assignments_to_do stack assignments watches *) l v : absState := (
        (AbsClosure coreStructures (v(0)::v(1)::v(2)::v(3)::v(4)::v(5)::v(6)::v(7)::v(8)::v(9)::nil)) **
        (* Assertions that the stack and assignments array contain the same set
           of assignments *)
        (AbsClosure treeEquivArray (v(2)::v(3)::nil)) **
        (* Assertion defining the prev pointer in the assignments_to_do
           doubly linked list *)
        (AbsClosure (validBackPointers (#prev_offset) (#next_offset)) (v(1)::nil)) **
        (AbsEach range(#0,#(var_count))
            (* Define the basic linked list connecting the watch variables
               inside the clauses linked list *)
            (AbsExistsT
                ((Path((nth(v(4),v(5))), v(0), v(6), #sizeof_clause, ((#watch_next_offset++++v(5))::nil))) **
                 (* Define the prev variable and the fact that if null we are at
                    the head of the list *)
                 (AbsClosure (validBackPointers (#watch_prev_offset++++v(5)) (#watch_next_offset++++v(5))) (v(6)::nil)) **
        (AbsAll TreeRecords(v(0))
            (* The current assignment is consistent with the clause *)
           (AbsClosure assignmentConsistent (v(0)::v(5)::v(3)::nil)) **
            (*
             * make sure that if the watch_var field is non-zero (pointing to
             * a variable) that watch_next and watch_prev put this clause into
             * the linked list for the watch variable.
             * Also, for all watch variables, either positive_lit or negative_lit
             * is true.
             *)
            (AbsClosure watchVariablesExists (v(0)::v(5)::nil)) **
            (AbsClosure watchVariablesLinkedIffSet (v(0)::v(5)::v(3)::nil)) **
            (* Make sure there are precisely two watch variables per clause or all variables are watches,
               needs fixing? *)
            (AbsClosure twoWatchVariables (v(0)::v(5)::nil)) **
            (* Watch variable invariant--case 1:  All but one variable in the
               clause are assigned, any watch variable pointing to an assigned
               variable is pointing to a variable that was assigned after all
               other assigned variables in the clause.  Also, one of the two
               watch variables points to the one unassigned variable *)
            ((AbsClosure allButOneAssigned (v(0)::v(5)::v(3)::v(2)::nil)) *\/*
            (* Watch variable invariant case 2: One of the assignments already
               satisfies the clause, if a watch variable is assigned a value,
               then that value must be a satisfying assignment or occured
               after a satisfying assignment *)
            ( (AbsClosure satisfyingAssignmentMade (v(0)::v(5)::v(3)::nil)) **
              (AbsClosure watchAfterSatisfyingAssignment (v(0)::v(5)::v(3)::v(2)::nil))) *\/*

            (* Watch variable invariant case 3: both watch variables point to
               unassigned variables *)
            ([v(0) inTree l] ** (AbsClosure watchesUnassignedOrV (v(0)::v(5)::v(3)::v::nil))))))))).

Definition iterate1 : absState := (AbsExists (range(#0,!!jjjj))
        ((([--(v(1),!!clause)--->(#watch_var_offset++++v(0))====#0]) **
          ([(nth(v(4),v(0))) ==== (#0)]) **
          [(!!non_watch) ==== (v(0))] **
          [(!!has_non_watch) ==== (#1)]) *\/* ([(!!has_non_watch) ==== (#0)]))).

Definition iterate2 : absState := (AbsAll (range(#0,!!kkkk))
        ([(#0) ==== (--(v(1),!!clause)--->(#watch_var_offset++++v(0)))]) *\/*
         [(#0) <<<< nth(v(4),v(0))] *\/*
         ([(#0) ==== (--(v(1),!!clause)--->(#positive_lit_offset++++v(0)))] **
          [(#0) ==== (--(v(1),!!clause)--->(#negative_lit_offset++++v(0)))]) **
          ([(!!val) ==== (#1)] *\/* [(!!val) ==== (#2)])).

Definition invariantCore: absState :=
        invariantCoreNoTail **
        (AbsClosure validTail (v(1)::v(6)::nil)).

Definition invariantCoreWL : absState :=
        (invariantCoreNoTailWL (find(!!clause,v(0)))) (!!varx) **
        (AbsClosure validTail (v(1)::v(6)::nil)).

Definition invariantWL (* clauses assignments_to_do stack assignments watches *) : absState :=
    (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsClosure invariantCoreWL((!!clauses)::(!!assignments_to_do_head)::(!!stack)::(!!assignments)::(!!watches)::v(0)::v(1)::v(2)::v(3)::v(4)::nil))))))).

Definition invariantWLIT1 (* clauses assignments_to_do stack assignments watches *): absState :=
    (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsClosure (invariantCoreWL ** iterate1) ((!!clauses)::(!!assignments_to_do_head)::(!!stack)::(!!assignments)::(!!watches)::v(0)::v(1)::v(2)::v(3)::v(4)::nil))))))).

Definition invariantWLIT2 (* clauses assignments_to_do stack assignments watches *) : absState :=
    (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsClosure (invariantCoreWL ** iterate2) ((!!clauses)::(!!assignments_to_do_head)::(!!stack)::(!!assignments)::(!!watches)::v(0)::v(1)::v(2)::v(3)::v(4)::nil))))))).

Definition invariant (* clauses assignments_to_do stack assignments watches *) : absState :=
    (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsClosure invariantCore (v(0)::v(1)::v(2)::v(3)::v(4)::(!!clauses)::(!!assignments_to_do_head)::(!!stack)::(!!assignments)::(!!watches)::nil))))))).

Definition loopInvariant (* clauses assignments_to_do stack assignments watches backtrack *) : absState :=
    (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsClosure (invariantCore ** ([(#0) <<<< v(7)] *\/* [v(10) ==== (#0)])) (v(0)::v(1)::v(2)::v(3)::v(4)::(!!clauses)::(!!assignments_to_do_head)::(!!stack)::(!!assignments)::(!!watches)::(!!backtrack)::nil))))))).

Definition invariantNoTail (* clauses assignments_to_do stack assignments watches*) : absState :=
    (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsClosure invariantCoreNoTail (v(0)::v(1)::v(2)::v(3)::v(4)::(!!clauses)::(!!assignments_to_do_head)::(!!stack)::(!!assignments)::(!!watches)::nil))))))).

Definition haveVarComponent : absState := ([v(11) ==== #0] *\/* [nth(v(3),(v(12)++++#1)) ==== #0]).

Definition haveVarInvariant: absState :=    (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsClosure (invariantCore ** haveVarComponent) (v(0)::v(1)::v(2)::v(3)::v(4)::(!!clauses)::(!!assignments_to_do_head)::(!!stack)::(!!assignments)::(!!watches)::(!!backtrack)::(!!have_var)::(!!varx)::nil))))))).

Definition finalState (x : nat) : absState :=
    (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (
        TREE(!!clauses,v(0),#sizeof_clause,(#next_offset::nil)) **
        TREE(!!assignments_to_do_head,v(1),#sizeof_assignment_stack,(#next_offset::nil)) **
        TREE(!!stack,v(2),#sizeof_assignment_stack,(#next_offset::nil)) **
        ARRAY(!!assignments,#var_count,v(3)) **
        ARRAY(!!watches,#var_count,v(4)) **
        (* Assertions that the stack and assignments array contain the same set
           of assignments *)
        (AbsAll TreeRecords(v(2))
            ([nth(v(3),--(v(2),v(5))-->stack_var_offset)====--(v(2),v(5))-->stack_val_offset])) **
        (AbsAll range(#0,#(var_count-1))
            ([nth(v(3),v(5))====#0] *\/*
             AbsExists (TreeRecords(v(2)))
                  ([(--(v(2),v(6))-->stack_var_offset====v(5) //\\
                   --(v(2),v(6))-->stack_val_offset====nth(v(3),v(5)))]) )) **
        (* Assertion defining the prev pointer in the assignments_to_do
           doubly linked list *)
        (AbsAll TreeRecords(v(1))
            ([(--(v(1),v(5))-->prev_offset====#0 //\\ (!!assignments_to_do_head)====v(5)) \\//
             (--(v(1),v(5))-->prev_offset inTree v(1) //\\
              --(v(1),--(v(1),v(5))-->prev_offset)-->next_offset====v(5))])) **
        (AbsEach range(#0,#(var_count-1))
            (* Define the basic linked list connecting the watch variables
               inside the clauses linked list *)
        (Path((nth(v(4),v(5))), v(0), v(6), #sizeof_clause, ((#watch_next_offset++++v(5))::nil)) **
         (* Define the prev variable and the fact that if null we are at
            the head of the list *)
         (AbsAll TreeRecords(v(6))
             ([(--(v(6),v(7))--->(#watch_prev_offset++++v(5))====#0 //\\ nth(v(4),v(5))====v(6)) \\//
               (--(v(6),--(v(6),v(7))--->(#watch_prev_offset++++v(5)))--->(#watch_next_offset++++v(5)))====v(7)]))) **
    (* All variables assigned (if x is non-zero) *)
    (if beq_nat x 0 then AbsEmpty else
    (AbsAll range(#0,#(var_count-1))
        ([nth(v(3),v(6))====#1 \\// nth(v(3),v(6))====#2]))) **
    (AbsEach TreeRecords(v(0))
        (* The current assignment is consistent with the clause *)
        (AbsExists range(#0,#(var_count-1))
             ([(--(v(0),v(5))--->(#positive_lit_offset++++v(6)) //\\
                  (nth(v(3),v(6))====#2 \\// nth(v(3),v(6))====#0)) \\//
               (--(v(0),v(5))--->(#negative_lit_offset++++v(6)) //\\
                  (nth(v(3),v(6))====#1 \\// nth(v(3),v(6))====#0))])) **
        (*
         * make sure that if the watch_var field is non-zero (pointing to
         * a variable) that watch_next and watch_prev put this clause into
         * the linked list for the watch variable.
         *)
        (AbsAll range(#0,#(var_count-1))
             ([
              (~~(--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0) //\\
               (~~(--(v(0),v(5))--->(#watch_prev_offset++++v(6))====#0) \\//
                nth(v(4),v(6))====v(5))) \\//
              (--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0 //\\
               --(v(0),v(5))--->(#watch_prev_offset++++v(6))====#0 //\\
               ~~(nth(v(4),v(6))====v(5)))]) **
        (* Make sure there are precisely two watch variables per clause or all variables are watches*)
        (SUM(range(#0,#(var_count-1)),ite((--(v(5),v(0))--->(#watch_var_offset++++v(6))),(#1),(#0)),#2) *\/*
         (AbsAll range(#0,#(var_count-1)) ([(--(v(5),v(0))--->(#watch_var_offset++++v(6)))]))) **
        (* Watch variable invariant--case 1:  All but one variable in the
           clause are assigned, any watch variable pointing to an assigned
           variable is pointing to a variable that was assigned after all
           other assigned variables in the clause.  Also, one of the two
           watch variables points to the one unassigned variable *)
        ((((SUM(range(#0,#(var_count-1)),
            ((--(v(0),v(5))--->(#positive_lit_offset++++v(6))) //\\
                 ite(nth(v(3),v(6))====#1,#1,#0))++++
            ((--(v(0),v(5))--->(#negative_lit_offset++++v(6))) //\\ ite(nth(v(3),v(6))====#2,#1,#0)),
            (* Needs fixing *)
            #(var_count-1)) **
         (* The one unassigned literal is a watch *)
         (AbsAll range(#0,#(var_count-1))
             ([#0<<<<--(v(0),v(5))--->(#watch_var_offset++++v(6)) \\//
             nth(v(3),v(6))====#0])) **
         (AbsAll range(#0,#(var_count-1))
             (AbsAll range(#0,#(var_count-1))
                 (([--(v(0),v(5))--->(#watch_var_offset++++v(6)) \\//
                   ~~(--(v(0),v(5))--->(#watch_var_offset++++v(7))) \\//
                   nth(v(3),v(6))====#0 \\// nth(v(3),v(7))====#0 \\// v(6)====v(7)]) *\/*
                  (AbsExists TreeRecords(v(2))
                      ([--(v(2),v(8))-->stack_var_offset====v(6)]) **
                      (AbsExists TreeRecords(find(v(2),v(8)))
                          ([--(v(2),v(9))-->stack_var_offset====v(7)]))))))))) *\/*
         (* Watch variable invariant case 2: One of the assignments already
            satisfies the clause, if a watch variable is assigned a value,
            then that value must be a satisfying assignment or occured
            after a satisfying assignment *)
         ( (AbsExists range(#0,#(var_count-1))
            ([(--(v(0),v(5))--->(#positive_lit_offset++++v(6)) //\\ nth(v(3),v(6))====#2) \\//
              (--(v(0),v(5))--->(#negative_lit_offset++++v(6)) //\\ nth(v(3),v(6))====#1)])) **
            (AbsAll range(#0,#(var_count-1))
              (([--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0]) *\/*
                (AbsExists TreeRecords(v(2))
                  (([--(v(2),v(7))-->stack_var_offset====v(6)]) **
                   (AbsExists find(v(2),v(7))
                       ([((#0 <<<< (--(v(0),v(5))--->(#positive_lit_offset++++ --(v(2),v(8))-->stack_var_offset))) //\\
                          --(v(2),v(8))-->stack_val_offset====#2) \\//
                         ((#0 <<<< --(v(0),v(5))--->(#negative_lit_offset++++ --(v(2),v(8))-->stack_var_offset)) //\\
                          --(v(2),v(8))-->stack_val_offset====#1)]))))))) *\/*

         (* Watch variable invariant case 3: both watch variables point to
            unassigned variables *)
         (AbsAll range(#0,#(var_count-1))
             ([--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0 \\// nth(v(3),v(6))====#0]))

)))))))))).


Definition Program :=
    backtrack ::= ANum(0);
    WHILE ANum(1) DO
        have_var ::= ANum(0);
        IF (!backtrack) THEN
            backtrack ::= A0;
            (CLoad varx (!stack+++ANum(stack_var_offset)));
            (CLoad valuex (!stack+++ANum(stack_val_offset)));
            (CLoad ssss (!stack+++ANum(next_offset)));
            DELETE !stack,ANum(sizeof_assignment_stack);
            stack ::= !ssss;
            have_var ::= A1;
            (CStore (!assignments+++!varx) A0)
        ELSE
            valuex ::= A1;
            iiii ::= A0;
            WHILE (!iiii <<= ANum(var_count)) DO
                (CLoad ssss (!assignments+++!iiii));
                IF (!ssss===A0) THEN
                    varx ::= !iiii;
                    have_var ::= A1
                ELSE
                    SKIP
                FI;
                iiii ::= !iiii +++ A1
            LOOP
        FI;
        IF (!have_var===A0) THEN
            RETURN A1
        ELSE
            SKIP
        FI;
        NEW todo,ANum(sizeof_assignments_to_do);
        (CStore (!todo+++ANum(next_offset)) (!assignments_to_do_head));
        (CStore (!todo+++ANum(prev_offset)) A0);
        IF (!assignments_to_do_tail===A0) THEN
            assignments_to_do_tail ::= !todo
        ELSE
            (CStore (!assignments_to_do_head+++ANum(prev_offset)) (!todo))
        FI;
        assignments_to_do_head ::= !todo;
        (CStore (!todo+++ANum(todo_var_offset)) (!varx));
        (CStore (!todo+++ANum(todo_val_offset)) (!valuex));
        (CStore (!todo+++ANum(todo_unit_offset)) A0);
        WHILE !assignments_to_do_tail DO
            (CLoad varx (!assignments_to_do_tail+++ANum(todo_var_offset)));
            (CLoad valuex (!assignments_to_do_tail+++ANum(todo_val_offset)));
            (CLoad prop (!assignments_to_do_tail+++ANum(todo_unit_offset)));
            (CLoad ssss (!assignments_to_do_tail+++ANum(prev_offset)));
            IF !ssss THEN
                assignments_to_do_tail ::= !ssss;
                (CStore (!ssss+++ANum(next_offset-1)) A0);
                DELETE !ssss,(ANum(sizeof_assignments_to_do))
            ELSE
                DELETE !ssss,(ANum(sizeof_assignments_to_do));
                assignments_to_do_head ::= A0;
                assignments_to_do_tail ::= A0
            FI;
            (CLoad ssss (!assignments+++!varx));
            IF !ssss THEN
                (CIf ((!ssss)===(!valuex))
                    (SKIP)
                    (WHILE (!assignments_to_do_head) DO
                        (CLoad todo (!assignments_to_do_head +++ ANum(next_offset)));
                        DELETE !assignments_to_do_head,ANum(sizeof_assignments_to_do);
                        assignments_to_do_head ::= !todo
                    LOOP;
                    assignments_to_do_tail ::= A0;
                    (CLoad ssss (!stack +++ ANum(stack_prop_offset)));
                    (CLoad vvvv (!stack +++ ANum(stack_val_offset)));
                    WHILE (ALand (!stack) (ALor (!ssss) (!vvvv===A2))) DO
                        (CLoad kkkk (!stack +++ ANum(next_offset)));
                        (CLoad vvvv (!stack +++ ANum(stack_var_offset)));
                        (CStore (!assignments +++ !vvvv) A0);
                        DELETE !stack,ANum(sizeof_assignment_stack);
                        stack ::= !kkkk;
                        (CLoad ssss (!stack +++ ANum(stack_prop_offset)));
                        (CLoad vvvv (!stack +++ ANum(stack_val_offset)))
                    LOOP;
                    IF (!stack===A0) THEN
                        RETURN A0
                    ELSE
                        SKIP
                    FI;
                    (CStore (!stack +++ ANum(stack_val_offset-1)) A2);
                    (CLoad vvvv (!stack +++ ANum(stack_var_offset)));
                    (CStore (!assignments +++ !vvvv) A2);
                    backtrack ::= A1))
            ELSE
                (CStore (!assignments+++!varx) (!valuex));
                NEW ssss,ANum(sizeof_assignment_stack);
                (CStore (!ssss+++ANum(next_offset-1)) (!stack));
                stack ::= !ssss;
                (CStore (!ssss+++ANum(stack_var_offset-1)) (!varx));
                (CStore (!ssss+++ANum(stack_val_offset-1)) (!valuex));
                (CStore (!ssss+++ANum(stack_prop_offset-1)) (!prop));
                (CLoad clause (!watches+++!varx));
                WHILE (!clause) DO
                    (CLoad nc (!clause+++ANum(watch_next_offset)+++!varx));
                    (CLoad ssss (!clause+++ANum(negative_lit_offset)+++!varx));
                    (CLoad vvvv (!clause+++ANum(positive_lit_offset)+++!varx));
                    IF (ALor (ALand (!valuex === A2) (!ssss))
                             (ALand (!valuex === A1) (!vvvv))) THEN
                        has_non_watch ::= A0;
                        skip ::= A0;
                        jjjj ::= A0;
                        WHILE (!jjjj <<= ANum(var_count-1)) DO
                            jjjj ::= !jjjj +++ A1;
                            (CLoad ssss (!clause+++ANum(positive_lit_offset)+++!jjjj));
                            (CLoad vvvv (!assignments+++!jjjj));
                            IF (ALand (!ssss) (!vvvv===A2)) THEN
                                skip ::= A1
                            ELSE
                                SKIP
                            FI;
                            (CLoad ssss (!clause+++ANum(negative_lit_offset)+++!jjjj));
                            IF (ALand (!ssss) (!vvvv===A1)) THEN
                                skip ::= A1
                            ELSE
                                SKIP
                            FI;
                            (CLoad ssss (!clause+++ANum(watch_var_offset)+++!jjjj));
                            IF (ALand (!vvvv) (!ssss===A0)) THEN
                                non_watch ::= !jjjj;
                                has_non_watch ::= A1
                            ELSE
                                SKIP
                            FI
                        LOOP;
                        IF (!skip) THEN
                            SKIP
                        ELSE
                            SKIP;
                            IF (!has_non_watch) THEN
                                (CLoad ssss (!watches +++ !non_watch));
                                (CStore (!clause +++ ANum(watch_next_offset) +++ !non_watch) (!ssss));
                                (CStore (!clause +++ ANum(watch_var_offset) +++ !non_watch) A1);
                                IF (!ssss) THEN
                                    (CStore (!ssss +++ ANum(watch_prev_offset) +++ !non_watch) (!clause))
                                ELSE
                                    SKIP
                                FI;
                                (CStore (!watches +++ !non_watch) (!clause));
                                (CStore (!clause +++ ANum(watch_var_offset) +++ !varx) A0);
                                (CLoad ssss (!clause +++ ANum(watch_prev_offset) +++ !varx));
                                (CLoad vvvv (!clause +++ ANum(watch_next_offset) +++ !varx));
                                IF (!ssss) THEN
                                    (CStore (!ssss +++ ANum(watch_next_offset) +++ !varx) (!vvvv))
                                ELSE
                                    (CStore (!watches +++ !varx) (!vvvv))
                                FI;
                                IF (!vvvv) THEN
                                    (CStore (!vvvv +++ ANum(watch_prev_offset) +++ !varx) (!ssss))
                                ELSE
                                    SKIP
                                FI
                            ELSE
                                kkkk ::= A0;
                                WHILE (!kkkk <<= ANum(var_count)) DO
                                    (CLoad ssss (!clause +++ ANum(watch_var_offset) +++ !kkkk));
                                    (CLoad jjjj (!assignments +++ !kkkk));
                                    IF (ALand (!ssss) ((!jjjj)===A0)) THEN
                                        vvvv ::= !kkkk;
                                        (CLoad ssss (!clause +++ ANum(positive_lit_offset) +++ !vvvv));
                                        IF (!ssss) THEN
                                            val ::= A2
                                        ELSE
                                            SKIP
                                        FI;
                                        (CLoad ssss (!clause +++ ANum(negative_lit_offset) +++ !vvvv));
                                        IF (!ssss) THEN
                                            val ::= A1
                                        ELSE
                                            SKIP
                                        FI
                                    ELSE
                                        SKIP
                                    FI;
                                    kkkk ::= !kkkk +++ A1
                                LOOP;
                                NEW todo,ANum(sizeof_assignments_to_do);
                                (CStore (!todo +++ ANum(next_offset)) (!assignments_to_do_head));
                                (CStore (!todo +++ ANum(prev_offset)) A0);
                                IF (!assignments_to_do_tail) THEN
                                    (CStore (!assignments_to_do_head +++ ANum(prev_offset)) (!todo))
                                ELSE
                                    assignments_to_do_tail ::= !todo
                                FI;
                                assignments_to_do_head ::= !todo;
                                (CStore (!todo +++ ANum(todo_var_offset-1)) (!vvvv));
                                (CStore (!todo +++ ANum(todo_val_offset-1)) (!val));
                                (CStore (!todo +++ ANum(todo_unit_offset-1)) A1)
                            FI
                        FI
                    ELSE
                        SKIP
                    FI;
                    clause ::= !nc
                LOOP
            FI
        LOOP
    LOOP.


















































































