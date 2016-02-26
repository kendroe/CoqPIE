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

Notation "'clauses'" := (Id 1) (at level 1).
Notation "'assignments_to_do_head'" := (Id 2) (at level 1).
Notation "'assignments_to_do_tail'" := (Id 3) (at level 1).
Notation "'stack'" := (Id 4) (at level 1).
Notation "'assignments'" := (Id 5) (at level 1).
Notation "'watches'" := (Id 6) (at level 1).
Notation "'backtrack'" := (Id 7) (at level 1).
Notation "'iiii'" := (Id 8) (at level 1).
Notation "'varx'" := (Id 9) (at level 1).
Notation "'valuex'" := (Id 10) (at level 1).
Notation "'have_var'" := (Id 11) (at level 1).
Notation "'prop'" := (Id 12) (at level 1).
Notation "'todo'" := (Id 13) (at level 1).
Notation "'clause'" := (Id 14) (at level 1).
Notation "'ssss'" := (Id 15) (at level 1).
Notation "'vvvv'" := (Id 16) (at level 1).
Notation "'val'" := (Id 17) (at level 1).
Notation "'kkkk'" := (Id 18) (at level 1).
Notation "'nc'" := (Id 19) (at level 1).
Notation "'jjjj'" := (Id 20) (at level 1).
Notation "'non_watch'" := (Id 21) (at level 1).
Notation "'has_non_watch'" := (Id 22) (at level 1).
Notation "'skip'" := (Id 22) (at level 1).

Definition var_count := 4.

Definition next_offset := 1.
Definition positive_lit_offset := 2.
Definition negative_lit_offset := var_count + 2.
Definition watch_var_offset := var_count * 2 + 2.
Definition watch_next_offset := var_count * 3 + 2.
Definition watch_prev_offset := var_count * 4 + 2.

Definition sizeof_clause := var_count * 5 + 1.

Definition prev_offset := 2.
Definition todo_var_offset := 3.
Definition todo_val_offset := 4.
Definition todo_unit_offset := 5.

Definition sizeof_assignments_to_do := 5.

Definition stack_var_offset := 2.
Definition stack_val_offset := 3.
Definition stack_prop_offset := 4.

Definition sizeof_assignment_stack := 4.

Definition level := 0.
Definition domain {ev} {eq} {f} (x : @absExp ev eq f) : (@absExp ev eq f) := #0.

(*Notation "'ForAllRecords' x 'in' r ',' y" :=
    (match level+1,v(level),(fun x => if beq_absExp x v(level) then r else domain x) with
     | level,x,domain => (AbsAll TreeRecords(r) y)
     | _,_,_ => AbsEmpty
     end) (at level 10).

Definition D {ev} {eq} {f} := ForAllRecords a in v(0), ([find(a,@domain ev eq f a)====#0]).*)

(*Notation "x '====' y" := (AbsFun (Id 5) (x::y::nil))
  (at level 6).*)

Definition invariant: absStateBasic :=
    (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (
        TREE(!!clauses,v(0),#sizeof_clause,(#next_offset::nil)) **
        TREE(!!assignments_to_do_head,v(1),#sizeof_assignment_stack,(#next_offset::nil)) **
        TREE(!!stack,v(2),#sizeof_assignment_stack,(#next_offset::nil)) **
        ARRAY(!!assignments,#var_count,v(3)) **
        ARRAY(!!watches,#var_count,v(4)) **
        (* Assertions that the stack and assignments array contain the same set
           of assignments *)
        (AbsAll TreeRecords(v(2))
            ([--(v(2),v(5))-->stack_var_offset <<<< #var_count] **
             ([--(v(2),v(5))-->stack_val_offset ==== #1] *\/* [--(v(2),v(5))-->stack_val_offset ==== #2]) **
             ([nth(v(3),--(v(2),v(5))-->stack_var_offset)====--(v(2),v(5))-->stack_val_offset]) **
             (AbsAll TreeRecords(nth(find(v(2),v(5)),#2))
                 ([~~(--(v(2),v(5))-->stack_var_offset====--(nth(find(v(2),v(5)),#2),v(6))-->stack_var_offset)])))) **
        (AbsAll range(#0,#(var_count))
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
        (AbsEach range(#0,#(var_count))
            (* Define the basic linked list connecting the watch variables
               inside the clauses linked list *)
            (AbsExistsT
                ((Path((nth(v(4),v(5))), v(0), v(6), #sizeof_clause, ((#watch_next_offset++++v(5))::nil))) **
                 (* Define the prev variable and the fact that if null we are at
                    the head of the list *)
                 (AbsAll TreeRecords(v(6))
                     ([(--(v(6),v(7))--->(#watch_prev_offset++++v(5))====#0 //\\ nth(v(4),v(5))====v(6)) \\//
                      (--(v(6),--(v(6),v(7))--->(#watch_prev_offset++++v(5)))--->(#watch_next_offset++++v(5)))====v(7)]))))) **
        (AbsAll TreeRecords(v(0))
            (* The current assignment is consistent with the clause *)
           ((AbsExists range(#0,#(var_count))
                ([(--(v(0),v(5))--->(#positive_lit_offset++++v(6)) //\\
                    (nth(v(3),v(6))====#2 \\// nth(v(3),v(6))====#0)) \\//
                  (--(v(0),v(5))--->(#negative_lit_offset++++v(6)) //\\
                    (nth(v(3),v(6))====#1 \\// nth(v(3),v(6))====#0))])) **
            (*
             * make sure that if the watch_var field is non-zero (pointing to
             * a variable) that watch_next and watch_prev put this clause into
             * the linked list for the watch variable.
             * Also, for all watch variables, either positive_lit or negative_lit
             * is true.
             *)
            (AbsAll range(#0,#(var_count))
                ([
                 (--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0) \\//
                  (--(v(0),v(5))--->(#positive_lit_offset++++v(6))) \\//
                  (--(v(0),v(5))--->(#negative_lit_offset++++v(6)))])) **
            (AbsAll range(#0,#(var_count))
                ([
                 (~~(--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0) //\\
                 (~~(--(v(0),v(5))--->(#watch_prev_offset++++v(6))====#0) \\//
                   nth(v(4),v(6))====v(5))) \\//
                 (--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0 //\\
                  --(v(0),v(5))--->(#watch_prev_offset++++v(6))====#0 //\\
                  ~~(nth(v(4),v(6))====v(5)))])) **
            (* Make sure there are precisely two watch variables per clause or all variables are watches,
               needs fixing? *)
            (SUM(range(#0,#(var_count)),ite((--(v(0),v(5))--->(#watch_var_offset++++v(6))),(#1),(#0)),#2)) **
            (* Watch variable invariant--case 1:  All but one variable in the
               clause are assigned, any watch variable pointing to an assigned
               variable is pointing to a variable that was assigned after all
               other assigned variables in the clause.  Also, one of the two
               watch variables points to the one unassigned variable *)
            ((((SUM(range(#0,#(var_count)),
              (((--(v(0),v(5))--->(#positive_lit_offset++++v(6))) \\// (--(v(0),v(5))--->(#negative_lit_offset++++v(6)))) //\\
                   ite(nth(v(3),v(6))====#0,#1,#0)),
               #1) **
            (* The one unassigned literal is a watch--needs fixing? *)
            (AbsAll range(#0,#(var_count))
                 ([(#0<<<<--(v(0),v(5))--->(#watch_var_offset++++v(6)) //\\
                   (nth(v(3),v(6))====#0)) \\//
                   (
                    ((#0<<<<nth(v(3),v(6))) \\// ((--(v(0),v(5))--->(#positive_lit_offset++++v(6))====#0 //\\
                    --(v(0),v(5))--->(#negative_lit_offset++++v(6))====#0))))])) **
            (AbsAll range(#0,#(var_count))
                 (AbsAll range(#0,#(var_count))
                     (([--(v(0),v(5))--->(#watch_var_offset++++v(6)) \\//
                        ((((--(v(0),v(5))--->(#positive_lit_offset++++v(6)))====#0 //\\ (--(v(0),v(5))--->(#negative_lit_offset++++v(6))====#0)))) \\//
                        ~~(--(v(0),v(5))--->(#watch_var_offset++++v(7))) \\//
                        nth(v(3),v(6))====#0 \\// nth(v(3),v(7))====#0 \\// v(6)====v(7)]) *\/*
                      (AbsExists TreeRecords(v(2))
                          (([--(v(2),v(8))-->stack_var_offset====v(7)]) **
                           (AbsExists TreeRecords(find(v(2),v(8)))
                              ([--(v(2),v(9))-->stack_var_offset====v(6)])))))))))) *\/*
            (* Watch variable invariant case 2: One of the assignments already
               satisfies the clause, if a watch variable is assigned a value,
               then that value must be a satisfying assignment or occured
               after a satisfying assignment *)
            ( (AbsExists range(#0,#(var_count))
                ([(--(v(0),v(5))--->(#positive_lit_offset++++v(6)) //\\ nth(v(3),v(6))====#2) \\//
                  (--(v(0),v(5))--->(#negative_lit_offset++++v(6)) //\\ nth(v(3),v(6))====#1)])) **
              (AbsAll range(#0,#(var_count))
                ((([#0====nth(v(3),v(6))]) *\/*
                  ([--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0]) **
                  ([#0<<<<nth(v(3),v(6))])) *\/*
                  (AbsExists TreeRecords(v(2))
                    (([--(v(2),v(7))-->stack_var_offset====v(6)]) **
                      (AbsExists TreeRecords(find(v(2),v(7)))
                        ([((#0 <<<< (--(v(0),v(5))--->(#positive_lit_offset++++ --(v(2),v(8))-->stack_var_offset))) //\\
                          --(v(2),v(8))-->stack_val_offset====#2) \\//
                        ((#0 <<<< --(v(0),v(5))--->(#negative_lit_offset++++ --(v(2),v(8))-->stack_var_offset)) //\\
                         --(v(2),v(8))-->stack_val_offset====#1)]))))))) *\/*

         (* Watch variable invariant case 3: both watch variables point to
            unassigned variables *)
         (AbsAll range(#0,#(var_count))
             ([--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0 \\// nth(v(3),v(6))====#0]))
))))))))).

Definition invariant1: absStateBasic :=
    (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (AbsExistsT (
        TREE(!!clauses,v(0),#sizeof_clause,(#next_offset::nil)) **
        TREE(!!assignments_to_do_head,v(1),#sizeof_assignment_stack,(#next_offset::nil)) **
        TREE(!!stack,v(2),#sizeof_assignment_stack,(#next_offset::nil)) **
        ARRAY(!!assignments,#var_count,v(3)) **
        ARRAY(!!watches,#var_count,v(4)) **
        ([(!!valuex)====#1]) **
        ([(~~ (!!have_var)) \\// (nth(v(3),!!varx)====#0 //\\ (((!!valuex)====#1) \\// ((!!valuex)====#2)))]) **
        (* Assertions that the stack and assignments array contain the same set
           of assignments *)
        (AbsAll TreeRecords(v(2))
            ([--(v(2),v(5))-->stack_var_offset <<<< #var_count] **
             ([--(v(2),v(5))-->stack_val_offset ==== #1] *\/* [--(v(2),v(5))-->stack_val_offset ==== #2]) **
             ([nth(v(3),--(v(2),v(5))-->stack_var_offset)====--(v(2),v(5))-->stack_val_offset]) **
             (AbsAll TreeRecords(nth(find(v(2),v(5)),#2))
                 ([~~(--(v(2),v(5))-->stack_var_offset====--(nth(find(v(2),v(5)),#2),v(6))-->stack_var_offset)])))) **
        (AbsAll range(#0,#(var_count))
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
        (AbsEach range(#0,#(var_count))
            (* Define the basic linked list connecting the watch variables
               inside the clauses linked list *)
            (AbsExistsT
                ((Path((nth(v(4),v(5))), v(0), v(6), #sizeof_clause, ((#watch_next_offset++++v(5))::nil))) **
                 (* Define the prev variable and the fact that if null we are at
                    the head of the list *)
                 (AbsAll TreeRecords(v(6))
                     ([(--(v(6),v(7))--->(#watch_prev_offset++++v(5))====#0 //\\ nth(v(4),v(5))====v(6)) \\//
                      (--(v(6),--(v(6),v(7))--->(#watch_prev_offset++++v(5)))--->(#watch_next_offset++++v(5)))====v(7)]))))) **
        (AbsAll TreeRecords(v(0))
            (* The current assignment is consistent with the clause *)
           ((AbsExists range(#0,#(var_count))
                ([(--(v(0),v(5))--->(#positive_lit_offset++++v(6)) //\\
                    (nth(v(3),v(6))====#2 \\// nth(v(3),v(6))====#0)) \\//
                  (--(v(0),v(5))--->(#negative_lit_offset++++v(6)) //\\
                    (nth(v(3),v(6))====#1 \\// nth(v(3),v(6))====#0))])) **
            (*
             * make sure that if the watch_var field is non-zero (pointing to
             * a variable) that watch_next and watch_prev put this clause into
             * the linked list for the watch variable.
             *)
            (AbsAll range(#0,#(var_count))
                ([
                 (--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0) \\//
                  ~~ (--(v(0),v(5))--->(#positive_lit_offset++++v(6))) \\//
                  ~~ (--(v(0),v(5))--->(#negative_lit_offset++++v(6)))])) **
            (AbsAll range(#0,#(var_count))
                ([
                 (~~(--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0) //\\
                 (~~(--(v(0),v(5))--->(#watch_prev_offset++++v(6))====#0) \\//
                   nth(v(4),v(6))====v(5))) \\//
                 (--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0 //\\
                  --(v(0),v(5))--->(#watch_prev_offset++++v(6))====#0 //\\
                  ~~(nth(v(4),v(6))====v(5)))])) **
            (* Make sure there are precisely two watch variables per clause *)
            (SUM(range(#0,#(var_count)),ite((--(v(0),v(5))--->(#watch_var_offset++++v(6))),(#1),(#0)),#2)) **
            (* Watch variable invariant--case 1:  All but one variable in the
               clause are assigned, any watch variable pointing to an assigned
               variable is pointing to a variable that was assigned after all
               other assigned variables in the clause.  Also, one of the two
               watch variables points to the one unassigned variable *)
            ((((SUM(range(#0,#(var_count)),
              (((--(v(0),v(5))--->(#positive_lit_offset++++v(6))) \\// (--(v(0),v(5))--->(#negative_lit_offset++++v(6)))) //\\
                   ite(nth(v(3),v(6))====#0,#1,#0)),
               #1) **
            (* The one unassigned literal is a watch--needs fixing? *)
            (AbsAll range(#0,#(var_count))
                 ([(#0<<<<--(v(0),v(5))--->(#watch_var_offset++++v(6)) //\\
                   (nth(v(3),v(6))====#0) \\//
                    ((#0<<<<nth(v(3),v(6))) \\// ((--(v(0),v(5))--->(#positive_lit_offset++++v(6))====#0 //\\
                    --(v(0),v(5))--->(#negative_lit_offset++++v(6))====#0))))])) **
            (AbsAll range(#0,#(var_count))
                 (AbsAll range(#0,#(var_count))
                     (([--(v(0),v(5))--->(#watch_var_offset++++v(6)) \\//
                        ((((--(v(0),v(5))--->(#positive_lit_offset++++v(6)))====#0 //\\ (--(v(0),v(5))--->(#negative_lit_offset++++v(6))====#0)))) \\//
                        ~~(--(v(0),v(5))--->(#watch_var_offset++++v(7))) \\//
                        nth(v(3),v(6))====#0 \\// nth(v(3),v(7))====#0 \\// v(6)====v(7)]) *\/*
                      (AbsExists TreeRecords(v(2))
                          (([--(v(2),v(8))-->stack_var_offset====v(7)]) **
                           (AbsExists TreeRecords(find(v(2),v(8)))
                              ([--(v(2),v(9))-->stack_var_offset====v(6)])))))))))) *\/*
            (* Watch variable invariant case 2: One of the assignments already
               satisfies the clause, if a watch variable is assigned a value,
               then that value must be a satisfying assignment or occured
               after a satisfying assignment *)
            ( (AbsExists range(#0,#(var_count))
                ([(--(v(0),v(5))--->(#positive_lit_offset++++v(6)) //\\ nth(v(3),v(6))====#2) \\//
                  (--(v(0),v(5))--->(#negative_lit_offset++++v(6)) //\\ nth(v(3),v(6))====#1)])) **
              (AbsAll range(#0,#(var_count))
                (([#0====nth(v(3),v(6))] *\/* 
                  [--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0] **
                  [#0 <<<< nth(v(3),v(6))]) *\/*
                  (AbsExists TreeRecords(v(2))
                    (([--(v(2),v(7))-->stack_var_offset====v(6)]) **
                      (AbsExists TreeRecords(find(v(2),v(7)))
                        ([((#0 <<<< (--(v(0),v(5))--->(#positive_lit_offset++++ --(v(2),v(8))-->stack_var_offset))) //\\
                          --(v(2),v(8))-->stack_val_offset====#2) \\//
                        ((#0 <<<< --(v(0),v(5))--->(#negative_lit_offset++++ --(v(2),v(8))-->stack_var_offset)) //\\
                         --(v(2),v(8))-->stack_val_offset====#1)]))))))) *\/*

         (* Watch variable invariant case 3: both watch variables point to
            unassigned variables *)
         (AbsAll range(#0,#(var_count))
             ([--(v(0),v(5))--->(#watch_var_offset++++v(6))====#0 \\// nth(v(3),v(6))====#0]))
))))))))).

Definition finalState (x : nat) : absStateBasic :=
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
            WHILE (!iiii <<= ANum(var_count-1)) DO
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
                DELETE !ssss,(ANum(sizeof_assignments_to_do));
                assignments_to_do_tail ::= !ssss;
                (CStore (!ssss+++ANum(next_offset)) A0)
            ELSE
                assignments_to_do_head ::= A0;
                assignments_to_do_tail ::= A0
            FI;
            (CLoad ssss (!assignments+++!varx));
            IF !ssss THEN
                WHILE (!assignments_to_do_head) DO
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
                (CStore (!stack +++ ANum(stack_val_offset)) A2);
                (CLoad vvvv (!stack +++ ANum(stack_var_offset)));
                (CStore (!assignments +++ !vvvv) A2);
                backtrack ::= A1
            ELSE
                (CStore (!assignments+++!varx) (!valuex));
                NEW ssss,ANum(sizeof_assignment_stack);
                (CStore (!ssss+++ANum(next_offset)) (!stack));
                stack ::= !ssss;
                (CStore (!ssss+++ANum(stack_var_offset)) (!varx));
                (CStore (!ssss+++ANum(stack_val_offset)) (!valuex));
                (CStore (!ssss+++ANum(stack_prop_offset)) (!prop));
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
                                WHILE (!kkkk <<= ANum(var_count-1)) DO
                                    (CLoad ssss (!clause +++ ANum(watch_var_offset) +++ !kkkk));
                                    (CLoad jjjj (!assignments +++ !kkkk));
                                    IF (ALand (!ssss) (!jjjj)) THEN
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
                                (CStore (!todo +++ ANum(todo_var_offset)) (!vvvv));
                                (CStore (!todo +++ ANum(todo_val_offset)) (!val));
                                (CStore (!todo +++ ANum(todo_unit_offset)) A1)
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
Proof. admit.
    (*intros.

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
    inversion H30. subst. clear H30. elim H7. reflexivity.*)
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
Proof. admit.
    (*intros.

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
    apply H12.*)
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
Proof. admit.
    (*intros.

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
    destruct n. reflexivity. simpl in H3. inversion H3.*)
Qed.

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
Proof. admit.
    (*intros.

    clear H. clear H5. clear H11. clear H12. clear H13.

    inversion H14. subst. clear H14.
    inversion H13. subst. clear H13.
    inversion H14. subst. clear H14.
    inversion H13. subst. clear H13.
    inversion H14. subst. clear H14.
    inversion H13. subst. clear H13.

    eapply expressionSubRL in H14. Focus 2. rewrite H7. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    inversion H14. subst. clear H14. Transparent basicEval. simpl in H19. Opaque basicEval.
    inversion H19. subst. clear H19. elim H5. reflexivity.

    subst. clear H13.
    eapply dumpVar in H14. Focus 2. instantiate (1 := 7). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H14.
    eapply dumpVar in H14. Focus 2. instantiate (1 := 7). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H14.
    eapply dumpVar in H14. Focus 2. instantiate (1 := 7). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H14.
    apply H14.

    subst. clear H14.
    simpl in H13.
    eapply dumpVar in H13. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H13.
    eapply expressionSubRSNeg in H16. Focus 2. apply H13. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    inversion H16. subst. clear H16.
    Transparent basicEval. simpl in H19. Opaque basicEval.
    inversion H19. subst. clear H19. elim H5. reflexivity.

    subst. clear H13.

    simpl in H14. eapply removeReplaceSame in H14. Focus 2. instantiate (1 := !!(varx)).
    instantiate (1 := v(4)). simpl. reflexivity. Focus 2. Transparent basicEval. simpl. reflexivity.
    Opaque basicEval. Focus 2. Transparent basicEval. simpl. reflexivity.
    Focus 2. rewrite H18. destruct (eee varx). omega. destruct n. omega. destruct n. omega.
    destruct n. omega. inversion H4. subst. elim H3. reflexivity.

    inversion H8. subst. clear H8.
    eapply expressionSubRSLR in H14. Focus 2. apply H13. Focus 2. simpl. reflexivity. Focus 2. simpl.
    reflexivity. Focus 2. simpl. reflexivity.
    inversion H14. subst. clear H14.
    Transparent basicEval. simpl in H19. Opaque basicEval.
    inversion H19. subst. clear H19. elim H5. reflexivity.
    subst. clear H8.
    eapply expressionSubRSLR in H14. Focus 2. apply H13. Focus 2. simpl. reflexivity. Focus 2. simpl.
    reflexivity. Focus 2. simpl. reflexivity.
    inversion H14. subst. clear H14.
    Transparent basicEval. simpl in H19. Opaque basicEval.
    inversion H19. subst. clear H19. elim H5. reflexivity.

    subst. clear H14.

    remember (validPredicate (@absEval unit eq_unit (@basicEval unit) eee
            (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: x3 :: nil)
            (v(8) ==== (!!(varx))))).
    destruct b.
    simpl in H13.
    eapply dumpVar in H13. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H13.
    eapply expressionSubLR in H13. Focus 2. rewrite Heqb. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    simpl in H13. eapply removeReplaceSame in H13. Focus 2. instantiate (1 := !!(varx)).
    instantiate (1 := v(4)). simpl. reflexivity. Focus 2. Transparent basicEval. simpl. reflexivity.
    Opaque basicEval. Focus 2. Transparent basicEval. simpl. reflexivity.
    Focus 2. rewrite H18. destruct (eee varx). omega. destruct n. omega. destruct n. omega.
    destruct n. omega. inversion H4. subst. elim H3. reflexivity.

    inversion H8. subst. clear H8.
    eapply expressionSubRSLR in H13. Focus 2. apply H14. Focus 2. simpl. reflexivity. Focus 2. simpl.
    reflexivity. Focus 2. simpl. reflexivity.
    inversion H13. subst. clear H13.
    Transparent basicEval. simpl in H19. Opaque basicEval.
    inversion H19. subst. clear H19. elim H5. reflexivity.
    subst. clear H8.
    eapply expressionSubRSLR in H13. Focus 2. apply H14. Focus 2. simpl. reflexivity. Focus 2. simpl.
    reflexivity. Focus 2. simpl. reflexivity.
    inversion H13. subst. clear H13.
    Transparent basicEval. simpl in H19. Opaque basicEval.
    inversion H19. subst. clear H19. elim H5. reflexivity.


    eapply dumpVar in H13. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H13.
    eapply removeReplace in H13. Focus 2. rewrite Heqb. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    eapply expressionSubRSLR in H15. Focus 2. apply H13. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    inversion H15. subst. clear H15. Transparent basicEval. simpl in H19. Opaque basicEval.
    inversion H19. elim H5. reflexivity.

    subst. clear H13.

    eapply dumpVar in H14. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H14.

    eapply expressionSubRSRL in H15. Focus 2. apply H14. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    inversion H15. subst. clear H15. Transparent basicEval. simpl in H19. Opaque basicEval.
    inversion H19; subst; clear H19. rewrite <- H2 in H. simpl in H. inversion H. subst.
    elim H5. reflexivity.

    subst. clear H14.

    inversion H13; subst; clear H13.
    inversion H14; subst; clear H14.

    inversion H13; subst; clear H13.

    eapply concreteComposeEmpty in H20. inversion H20; subst; clear H20.

    eapply dumpVar in H11. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H11.

    eapply expressionSubRSRL in H15. Focus 2. apply H11. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    inversion H15. subst. clear H15. Transparent basicEval. simpl in H20. Opaque basicEval.
    inversion H20; subst; clear H20. rewrite <- H2 in H. simpl in H. inversion H. subst.
    elim H5. reflexivity.

    inversion H13. subst. clear H13.
    Transparent basicEval. simpl in H12. Opaque basicEval. inversion H12. subst. clear H12.
    inversion H20; subst; clear H20.
    inversion H; subst; clear H.
    inversion H12; subst; clear H12.
    eapply concreteComposeEmpty in H22. inversion H22; subst; clear H22.

    eapply dumpVar in H14. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H11.

    eapply expressionSubRSRL in H15. Focus 2. apply H14. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.

    inversion H15. subst. clear H15. Transparent basicEval. simpl in H22. Opaque basicEval.
    inversion H22; subst; clear H22. rewrite <- H2 in H. simpl in H. inversion H. subst.
    elim H12. reflexivity.

    inversion H14; subst; clear H14. Transparent basicEval. simpl in H12. Opaque basicEval.
    inversion H20; subst; clear H20.
    inversion H; subst; clear H.
    inversion H11; subst; clear H11.
    Transparent basicEval. simpl in H19. Opaque basicEval.
    inversion H22; subst; clear H22. inversion H; subst; clear H. destruct x4; inversion H19; subst; clear H19.
    inversion H10; subst; clear H10.
    Transparent basicEval. simpl in H21. Opaque basicEval.
    inversion H13; subst; clear H13.
    eapply concreteComposeEmpty in H25. inversion H25; subst; clear H25.
    simpl in H20. simpl in H24. simpl in H19.

    eapply dumpVar in H20. Focus 2. instantiate (1 := 6). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H20.
    eapply dumpVar in H20. Focus 2. instantiate (1 := 6). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H20.
    eapply dumpVar in H20. Focus 2. instantiate (1 := 6). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H20.
    eapply dumpVar in H20. Focus 2. instantiate (1 := 6). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H20.
    eapply dumpVar in H20. Focus 2. instantiate (1 := 6). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H20.

    eapply reverse in H20.
    eapply expressionSubRSNeg in H20. Focus 2. eapply H24.
    rewrite H21 in H12. inversion H12; subst; clear H12.
    eapply  subRangeSet. apply H14. apply H11. apply H5. apply H21.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity.

    inversion H20. subst. clear H20. Transparent basicEval. simpl in H25. Opaque basicEval.
    inversion H25. subst. clear H25. elim H10. reflexivity.

 Qed.


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
    intros.

    eapply andSum8 in H6. Focus 2. apply H8. Focus 2. simpl. reflexivity. Focus 2.
    Transparent basicEval. simpl. Opaque basicEval. reflexivity.

    simplifyHyp H6.

    eapply unfoldSum in H6. Focus 2. simpl. reflexivity. Focus 2. instantiate (1 := (!!varx)). simpl. reflexivity.
    Focus 2. Transparent basicEval. simpl. Opaque basicEval.
    destruct (eee varx). reflexivity. destruct n. reflexivity. destruct n. reflexivity.
    destruct n. reflexivity. destruct n. reflexivity. inversion H5. subst. clear H5. elim H4. reflexivity.

    simpl in H6. inversion H6. subst. clear H6. inversion H15. subst. clear H15.
    inversion H6. subst. clear H6. inversion H15. subst. clear H15. inversion H6. subst. clear H6.
    inversion H17. subst. clear H17.
    eapply concreteComposeEmpty in H20. inversion H20. subst. clear H20.
    eapply concreteComposeEmpty in H22. inversion H22. subst. clear H22.
    simpl in H15. simpl in H16. simpl in H18.
    simplifyHyp H15. simplifyHyp H16.
    eapply foldSum in H16. Focus 2. apply H15. Focus 2. simpl. reflexivity.
    eapply expressionSubRL in H15. Focus 2. rewrite H9. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    simplifyHyp H15.
    eapply expressionSubRL in H16. Focus 2. rewrite H9. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    simplifyHyp H16.
    eapply expressionSubRL in H18. Focus 2. rewrite H9. reflexivity. Focus 2. simpl. reflexivity.
    Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity. Focus 2. simpl. reflexivity.
    simplifyHyp H18.
    eapply expressionSubRSRL in H16. Focus 2. apply H18. Focus 2. simpl. reflexivity. Focus 2.
    simpl. reflexivity. Focus 2. simpl. reflexivity.
    eapply resolveSum8x10 in H16. Focus 2. intros. eapply H1. instantiate (1 := NatValue 0::NatValue 1::NatValue 2::NatValue 3::nil) in H6. simpl in H6. apply H6.
    Focus 2. simpl. reflexivity.
    Focus 2. simpl. intros. instantiate (1 := ((#0 <<<< --( v(2), v(6) )---> (#10 ++++ v(10))) //\\
                                               (nth(v(4), v(10)) ==== #0))).
    simplifyHyp H14. simplifyHyp H14.
    inversion H14. subst. clear H14.
    inversion H22. subst. clear H22.
    eapply expressionSubGRSLR. apply H21. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity. eapply RSEmpty. unfold empty_heap. reflexivity.
    subst. clear H22.
    eapply expressionSubGRSOr1. apply H21. simpl. reflexivity. simpl. reflexivity.
    instantiate (3 := (--( v(2), v(6) )---> (#6 ++++ v(10)))).
    instantiate (1 := (nth(v(4), v(10)) ==== #0)). simpl. reflexivity.
    simpl. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity. eapply RSEmpty. unfold empty_heap. reflexivity.
    subst. clear H14.
    eapply expressionSubGRSOr2. apply H22. simpl. reflexivity. simpl. reflexivity.
    instantiate (3 := (--( v(2), v(6) )---> (#2 ++++ v(10)))).
    instantiate (1 := (nth(v(4), v(10)) ==== #0)). simpl. reflexivity.
    simpl. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity. eapply RSEmpty. unfold empty_heap. reflexivity.
    Focus 2. Transparent basicEval. simpl. reflexivity.

    eapply sumDiff in H0. Focus 2.
    eapply dumpVar in H16. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H16.
    eapply dumpVar in H16. Focus 2. instantiate (1 := 8). simpl. reflexivity. Focus 2. simpl. reflexivity.
    simpl in H16.
    apply H16. Focus 2. simpl. reflexivity.
    simplifyHyp H0.
 
    eapply sumExists in H0.
    inversion H0. subst. clear H0. Transparent basicEval. simpl in H19. Opaque basicEval.
    inversion H19. subst. clear H19.
    inversion H22. subst. clear H22. inversion H0. subst. clear H0.
    simplifyHyp H14. inversion H14. subst. clear H14.
    eapply concreteComposeEmpty in H23. inversion H23. subst. clear H23.

    assert(
       @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
         (AbsAll range(#0, #4)
            (((((([--( v(2), v(6) )---> (#10 ++++ (!!varx))] *\/*
                  [--( v(2), v(6) )---> (#2 ++++ (!!varx)) ==== #0] **
                  [--( v(2), v(6) )---> (#6 ++++ (!!varx)) ==== #0]) *\/*
                 [~~ --( v(2), v(6) )---> (#10 ++++ v(9))]) *\/*
                [nth(replacenth(v(4), !!(varx), !!(valuex)), (!!varx)) ==== #0]) *\/*
               [nth(replacenth(v(4), !!(varx), !!(valuex)), v(9)) ==== #0]) *\/*
              [(!!varx) ==== v(9)]) *\/*
             ([(!!(varx)) ==== v(9)] ** [(!!(varx)) ==== (!!(varx))] *\/*
              AbsExists TreeRecords(v(0))
                ([(!!(varx)) ==== v(9)] **
                 [nth(find(v(0), v(10)), #3) ==== (!!(varx))])) *\/*
             AbsExists TreeRecords(v(0))
               (AbsExists TreeRecords(find(v(0), v(10)))
                  ([nth(find(v(0), v(10)), #3) ==== v(9)] **
                   [nth(find(v(0), v(11)), #3) ==== (!!(varx))]))))
         (v :: v0 :: v1 :: v2 :: ListValue l :: v4 :: x :: x0 :: NatValue (eee varx) :: nil)
         (eee, empty_heap)
    ).
    eapply removeQuantVar. eapply H7.
    destruct (eee varx). left. reflexivity. destruct n. right. left. reflexivity. destruct n.
    right. right. left. reflexivity. destruct n. right. right. right. left. reflexivity.
    inversion H5. subst. clear H5. elim H4. reflexivity.
    instantiate (2 := 8). simpl. reflexivity. simpl. reflexivity.
    inversion H0. subst. clear H0.
    Transparent basicEval. simpl in H22. Opaque basicEval. inversion H22. subst. clear H22.
    assert (In x3 (NatValue 0::NatValue 1::NatValue 2::NatValue 3::nil)). apply H6.
    eapply H25 in H6. clear H25.

    eapply mergeTheorem1Aux9b.
    apply H. apply H1. apply H2. apply H3. apply H4. apply H5. apply H7. apply H8. apply H9. apply H10.
    apply H11. apply H12. apply H15. apply H18. apply H16. apply H6. apply H20. apply H19. apply H0.
    apply H13.*)
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
              ([~~ !!(varx) ==== nth(find(v(0), v(6)), #3)]) ** AbsEmpty) **
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
            ((!!(stack) :: !!(ssss) :: nth(v(0), #0) :: nil)
             :: (!!(have_var) :: #1 :: nil)
                :: (nth(v(4), !!(varx)) :: !!(backtrack) :: #0 :: nil) :: nil))
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
Proof. admit.
    (*intros.

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
            eapply arrayLength. apply H12. simpl. reflexivity.*)
Qed.

Theorem SatProgramWorks :
    exists x, {{invariant}}Program{{finalState x, Return x}}.
Proof.
    unfold invariant. unfold Program. simpl.

    eapply ex_intro.

    eapply strengthenPost.

    (* backtrack ::= ANum(0); *)
    pcrunch.

    (* WHILE ANum(1) DO *)
    eapply while with (invariant := invariant). unfold invariant. apply sbasic. intros. unfold invariant.

    eapply ex_intro. eapply strengthenPost.

    pcrunch. admit. apply sbasic.

    simp. simp. simp. simp. simp.
    eapply unfold_pre. unfoldHeap (@AbsVar unit eq_unit (@basicEval unit) stack).

    simp. simp. simp. simp.

    pcrunch. pcrunch. pcrunch. pcrunch.
    simp. simp. simp. simp. simp. simp. simp. simp. simp.

    eapply store_array.
    apply (AbsQVar 0).
    compute. reflexivity. compute. reflexivity. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity.
    solveSPickElement.

    intros. removeExistentials. simpl in H.
    eapply pickAssertion.
    apply H. solveSPickElement. reflexivity.  intro X. inversion X. compute. reflexivity.

    compute. reflexivity.

    simp. simp. simp. simp. simp.

    eapply while with (invariant := invariant1). unfold invariant1. apply sbasic. intros. unfold invariant1.
    eapply ex_intro. eapply strengthenPost.

    simp. simp. simp. simp. simp.

    pcrunch.

    eapply load_array.
    apply (AbsQVar 0).
    compute. reflexivity. compute. reflexivity. compute. reflexivity. compute. reflexivity.
    solveSPickElement.

    intros. removeExistentials. simpl in H.

    assert (@absEval unit eq_unit basicEval (fst ss) nil (~~ #3 <<<< !!(iiii))=NatValue 1).
    eapply pickAssertion.
    apply H. solveSPickElement. reflexivity.  intro X. inversion X. compute. reflexivity.

    clear H. Transparent basicEval. simpl in H0. simpl.

    remember (ble_nat (fst ss iiii) 3).
    destruct b.

    destruct (fst ss iiii). reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    destruct n. reflexivity.
    simpl in Heqb. inversion Heqb.
    simpl in H0. inversion H0.
  
    Opaque basicEval.

    compute. reflexivity.

    admit. apply sbasic.
    eapply mergeSimplifyLeft. compute. reflexivity.
    eapply mergeSimplifyLeft. compute. reflexivity.
    eapply mergeSimplifyLeft. compute. reflexivity.
    eapply mergeSimplifyLeft. compute. reflexivity.
    eapply mergeSimplifyLeft. compute. reflexivity.
    eapply mergeSimplifyLeft. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.

    startMerge.
    doMergeStates.

    eapply DMImplyPredicates1.
    instantiate (2 := ([~~ !!(have_var)] *\/* [nth(v(3), !!(varx)) ==== #0])). solveSPickElement.
    simpl. reflexivity.

    simpl. intros.

 assert (exists hh, @realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) (ARRAY(!!(assignments), #4, v(5))) bbb (eee,hh)).
    solvePickData H0.
    inversion H1. subst. clear H1.
 assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) ( [!!(varx) ==== !!(iiii)]) bbb (eee,empty_heap)).
    solvePickTerm H0.
 assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) ( [#0 ==== nth(v(5), !!(iiii))]) bbb (eee,empty_heap)).
    solvePickTerm H0.

    Transparent basicEval.

        inversion H1. subst. clear H1. simpl in H9. inversion H9. subst. clear H9.
            remember (beq_nat (eee varx) (eee iiii)). destruct b. apply beq_nat_eq in Heqb.

        inversion H3. subst. clear H3. simpl in H11.

        inversion H2. subst. clear H2. simpl in H10. inversion H10. subst. clear H10.

        rewrite <- H7 in H11.

        inversion H11. subst. clear H11. remember (nth (eee iiii) vl NoValue). destruct y.
            destruct n.

        eapply RSOrComposeR. eapply RSR. simpl. reflexivity. rewrite Heqb. rewrite Heqy.
        rewrite <- H7. rewrite <- Heqy. simpl. eapply BTStatePredicate. intro X. inversion X.

        unfold empty_heap. reflexivity.

        inversion H2. subst. clear H2. elim H3. reflexivity.
        inversion H2. inversion H2. inversion H2. inversion H1. subst. clear H1.
        elim H4. reflexivity.

    Opaque basicEval.

    eapply DMFinish. solveAllPredicates. solveAllPredicates.

    intros. simplifyHyp H. simplifyHyp H. simplifyHyp H. simplifyHyp H. simplifyHyp H. simplifyHyp H. simplifyHyp H.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.

    stateImplication.

    intros.

    eapply simplifyEquiv2. rewrite H0. compute. reflexivity.
    eapply RSEmpty. unfold empty_heap. reflexivity.

    intros. simplifyHyp H. simplifyHyp H. simplifyHyp H. unfold invariant1.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.
    eapply simplifyEquiv2. compute. reflexivity.

    stateImplication.

    intros. clear H.

    assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit))
            ([!!(have_var) ==== #0]) b (e,empty_heap)).
    solvePickTerm H1.

    eapply simplifyEquiv2. rewrite H0. compute. reflexivity.
    eapply simplifyEquiv2. rewrite H0. compute. reflexivity.

    Transparent basicEval.

        inversion H. subst. clear H. simpl in H7. inversion H7. subst. clear H7.
        remember (beq_nat (e have_var) 0). destruct b0. apply beq_nat_eq in Heqb0.

        eapply RSOrComposeL. eapply RSR. simpl. reflexivity.
        rewrite Heqb0. simpl. eapply BTStatePredicate.
        intro X. inversion X. unfold empty_heap. reflexivity.

        inversion H. subst. clear H. elim H2. reflexivity.

    Opaque basicEval.

    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyRight. compute. reflexivity.
    eapply mergeSimplifyLeft. compute. reflexivity.
    eapply mergeSimplifyLeft. compute. reflexivity.

    startMerge.
    doMergeStates.

    eapply DMImplyPredicates1.

    instantiate (2 := (AbsAll range(#0,#4) _)). solveSPickElement. simpl. reflexivity.

    simpl. intros.

    assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) (AbsAll range(#0, #4)
             ([nth(v(4), v(6)) ==== #0] *\/*
              [!!(varx) ==== v(6)] *\/*
              AbsExists TreeRecords(v(0))
                ([nth(find(v(0), v(7)), #3) ==== v(6)] **
                 [nth(find(v(0), v(7)), #4) ==== nth(v(4), v(6))]))) bbb (eee,empty_heap)).
      solvePickTerm H0.
    assert (@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) ([#0 ==== nth(v(4), !!(varx))]) bbb (eee,empty_heap)).
      solvePickTerm H0.

    Transparent basicEval.

        inversion H2. subst. clear H2. simpl in H8.
        remember (nth 4 bbb NoValue). destruct y.
            inversion H8.
            remember (nth (eee varx) l NoValue). destruct y.
            destruct n.
                eapply RSAll. simpl. reflexivity. reflexivity. intros.
                inversion H1. subst. clear H1. simpl in H6. inversion H6. subst. clear H6.
                eapply H10 in H2. inversion H2.
                    subst. clear H2.
                    eapply RSOrComposeL. apply H6.
                    subst. clear H2.
                        inversion H6. subst. clear H6.
                            inversion H5. subst. clear H5. simpl in H7. remember (nth 6 (bbb++x::nil) NoValue). destruct y.
                                inversion H7. subst. clear H7. remember (beq_nat (eee varx) n). destruct b.
                                inversion H1. subst. clear H1. apply beq_nat_eq in Heqb.
                                apply RSOrComposeL. eapply RSR. simpl. reflexivity.
                                rewrite <- Heqy1.
                                remember (nth 4 (bbb ++ x :: nil) NoValue). destruct y.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                simpl in Heqy. simpl in Heqy2.
                                rewrite <- Heqy in Heqy2. inversion Heqy2.
                                rewrite <- Heqb.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                simpl in Heqy. simpl in Heqy2. rewrite <- Heqy in Heqy2.
                                inversion Heqy2. rewrite <- Heqy0. simpl.
                                eapply BTStatePredicate. intro X. inversion X.
                                unfold empty_heap. reflexivity.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                simpl in Heqy. simpl in Heqy2.
                                rewrite <- Heqy in Heqy2. inversion Heqy2.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                destruct bbb. simpl in Heqy. inversion Heqy.
                                simpl in Heqy. simpl in Heqy2.
                                rewrite <- Heqy in Heqy2. inversion Heqy2.
                            inversion H1. subst. clear H1. elim H2. reflexivity.
                            inversion H7. inversion H7. inversion H7.
                        subst. eapply RSOrComposeR. apply H5.
                        inversion H8. elim H3. reflexivity.
                        inversion H8. inversion H8. inversion H8. inversion H8. inversion H8.

    Opaque basicEval.

    Focus 1.

    eapply DMImplyPredicates1. instantiate (2 := (AbsAll _ _)). solveSPickElement.
    simpl. reflexivity.

    intros.

    eapply mergeTheorem1. apply H. apply H0.

    apply DMFinish. solveAllPredicates. solveAllPredicates.
    assert(@realizeState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) (AbsAll TreeRecords(v(2))
             (AbsExists range(#0, #4)
                (([--( v(2), v(6) )---> (#1 ++++ v(7))] **
                  ([nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #2] *\/*
                   [nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #0]) *\/*
                  [--( v(2), v(6) )---> (#5 ++++ v(7))] **
                  ([nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #1] *\/*
                   [nth(replacenth(v(4), !!(varx), !!(valuex)), v(7)) ==== #0])) **
                 AbsAll range(#0, #4)
                   ([~~ --( v(2), v(6) )---> (#9 ++++ v(8)) ==== #0] **
                    ([~~ --( v(2), v(6) )---> (#17 ++++ v(8)) ==== #0] *\/*
                     [nth(v(5), v(8)) ==== v(6)]) *\/*
                    ([--( v(2), v(6) )---> (#9 ++++ v(8)) ==== #0] **
                     [--( v(2), v(6) )---> (#17 ++++ v(8)) ==== #0]) **
                    [~~ nth(v(5), v(8)) ==== v(6)]) **
                 (SUM(range(#0, #4),
                  ite(--( v(6), v(2) )---> (#9 ++++ v(8)),
                  --( v(6), v(2) )---> (#9 ++++ v(8)), 
                  #0), #2) *\/*
                  AbsAll range(#0, #4)
                    ([--( v(6), v(2) )---> (#9 ++++ v(8))])) **
                 (SUM(range(#0, #4),
                  (--( v(2), v(6) )---> (#1 ++++ v(8)) //\\
                   (ite(nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                        #1,
                    nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #1,
                    #0))) ++++
                  (--( v(2), v(6) )---> (#5 ++++ v(8)) //\\
                   (ite(nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                        #2,
                    nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ==== #2,
                    #0))), #4) **
                  AbsAll range(#0, #4)
                    ([#0 <<<< --( v(2), v(6) )---> (#9 ++++ v(8))] **
                     [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                      #0] *\/*
                     [--( v(2), v(6) )---> (#1 ++++ v(8)) ==== #0] **
                     [--( v(2), v(6) )---> (#5 ++++ v(8)) ==== #0]) **
                  AbsAll range(#0, #4)
                    (AbsAll range(#0, #4)
                       ((((([--( v(2), v(6) )---> (#9 ++++ v(8))] *\/*
                            [~~ --( v(2), v(6) )---> (#9 ++++ v(9))]) *\/*
                           [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                            #0]) *\/*
                          [nth(replacenth(v(4), !!(varx), !!(valuex)), v(9)) ====
                           #0]) *\/* [v(8) ==== v(9)]) *\/*
                        ([!!(varx) ==== v(8)] ** [!!(varx) ==== v(9)] *\/*
                         AbsExists TreeRecords(v(0))
                           ([!!(varx) ==== v(8)] **
                            [nth(find(v(0), v(10)), #2) ==== v(9)])) *\/*
                        AbsExists TreeRecords(v(0))
                          (AbsExists TreeRecords(find(v(0), v(10)))
                             ([nth(find(v(0), v(10)), #2) ==== v(8)] **
                              [nth(find(find(v(0), v(10)), v(11)), #2) ====
                               v(9)])))) *\/*
                  AbsExists range(#0, #4)
                    (([--( v(2), v(6) )---> (#1 ++++ v(8))] **
                      [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                       #2] *\/*
                      [--( v(2), v(6) )---> (#5 ++++ v(8))] **
                      [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                       #1]) **
                     AbsAll range(#0, #4)
                       ([--( v(2), v(6) )---> (#9 ++++ v(9)) ==== #0] *\/*
                        ([!!(varx) ==== v(9)] **
                         ([#0 <<<< --( v(2), v(6) )---> (#1 ++++ !!(varx))] **

                          [!!(valuex) ==== #2] *\/*
                          [#0 <<<< --( v(2), v(6) )---> (#5 ++++ !!(varx))] **
                          [!!(valuex) ==== #1]) *\/*
                         AbsExists TreeRecords(v(0))
                           ([!!(varx) ==== v(9)] **
                            ([#0 <<<<
                              --( v(2), v(6)
                              )---> (#1 ++++ nth(find(v(0), v(10)), #2))] **
                             [nth(find(v(0), v(10)), #3) ==== #2] *\/*
                             [#0 <<<<
                              --( v(2), v(6)
                              )---> (#5 ++++ nth(find(v(0), v(10)), #2))] **
                             [nth(find(v(0), v(10)), #3) ==== #1]))) *\/*
                        AbsExists TreeRecords(v(0))
                          (AbsExists TreeRecords(find(v(0), v(10)))
                             ([nth(find(v(0), v(10)), #2) ==== v(9)] **
                              ([#0 <<<<
                                --( v(2), v(6)
                                )---> (#1 ++++
                                       nth(find(find(v(0), v(10)), v(11)),
                                       #2))] **
                               [nth(find(find(v(0), v(10)), v(11)), #3) ====
                                #2] *\/*
                               [#0 <<<<
                                --( v(2), v(6)
                                )---> (#5 ++++
                                       nth(find(find(v(0), v(10)), v(11)),
                                       #2))] **
                               [nth(find(find(v(0), v(10)), v(11)), #3) ====
                                #1]))))) *\/*
                  AbsAll range(#0, #4)
                    ([--( v(2), v(6) )---> (#9 ++++ v(8)) ==== #0] *\/*
                     [nth(replacenth(v(4), !!(varx), !!(valuex)), v(8)) ====
                      #0]))))) bbb (eee,empty_heap)).
        solvePickTerm H0.

        inversion H1. subst. clear H1. simpl in H5.
        eapply RSAll. simpl. reflexivity. simpl. rewrite H5. reflexivity.

        intros. apply H8 in H1. clear H8. inversion H1. subst. clear H1. inversion H9. subst. clear H9.
        inversion H1. subst. clear H1. inversion H3. subst. clear H3.
        apply concreteComposeEmpty in H11. inversion H11. subst. clear H11.
        inversion H8. subst. clear H8. inversion H4. subst. clear H4.
        inversion H9. subst. clear H9.
        apply concreteComposeEmpty in H12. inversion H12. subst. clear H12.
        apply concreteComposeEmpty in H15. inversion H15. subst. clear H15. simpl in H10.
        eapply RSExists. simpl. reflexivity. Transparent basicEval. simpl. Opaque basicEval. reflexivity.
        eapply ex_intro. Transparent basicEval. simpl in H6. Opaque basicEval. inversion H6. subst. clear H6.
        split. apply H2.
        eapply RSCompose.
        inversion H8. subst. clear H8. Focus 2. subst. clear H8. Focus 1.

    (* End of derivation *)
