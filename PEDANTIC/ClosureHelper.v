(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * ClosureHelper.v
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

Theorem breakClosure : forall bindings s state param ss,
    ss = subStateList state param ->
    (realizeState (AbsClosure state param) bindings s <-> realizeState ss bindings s).
Proof.
    admit.
Admitted.

Fixpoint breakTopClosure (s : absState) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (breakTopClosure s1) (breakTopClosure s2))
    | AbsOrStar s1 s2 => (AbsOrStar (breakTopClosure s1) (breakTopClosure s2))
    | AbsExistsT s => AbsExistsT (breakTopClosure s)
    | AbsExists e s => AbsExists e (breakTopClosure s)
    | AbsAll e s => AbsAll e (breakTopClosure s)
    | AbsEach e s => AbsEach e (breakTopClosure s)
    | AbsEmpty => AbsEmpty
    | AbsAny => AbsAny
    | AbsNone => AbsNone
    | AbsLeaf i ll => AbsLeaf i ll
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id e1 e2 e3
    | AbsMagicWand s1 s2 => AbsMagicWand (breakTopClosure s1) (breakTopClosure s2)
    | AbsUpdateVar s vv vall => AbsUpdateVar (breakTopClosure s) vv vall
    | AbsUpdateWithLoc s vv vall => AbsUpdateWithLoc (breakTopClosure s) vv vall
    | AbsUpdateLoc s vv vall => AbsUpdateLoc (breakTopClosure s) vv vall
    | AbsUpdState s1 s2 s3 =>  (AbsUpdState (breakTopClosure s1) (breakTopClosure s2) (breakTopClosure s3))
    | AbsClosure s ll => subStateList s ll
   end.

Theorem breakTopClosureThm1 : forall bindings s state1 state2,
    state1 = breakTopClosure state2 ->
    (realizeState state1 bindings s -> realizeState state2 bindings s).
Proof.
    admit.
Admitted.

Theorem breakTopClosureThm2 : forall bindings s state1 state2,
    state1 = breakTopClosure state2 ->
    (realizeState state2 bindings s -> realizeState state1 bindings s).
Proof.
    admit.
Admitted.

Theorem breakLeftClosureThm : forall left1 left2 right m,
    left1 = breakTopClosure left2 ->
    mergeStates left1 right m -> mergeStates left2 right m.
Proof.
    admit.
Admitted.

Theorem breakRightClosureThm : forall left right1 right2 m,
    right1 = breakTopClosure right2 ->
    mergeStates left right1 m -> mergeStates left right2 m.
Proof.
    admit.
Admitted.






