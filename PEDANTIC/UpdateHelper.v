(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * UpdateHelper.v
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

Theorem realizeStateAbsUpdateWithLoc :  forall (as1 : absState) vv valaa bindings s,
                  realizeState (AbsUpdateWithLoc as1 vv valaa) bindings s ->
                  exists s1 s valc vald,
                  (realizeState as1 bindings s1 /\
                  (NatValue valc) = absEval (env_p s) bindings valaa /\
                  (heap_p s) = (heap_p s1) /\
                  (heap_p s) valc = Some vald /\
                  (override (env_p s) vv vald)= (env_p s1)).
Proof.
    admit.
Admitted.

Theorem realizeStateAbsUpdateVar :  forall (as1 : absState) vv valaa bindings s s1 valc,
                  realizeState (AbsUpdateVar as1 vv valaa) bindings s ->
                  (realizeState as1 bindings s1 /\
                   (NatValue valc) = absEval (env_p s) bindings valaa /\
                   (heap_p s) = (heap_p s1) /\
                   (override (env_p s) vv valc)= (env_p s1)).
Proof.
    admit.
Admitted.

Ltac decomposeUpdatesStep := match goal with
                   | [ H: exists _, _ |- _] => destruct H
                   | [ H: _ /\ _ |- _] => destruct H
                   | [ H: realizeState _ _ _ |- _ ] => eapply realizeStateAbsUpdateWithLoc in H
                   | [ H: realizeState _ _ _ |- _ ] => eapply realizeStateAbsUpdateVar in H
                   end.

Ltac decomposeUpdates := repeat decomposeUpdatesStep.





