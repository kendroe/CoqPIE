(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * ProgramTactics.v
 * This file contains 'pcrunch'.  This tactic is an expansion of crunch that
 * handles a few definitions not present in SfLib and SfLibExtras.
 *
 **********************************************************************************)

Require Export SfLib.
Require Export SfLibExtras.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export AbsState.
Require Export AbsStateInstance.
Require Export AbsExecute.
Require Export Simplify.
Require Export Eqdep.
Require Export StateImplication.
Require Export Classical.
Require Export Unfold.
Require Export merge.

Ltac destructStateStep := match goal with
                          | [H: realizeState (_ ** _) _ (_,empty_heap) |- _] => inversion H;subst;clear H
                          | [H: realizeState (AbsAll _ _) _ (_,empty_heap) |- _] => inversion H;subst;clear H
                          | [H: absEval _ _ _ = _ |- _] => simpl in H
                          | [H: realizeState (AbsExists _ _) _ (_,empty_heap) |- _] => inversion H;subst;clear H
                          | [H: realizeState (AbsExistsT _) _ (_,empty_heap) |- _] => inversion H;subst;clear H
                          | [H: realizeState ([_]) _ (_,empty_heap) |- _] => inversion H;subst;clear H
                          | [H: exists _, _ |- _] => inversion H;subst;clear H
                          | [H: context [map _ (_::_)] |- _] => simpl in H
                          | [H: _ /\ _ |- _] => inversion H;subst;clear H
                          | [H: concreteCompose _ _ (_, empty_heap) |- _] => apply concreteComposeEmpty in H; inversion H; subst; clear H
                          end.

Ltac destructState := repeat destructStateStep.

Ltac destructStateStep1 := match goal with
                          | [H: realizeState (_ ** _) _ (_,empty_heap) |- _] => inversion H;subst;clear H
                          | [H: realizeState (AbsAll _ _) _ (_,empty_heap) |- _] => inversion H;subst;clear H
                          | [H: realizeState (AbsExists _ _) _ (_,empty_heap) |- _] => inversion H;subst;clear H
                          | [H: realizeState (AbsExistsT _) _ (_,empty_heap) |- _] => inversion H;subst;clear H
                          | [H: exists _, _ |- _] => inversion H;subst;clear H
                          | [H: context [map _ (_::_)] |- _] => simpl in H
                          | [H: _ /\ _ |- _] => inversion H;subst;clear H
                          | [H: concreteCompose _ _ (_, empty_heap) |- _] => apply concreteComposeEmpty in H; inversion H; subst; clear H
                          end.

Ltac destructState1 := repeat destructStateStep1.

Ltac hypSimpStep := match goal with
                   | [H: context [match nth ?A ?B NoValue with | NatValue _ => _ | ListValue _ => _ | NoValue => _ | OtherValue _  => _ end] |- _] => let x := fresh in remember (nth A B NoValue) as x;destruct x
                   | [H: context [match findRecord ?A ?B with | NatValue _ => _ | ListValue _ => _ | NoValue => _ | OtherValue _  => _ end] |- _] => let x := fresh in remember (findRecord A B) as x;destruct x
                   | [H: context [if beq_nat ?A ?B then _ else _ ] |- _ ] => let x := fresh in remember (beq_nat A B) as x; destruct x
                   | [H: true = beq_nat _ _ |- _] => apply beq_nat_eq in H;subst
                   | [H: context [map _ (_::_)] |- _] => simpl in H
                   | [H: basicState (Id 1) (NoValue::_) _ |- _ ] => inversion H
                   | [H: basicState (Id 1) (ListValue _::_) _ |- _ ] => inversion H
                   | [H: basicState (Id 1) (OtherValue _::_) _ |- _ ] => inversion H
                   | [H: basicState (Id 1) (NatValue 0::_) _ |- _ ] => inversion H;crunch
                   | [ H: NatValue _ = NoValue |- _ ] => inversion H
                   | [ H: ListValue _ = NoValue |- _ ] => inversion H
                   | [ H: OtherValue _ = NoValue |- _ ] => inversion H
                   | [ H: NoValue = NatValue _ |- _ ] => inversion H
                   | [ H: ListValue _ = NatValue _ |- _ ] => inversion H
                   | [ H: OtherValue _ = NatValue _ |- _ ] => inversion H
                   | [ H: NoValue = ListValue _ |- _ ] => inversion H
                   | [ H: NatValue _ = ListValue _ |- _ ] => inversion H
                   | [ H: OtherValue _ = ListValue _ |- _ ] => inversion H
                   | [ H: NoValue = OtherValue _ |- _ ] => inversion H
                   | [ H: NatValue _ = OtherValue _ |- _ ] => inversion H
                   | [ H: ListValue _ = OtherValue _ |- _ ] => inversion H
                   | [ |- NatValue _ <> NoValue ] => let x :=fresh in (intro x;inversion x)
                   | [ |- ListValue _ <> NoValue ] => let x :=fresh in (intro x;inversion x)
                   | [ |- OtherValue _ <> NoValue ] => let x :=fresh in (intro x;inversion x)
                   | [ |- NoValue <> NatValue _ ] => let x :=fresh in (intro x;inversion x)
                   | [ |- ListValue <> NatValue _ ] => let x :=fresh in (intro x;inversion x)
                   | [ |- OtherValue _ <> NatValue ] => let x :=fresh in (intro x;inversion x)
                   | [ |- NoValue <> ListValue _ ] => let x :=fresh in (intro x;inversion x)
                   | [ |- NatValue <> ListValue _ ] => let x :=fresh in (intro x;inversion x)
                   | [ |- OtherValue _ <> ListValue ] => let x :=fresh in (intro x;inversion x)
                   | [ |- NoValue <> OtherValue _ ] => let x :=fresh in (intro x;inversion x)
                   | [ |- NatValue <> OtherValue _ ] => let x :=fresh in (intro x;inversion x)
                   | [ |- ListValue _ <> OtherValue ] => let x :=fresh in (intro x;inversion x)
                   | [ H: NatValue _ = NatValue _ |- _ ] => (inversion H;subst;clear H)
                   | [ H: ListValue _ = ListValue _ |- _ ] => (inversion H;subst;clear H)
                   | [ H: OtherValue _ = OtherValue _ |- _ ] => (inversion H;subst;clear H)
                   | [ H: context [nth _ nil _] |- _ ] => simpl in H
                   | [ H: 1=0 |- _ ] => inversion H
                   | [ H: 0=1 |- _ ] => inversion H
                   | [ H: false = beq_nat 0 0 |- _ ] => apply beq_nat_neq in H; elim H; reflexivity
                   | [ H: In (NatValue _) (_::_) |- _ ] => simpl in H
                   | [ H: In (ListValue _) (_::_) |- _ ] => simpl in H
                   | [ H: In (NoValue) (_::_) |- _ ] => simpl in H
                   | [ H: In (OtherValue _) (_::_) |- _ ] => simpl in H
                   | [ H: ListValue _ = _ \/ _ |- _ ] => inversion H;subst;clear H
                   | [ H: OtherValue _ = _ \/ _ |- _ ] => inversion H;subst;clear H
                   | [ H: NoValue = _ \/ _ |- _ ] => inversion H;subst;clear H
                   | [ H: _ = ListValue _ \/ _ |- _ ] => inversion H;subst;clear H
                   | [ H: _ = OtherValue _ \/ _ |- _ ] => inversion H;subst;clear H
                   | [ H: _ = NoValue \/ _ |- _ ] => inversion H;subst;clear H
                   | [ H: False |- _ ] => inversion H
                   | [ H: context [rangeSet (NoValue)] |- _] => simpl in H
                   end.

Ltac destructB := match goal with
                  | [H: length ?B = _ |- _] => destruct B;simpl in H;inversion H;subst;clear H
                  end.

Ltac destruct_bindings := repeat destructB.

Ltac hypSimp := repeat hypSimpStep.

Ltac pcrunchStep := match goal with
                   | [ H: ceval _ _ (_ ::= _) _ _ |- _] => (inversion H; subst; clear H)
                   | [ H: ceval _ _ (CNew _ _) _ _ |- _] => (inversion H; subst; clear H)
                   | [ H: ceval _ _ (CDelete _ _) _ _ |- _] => (inversion H; subst; clear H)
                   | [ H: ceval _ _ (CLoad _ _) _ _ |- _] => (inversion H; subst; clear H)
                   | [ H: ceval _ _ (CStore _ _) _ _ |- _] => (inversion H; subst; clear H)
                   | [ H: ceval _ _ (CSkip) _ _ |- _] => (inversion H; subst; clear H)
                   | [ |- _ ] => progress crunchStep
                   | [ |- _ ] => progress auto
                   | [ |- mergeReturnStates AbsNone _ _ _ _ _ ] => eapply mergeReturnStatesTrivial1
                   | [ |- mergeReturnStates _ AbsNone _ _ _ _ ] => eapply mergeReturnStatesTrivial2
                   | [ |- mergeStates AbsNone _ _ ] => eapply mergeStatesTrivial1
                   | [ |- mergeStates _ AbsNone _ ] => eapply mergeStatesTrivial2
                   | [ H: NatValue _ = NoValue |- _ ] => inversion H
                   | [ H: ListValue _ = NoValue |- _ ] => inversion H
                   | [ H: OtherValue _ = NoValue |- _ ] => inversion H
                   | [ H: NoValue = NatValue _ |- _ ] => inversion H
                   | [ H: ListValue = NatValue _ |- _ ] => inversion H
                   | [ H: OtherValue = NatValue _ |- _ ] => inversion H
                   | [ H: NoValue = ListValue _ |- _ ] => inversion H
                   | [ H: NatValue = ListValue _ |- _ ] => inversion H
                   | [ H: OtherValue = ListValue _ |- _ ] => inversion H
                   | [ H: NoValue = OtherValue _ |- _ ] => inversion H
                   | [ H: NatValue = OtherValue _ |- _ ] => inversion H
                   | [ H: ListValue = OtherValue _ |- _ ] => inversion H

                   | [ |- NatValue _ <> NoValue ] => let x :=fresh in (intro x;inversion x)
                   | [ |- ListValue _ <> NoValue ] => let x :=fresh in (intro x;inversion x)
                   | [ |- OtherValue _ <> NoValue ] => let x :=fresh in (intro x;inversion x)
                   | [ |- NoValue <> NatValue _ ] => let x :=fresh in (intro x;inversion x)
                   | [ |- ListValue <> NatValue _ ] => let x :=fresh in (intro x;inversion x)
                   | [ |- OtherValue _ <> NatValue ] => let x :=fresh in (intro x;inversion x)
                   | [ |- NoValue <> ListValue _ ] => let x :=fresh in (intro x;inversion x)
                   | [ |- NatValue <> ListValue _ ] => let x :=fresh in (intro x;inversion x)
                   | [ |- OtherValue _ <> ListValue ] => let x :=fresh in (intro x;inversion x)
                   | [ |- NoValue <> OtherValue _ ] => let x :=fresh in (intro x;inversion x)
                   | [ |- NatValue <> OtherValue _ ] => let x :=fresh in (intro x;inversion x)
                   | [ |- ListValue _ <> OtherValue ] => let x :=fresh in (intro x;inversion x)

                   | [ H: NatValue _ = NatValue _ |- _ ] => (inversion H;subst;clear H)
                   | [ H: ListValue _ = ListValue _ |- _ ] => (inversion H;subst;clear H)
                   | [ H: OtherValue _ = OtherValue _ |- _ ] => (inversion H;subst;clear H)

                   | [ |- validExpression _ _ ] => unfold validExpression
                   | [ |- {{_}}_;_{{ _ return _ with _ }} ] => eapply compose
                   | [ |- {{_}}_ ::= _{{ _ return _ with _ }} ] => eapply assign
                   | [ |- {{_}} (CIf _ _ _) {{ _ return _ with _ }} ] => eapply if_statement
                   | [ |- {{_}} (CLoad _ _) {{ _ return _ with _ }} ] => eapply load;solve [(simpl;reflexivity)]
                   | [ |- {{_}} (DELETE _,_) {{ _ return _ with _ }} ] => eapply @del_thm
                   | [ |- {{_}} (CStore _ _) {{ _ return _ with _ }} ] => eapply @store
                   | [ |- {{_}} (NEW _,_) {{ _ return _ with _ }} ] => eapply @new_thm
                   | [ |- {{_}} (SKIP) {{ _ return _ with _ }} ] => eapply skip_thm
                   | [ |- {{_}} (RETURN _) {{ _ return _ with _ }} ] => eapply return_thm
                   end.

Ltac pcrunch := repeat pcrunchStep.










































