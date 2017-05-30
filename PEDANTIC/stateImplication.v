(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * StateImplication.v
 * This file contains many defintions and tactics useful in proving that one state
 * implies another.  The key tactic is one that pairs off components of a state.
 *
 * Key definitions:
 *     stateImplication
 *     prove_implication
 *
 **********************************************************************************)

Require Import Omega.
Require Export SfLib.
Require Export ImpHeap.
Require Export AbsState.
Require Export PickElement.
Require Export AbsStateInstance.

(* Glue stuff *)
Fixpoint no_cell_terms (s : absState) : bool :=
    match s with
    | AbsStar a b => if no_cell_terms a then no_cell_terms b else false
    | AbsExists e s => no_cell_terms s
    | AbsExistsT s => no_cell_terms s
    | AbsAll e s => no_cell_terms s
    | AbsEach e s => no_cell_terms s
    | AbsLeaf (AbsCellId) l => false
    | _ => true
    end.

Fixpoint no_r_terms (s : absState) : bool :=
    match s with
    | AbsStar a b => if no_r_terms a then no_r_terms b else false
    | AbsExists e s => no_r_terms s
    | AbsExistsT s => no_r_terms s
    | AbsAll e s => no_r_terms s
    | AbsEach e s => no_r_terms s
    | AbsLeaf (Id x) l => if (beq_nat x 3) (*AbsCell*) then true else if (beq_nat x 1) (*AbsPredicate*) then true else false
    | _ => true
    end.

Fixpoint r_term_list (s : absState) : list absState :=
    match s return list (absState) with
    | AbsStar a b => (r_term_list a)++(r_term_list b)
    | AbsExists e s => r_term_list s
    | AbsExistsT s => r_term_list s
    | AbsAll e s => r_term_list s
    | AbsEach e s => r_term_list s
    | AbsLeaf (Id x) l => if beq_nat x 1 then nil else if beq_nat x 3 then nil else (AbsLeaf (Id x) l)::nil
    | _ => nil
    end.

Fixpoint predicate_list(s : absState) : list absState :=
    match s return list absState with
    | AbsStar a b => (predicate_list a)++(predicate_list b)
    | AbsExists e s => predicate_list s
    | AbsExistsT s => predicate_list s
    | AbsAll e s => predicate_list s
    | AbsEach e s => predicate_list s
    | AbsLeaf (AbsPredicateId) l => (AbsLeaf (AbsPredicateId) l)::nil
    | _ => nil
    end.

Fixpoint strip_front_exists (s : absState) : (absState * nat) :=
    match s with
    | AbsExistsT s => match strip_front_exists s with
                      (st,n) => (st,n+1)
                      end
    (*| AbsExists i l s => match strip_front_exists s with
                         (st,n) => (st,n+1)
                         end*)
    | _ => (s,0)
    end.

Fixpoint map_over (l : list (nat * nat)) (v : nat) :=
    match l with
    | nil => 0
    | ((x1,x2)::r) => if beq_nat x2 v then x1 else map_over r v
    end.

Fixpoint map_over_exp (l : list (nat * nat)) (limit1 : nat) (limit2 : nat) (e : absExp) : absExp :=
   match e return absExp with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar v => AbsQVar (if ble_nat limit2 v then (v+limit1)-limit2 else map_over l v)
   | AbsFun i ll => AbsFun i (map (map_over_exp l limit1 limit2) ll)
   end.

Fixpoint map_over_state (l : list (nat * nat)) (limit1 : nat) (limit2 : nat) (s : absState) : absState :=
   match s return absState with
    | AbsStar s1 s2 => (AbsStar (map_over_state l limit1 limit2 s1) (map_over_state l limit1 limit2 s2))
    | AbsOrStar s1 s2 => (AbsOrStar (map_over_state l limit1 limit2 s1) (map_over_state l limit1 limit2 s2))
    | AbsExists e s => AbsExists (map_over_exp l limit1 limit2 e) (map_over_state (push_pairs l) (S limit1) (S limit2) s)
    | AbsExistsT s => AbsExistsT (map_over_state (push_pairs l) (S limit1) (S limit2) s)
    | AbsAll e s => AbsAll (map_over_exp l limit1 limit2 e) (map_over_state (push_pairs l) (S limit1) (S limit2) s)
    | AbsEach e s => AbsEach (map_over_exp l limit1 limit2 e) (map_over_state (push_pairs l) (S limit1) (S limit2) s)
    | AbsEmpty => AbsEmpty
    | AbsNone => AbsNone
    | AbsAny => AbsAny
    | AbsLeaf i ll => AbsLeaf i (map (map_over_exp l limit1 limit2) ll)
    | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (map_over_exp l limit1 limit2 e1) (map_over_exp (push_pairs l) (S limit1) (S limit2) e2) (map_over_exp l limit1 limit2 e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (map_over_state l limit1 limit2 s1) (map_over_state l limit1 limit2 s2)
    | AbsUpdateVar s i e => AbsUpdateVar (map_over_state l limit1 limit2 s) i (map_over_exp l limit1 limit2 e)
    | AbsUpdateWithLoc s i e => AbsUpdateWithLoc (map_over_state l limit1 limit2 s) i (map_over_exp l limit1 limit2 e)
    | AbsUpdateLoc s i e => AbsUpdateLoc (map_over_state l limit1 limit2 s) (map_over_exp l limit1 limit2 i) (map_over_exp l limit1 limit2 e)
    | AbsUpdState s1 s2 s3 => AbsUpdState (map_over_state l limit1 limit2 s1) (map_over_state l limit1 limit2 s2) (map_over_state l limit1 limit2 s3)
    | AbsClosure s ll => AbsClosure s (map (map_over_exp l limit1 limit2) ll)
   end.

Fixpoint mem1 (x : nat) (m : list (nat * nat)) :=
    match m with
    | nil => false
    | ((a,b)::r) => if beq_nat a x then true else mem1 x r
    end.

Fixpoint mem2 (x : nat) (m : list (nat * nat)) :=
    match m with
    | nil => false
    | ((a,b)::r) => if beq_nat b x then true else mem2 x r
    end.

Fixpoint complete_mapping1 (x1 : nat) (l1 : nat) (l2 : nat) (s2 : absState) (m : list (nat * nat)) :=
    match x1 with
    | 0 => (m,l1,l2,s2)
    | S x1' => if mem1 x1' m then complete_mapping1 x1' l1 l2 s2 m
               else complete_mapping1 x1' l1 (l2+1) (addStateVar l2 s2) ((x1',l2)::m)
    end.

Fixpoint complete_mapping2 (x2 : nat) (l1 : nat) (l2 : nat) (s1 : absState) (m : list (nat * nat)) :=
    match x2 with
    | 0 => (m,l1,l2,s1)
    | S x2' => if mem2 x2' m then complete_mapping2 x2' l1 l2 s1 m
               else complete_mapping2 x2' (l1+1) l2 (addStateVar l1 s1) ((l1,x2')::m)
    end.

Fixpoint complete_mapping (l1 : nat) (l2 : nat) (m : list (nat * nat))
                          (s1 : absState) (s2 : absState) :=
    match complete_mapping1 l1 l1 l2 s2 m with
    | (m',l1',l2',s2') => match complete_mapping2 l2' l1' l2' s1 m' with
                          | (m'',l1'',l2'',s1'') => (m'',l1'',l2'',s1'',s2')
                          end
    end.

Fixpoint prove_state_implication (tl : nat) (s1: absState) (s2 : absState) (e : env) (h : heap) : Prop :=
    match tl return Prop with
    | 0 => realizeState s1 nil (e,h) -> realizeState s2 nil (e,empty_heap)
    | S n => exists x, prove_state_implication n (instantiateState s1 x) (instantiateState s2 x) e h
    end.

Fixpoint incrementLeft (pairs : list (nat * nat)) :=
    match pairs with
    | ((a,b)::c) => ((S a),b)::(incrementLeft c)
    | nil => nil
    end.

Fixpoint incrementRight (pairs : list (nat * nat)) :=
    match pairs with
    | ((a,b)::c) => (a,(S b))::(incrementLeft c)
    | nil => nil
    end.

(*
 * This top level definition is responsible for proving implications.  It works by first pairing off
 * identical components and then setting up a proof goal for the remainder.
 *)
Inductive prove_implication : list (nat * nat) -> absState -> nat -> absState -> nat -> list (nat * nat) -> absState -> Prop :=
    | CILPairR : forall s1 s2 s1' s2' l1 l2 vars vars' vars'' limit1 limit2 tl,
               Some (s1',s2',l1,l2,vars') = pick2RsNiF s1 s2 vars limit1 limit2 (@nil (list absExp)) (@nil (list absExp)) ->
               (*pick2RsNi s1 s2 vars limit1 limit2 (@nil (list absExp)) (@nil (list absExp )) l1 l2 s1' s2' vars' ->*)
               prove_implication vars' s1' limit1 s2' limit2 vars'' tl ->
               prove_implication vars s1 limit1 s2 limit2 vars'' tl
    | CILPairUpdateWithLoc : forall s1 s2 s1' s2' i1 i2 s1'' s2'' l1 l2 vars vars' vars'' limit1 limit2 tl tl' vars''',
               Some (s1',s2',(AbsUpdateWithLoc s1'' i1 l1),(AbsUpdateWithLoc s2'' i2 l2),vars') = pick2UpdateWithLocsNiF s1 s2 vars limit1 limit2 (@nil (list absExp)) (@nil (list absExp)) ->
               prove_implication vars' s1' limit1 s2' limit2 vars'' tl ->
               prove_implication vars'' s1'' limit1 s2'' limit2 vars''' tl' ->
               prove_implication vars s1 limit1 s2 limit2 vars''' (tl ** (AbsUpdateWithLoc tl' i1 l1))
    (*| CILPairCell : forall s1 s2 s1' s2' loc1 loc2 val1 val2 vars vars' vars'' limit1 limit2 tl,
               pick2Cells s1 s2 vars limit1 limit2 nil nil loc1 loc2 val1 val2 s1' s2' vars' ->
               prove_implication vars' s1' limit1 s2' limit2 vars'' tl ->
               prove_implication vars s1 limit1 s2 limit2 vars'' tl*)
    | CILFinish : forall vars limit1 limit2 s1 s2,
                  prove_implication vars s1 limit1 s2 limit2 vars s1.

Ltac prove_implication := (eapply CILPairR;[solve [compute;reflexivity] | prove_implication]) ||
                          (eapply CILPairUpdateWithLoc;[solve [compute;reflexivity] | prove_implication | prove_implication]) ||
                          (eapply CILFinish;simpl;reflexivity).

Function  stripUpdateWithLocs (s : absState) :=
    match s with
    | AbsUpdateWithLoc ss i v => match substVarState (addStateVar 0 (stripUpdateWithLocs ss)) i v(0) with
                                 | Some x => (AbsExistsT x)
                                 | _ => AbsUpdateWithLoc ss i v
                                 end
    | (a ** b) => ((stripUpdateWithLocs a) ** (stripUpdateWithLocs b))
    | AbsUpdateVar ss i v => AbsUpdateVar (stripUpdateWithLocs ss) i v
    | x => x
    end.

(*
 * The top level state implication theorem.  One state implies another if we
 * can first pair off many of the identical components and then prove that
 * the first state implies the remaining components.
 *)
Theorem stateImplication : forall s state1 (state2 : absState) state1' tl1 tl2 state2' state2'' vars mx l1x l2x state1x state2x state2x' bb,
    realizeState state1 bb s ->
    (state1',tl1) = remove_top_existentials state1 ->
    (state2',tl2) = remove_top_existentials state2 ->
    prove_implication nil state2' tl2 state1' tl1 vars state2'' ->
    (mx,l2x,l1x,state2x,state1x) = complete_mapping tl2 tl1 vars state2'' state1' ->
    state2x' = map_over_state mx l1x l2x state2x ->
    (forall e h b, length b=l1x-> (realizeState state1x (bb++b) (e,h)) -> (exists bbb, realizeState (stripUpdateWithLocs state2x') (bb++bbb) (e,empty_heap))) ->
    realizeState state2 bb s.
Proof. admit. Admitted.

Definition basicStateImplication := stateImplication.

(*
 * The tactics below are all useful in applying the stateImplication
 * theorem above and performing other useful tasks in proving an
 * implication
 *)
Ltac stateImplication :=
    eapply stateImplication;[
        crunch |
        (simpl; reflexivity) |
        (simpl; reflexivity) |
        prove_implication |
        (simpl; reflexivity) |
        (simpl; reflexivity) |
        idtac].
Ltac basicStateImplication :=
    eapply stateImplication;[
        crunch |
        (simpl; reflexivity) |
        (simpl; reflexivity) |
        prove_implication |
        (simpl; reflexivity) |
        (simpl; reflexivity) |
        idtac].

Ltac reduceHyp :=
    match goal with
    | [ H: 1 = 0 |- _ ] => inversion H
    | [ H: 0 = 1 |- _ ] => inversion H
    | [ H: true = false |- _ ] => inversion H
    | [ H: false = true |- _ ] => inversion H
    | [ H: None = Some _ |- _ ] => inversion H
    | [ H: Some _ = None |- _ ] => inversion H
    | [ H: 0 <> 0 |- _ ] => omega
    | [ H: 1 <> 1 |- _ ] => omega
    | [H: context [if beq_nat ?X ?Y then _ else _] |- _] => let x:= fresh in remember (beq_nat X Y) as x; destruct x; compute in H
    | [ H: true = beq_nat _ _ |- _ ] => apply beq_nat_eq in H;subst
    (*| [H: absEval (AbsVar _) _ _ |- _] => inversion H;subst;clear H
    | [H: absEval (AbsNatVal _) _ _ |- _] => inversion H;subst;clear H
    | [H: absEval (AbsHeapVal _) _ _ |- _] => inversion H;subst;clear H
    | [H: context [beq_nat 1 1] |- _ ] => compute in H
    | [H: context [beq_nat 1 0] |- _ ] => compute in H
    | [H: context [beq_nat 0 1] |- _ ] => compute in H
    | [H: context [beq_nat 0 0] |- _ ] => compute in H*)
    | [H: 1 = 1 |- _] => inversion H; subst; clear H
    | [H: 1 = 0 |- _] => inversion H; subst; clear H
    | [H: 0 = 1 |- _] => inversion H; subst; clear H
    | [H: 0 = 0 |- _] => inversion H; subst; clear H
    | [H: NatValue _ = NatValue _ |- _] => inversion H; subst; clear H
    (*| [H: HeapValue _ = HeapValue _ |- _] => inversion H; subst; clear H*)
    | [H: OtherValue _ = OtherValue _ |- _] => inversion H; subst; clear H
    | [H: NoValue = NoValue |- _] => inversion H; subst; clear H
    | [H: realizeState _ _ _ |- _] => inversion H; subst; clear H
    | [H: basicState _ _ _ |- _] => inversion H; subst; clear H
    (*| [H: absEval (AbsQVar _) _ _ |- _] => inversion H; subst; clear H
    | [H: absEval (AbsHeapRef _ _) _ _ |- _] => inversion H; subst; clear H
    | [H: absEval (AbsPlus _ _) _ _ |- _] => inversion H; subst; clear H
    | [H: absEval (AbsMinus _ _) _ _ |- _] => inversion H; subst; clear H
    | [H: absEval (AbsTimes _ _) _ _ |- _] => inversion H; subst; clear H
    | [H: absEval (AbsImply _ _) _ _ |- _] => inversion H; subst; clear H
    | [H: absEval (AbsNot _) _ _ |- _] => inversion H; subst; clear H
    | [H: absEval (AbsAnd _ _) _ _ |- _] => inversion H; subst; clear H
    | [H: absEval (AbsOr _ _) _ _ |- _] => inversion H; subst; clear H
    | [H: absEval (AbsIte _ _ _) _ _ |- _] => inversion H; subst; clear H
    | [H: absEval (AbsEqual _ _) _ (NatValue 0) |- _] => inversion H; subst; clear H
    | [H: absEval (AbsEqual _ _) _ (NatValue 1) |- _] => inversion H; subst; clear H
    | [H: absEval (AbsLess _ _) _ (NatValue 0) |- _] => inversion H; subst; clear H
    | [H: absEval (AbsLess _ _) _ (NatValue 1) |- _] => inversion H; subst; clear H
    | [H: absEval (AbsRMember _ _ _ _ _) _ (NatValue 0) |- _] => inversion H; subst; clear H
    | [H: absEval (AbsRInclude _ _ _ _ _) _ (NatValue 0) |- _] => inversion H; subst; clear H
    | [H: absEval (AbsRMember _ _ _ _ _) _ (NatValue 1) |- _] => inversion H; subst; clear H
    | [H: absEval (AbsRInclude _ _ _ _ _) _ (NatValue 1) |- _] => inversion H; subst; clear H
    | [H: absEval (AbsEqual _ _) _ (NatValue 1) |- _] => inversion H; subst; clear H*)
    | [H: context [instantiateState _ _] |- _ ] => compute in H
    | [H: exists _, _ |- _] => inversion H; subst; clear H
    | [H: context [(match env_p ?Y ?Z with | Some _ => _ | None => _ end)] |- _] => let xx:=fresh in remember (env_p Y Z) as xx; destruct xx; compute in H
    (*| [H: context [btnat _] |- _] => unfold btnat in H*)
    | [H: context [basicEval _ _] |- _] => unfold basicEval in H
    (*| [H: context [AbsEqualId] |- _] => unfold AbsEqualId in H*)
    (*| [H: context [absCanEvalList _ _] |- _] => compute in H*)
    | [H: Some _ = Some _ |- _] => inversion H; subst; clear H
    end.

Ltac propagate :=
           match goal with
           | [H: fst ?s _ = Some _, C:concreteCompose ?s _ _ |- _] => erewrite composeEnvPropagate1 in H;[idtac|apply C]
           | [H: fst ?s _ = Some _, C:concreteCompose _ ?s _ |- _] => erewrite composeEnvPropagate2 in H;[idtac|apply C]
           | [H: Some _ = fst ?s _, C:concreteCompose ?s _ _ |- _] => erewrite composeEnvPropagate1 in H;[idtac|apply C]
           | [H: Some _ = fst ?s _, C:concreteCompose _ ?s _ |- _] => erewrite composeEnvPropagate2 in H;[idtac|apply C]
           end.

Ltac reduceHypothesis := repeat reduceHyp.

Ltac simplHyp := repeat match goal with
                 | [H: _ = fst (_,_) _ |- _] => simpl in H
                 | [H: fst (_,_) _ = _ |- _] => simpl in H
                 | [H1: ?x ?y = Some _, H2: ?x ?y = Some _ |- _] => rewrite H1 in H2
                 | [H1: Some _ = ?x ?y, H2: Some _ = ?x ?y |- _] => rewrite <- H1 in H2
                 | [H: Some _ = Some _ |- _] => inversion H; subst; clear H
                 end.

Ltac tryEmptyCompose := apply emptyConcreteCompose || idtac.

Ltac simplifyEval :=
     match goal with
     | [H: Some _ = ?e ?v |- context [?e ?v]] => rewrite <- H;simpl;try simplifyEval
     | [H: ?e ?v = Some _ |- context [?e ?v]] => rewrite H;simpl;try simplifyEval
     | [ |- context [env_p _ _]] => unfold env_p;simpl;try simplifyEval
     | [ |- context [env_p _]] => unfold env_p;simpl;try simplifyEval
     (*| [ |- context [btnat _]] => unfold btnat*)
     | [ |- _ = _] => reflexivity
     (*| [ |- context [AbsEqualId] ] => unfold AbsEqualId; simpl; try simplifyEval
     | [ |- context [AbsEqualId] ] => unfold AbsOrId; simpl; try simplifyEval
     | [ |- context [AbsEqualId] ] => unfold AbsRMemberId; simpl; try simplifyEval*)
     | [ |- context [basicEval (Id _) _] ] => unfold basicEval; simpl; try simplifyEval
     end.

Ltac decomposeR :=
    match goal with
    | [ |- Tree 0 _ _ _ empty_heap ] => eapply TreeBase;[omega | unfold empty_heap; reflexivity ]
    end.

Ltac decomposeBasicState :=
    match goal with
    (*| [ |- context [Id 2] ] => try decomposeBasicState*)
    | [ |- basicState (AbsTreeId) (NatValue _::_::NatValue _::_) _] => eapply BStateTree; [try decomposeR | simplifyStripNatValues]
    | [ |- basicState (AbsPredicateId) _ _] => eapply BTStatePredicate;[ omega | intros; simpl; reflexivity ]
    | [ |- _ ] => simpl; simplifyEval; try decomposeBasicState
    end.

Ltac decomposeTheState :=
    match goal with
    | [ |- realizeState (AbsStar _ _) _ _] => eapply RSCompose;[try decomposeTheState | try decomposeTheState | tryEmptyCompose]
    | [ |- realizeState AbsEmpty _ _] => (eapply RSEmpty;simpl;unfold empty_heap;reflexivity)
    | [ |- realizeState (AbsLeaf _ _) _ _] => eapply RSR;[simpl;reflexivity | idtac]
    | [ |- realizeState (AbsAll _ _) _ _] => eapply RSAll;[simpl;reflexivity | simpl;reflexivity | simpl | idtac]
    (*| [ |- realizeStateList ((AbsExistsT _)::_) _] => eapply RSLExistsU;eapply ex_intro;simpl
    | [ |- realizeStateList ((AbsExists _ _ _)::_) _] => eapply RSLExists;eapply ex_intro;simpl
    | [ |- realizeStateList ((AbsEach _ _ _)::_) _] => eapply RSLEach;intros;simpl;decomposeTheState
    | [ |- realizeStateList ((AbsAccumulate _ _ _ _ _ _)::_) _ ] => eapply RSLAccumulate;[simpl;reflexivity|simpl;reflexivity|idtac|simpl;reflexivity]
    | [ |- absEval _ _ _] => decomposeEval
    | [ H:?X <>?X |- _] => let H1 := fresh in assert (X = X) as H1; reflexivity; apply H in H; inversion H*)
    end.
(*
 * The following definition is used to simplify the reduction of realizeState
 *)
Fixpoint destructState (a : absState) (bindings : list (@Value unit)) (s : state) : Prop :=
    match a with
    | AbsStar as1 as2 => exists h1 h2,
                         (destructState as1 bindings (fst s,h1) /\
                          destructState as2 bindings (fst s,h2) /\
                          (forall v, h1 v=None \/ h2 v=None) /\
                          compose_heaps h1 h2=(snd s))
    | AbsOrStar as1 as2 => (destructState as1 bindings s) \/ (destructState as2 bindings s)
    | AbsExists e a => forall  e rl,
                       absEval (env_p s) bindings e = (ListValue rl) ->
                       (exists x, In x rl /\
                           destructState a (bindings++(x::nil)) s)
    | AbsExistsT a => (exists x, destructState a (bindings++(x::nil)) s)
    | AbsAccumulate i e1 e2 e3 => forall v3 vl,
                    absEval (env_p s) bindings e1 = (ListValue vl) ->
                    absEval (env_p s) bindings e3 = v3 ->
                    basicAccumulate i (env_p s) bindings vl e2 v3
    | AbsAll e a => forall rl,
                    absEval (env_p s) bindings e = ListValue rl ->
                    (forall x, In x rl ->
                               destructState a (bindings++(x::nil)) s)
    | AbsEach e a => forall v rl states l,
                     absEval (env_p s) bindings e = v ->
                     v = ListValue rl ->
                     allFirsts rl l ->
                     allSeconds states l ->
                     (forall x y, In (x,y) l -> destructState a (bindings++(x::nil)) y) ->
                     fold_compose states s
    | AbsEmpty => (forall x, snd s x=None)
    | AbsAny => True
    | AbsNone => False
    | AbsLeaf i el => basicState i (map (absEval (env_p s) bindings) el) (snd s)
    | AbsMagicWand as1 as2 => exists h1 h2,
                            (destructState as1 bindings (fst s,h1) /\
                             destructState as2 bindings (fst s,h2) /\
                             (forall v, ~(h1 v=None) \/ h2 v=None) /\
                             compose_heaps h2 (snd s)=h1)
    | AbsUpdateVar ss i e => destructState ss bindings s
    | AbsUpdateWithLoc ss i e => destructState ss bindings s
    | AbsUpdateLoc ss i e => destructState ss bindings s
    | AbsUpdState s1 s2 s3 => destructState s1 bindings s
    | AbsClosure ss el => destructState ss (map (absEval (env_p s) bindings) el) (empty_env,heap_p s)
    end.

Theorem realizeDestructThm : forall s b st,
    @realizeState s b st -> destructState s b st.
Proof. admit. Admitted.

Ltac removeExistentials :=
    repeat (match goal with
     | [ H:realizeState (AbsExistsT _) _ _ |- _ ] => (inversion H; subst; clear H)
     | [ H: exists _, _ |- _ ] => (inversion H;subst;clear H)
     end).

Theorem pickAssertion : forall fs s e P P' bind bind2 x,
    realizeState P bind s ->
    spickElement P ([e]) P' ->
    fst s = fs ->
    x<>0 ->
    noQVarExp e=true ->
    absEval fs bind2 e = NatValue x.
Proof. admit. Admitted.

Theorem pickTerm : forall P bind s fs e P',
    realizeState P bind s ->
    spickElement P e P' ->
    allPredicates e ->
    fst s = fs ->
    realizeState e bind (fs,empty_heap).
Proof. admit. Admitted.

Ltac solvePickTerm X := eapply pickTerm;[apply X | solveSPickElement | solveAllPredicates | simpl; reflexivity].

Theorem pickData : forall P bind s fs e P',
    realizeState P bind s ->
    spickElement P e P' ->
    fst s = fs ->
    (exists h, realizeState e bind (fs,h)).
Proof. admit. Admitted.

Ltac solvePickData X := eapply pickData;[apply X | solveSPickElement | simpl; reflexivity].

Theorem concreteComposeEmpty : forall s1 s2 eee,
    concreteCompose s1 s2 (eee, empty_heap) <-> s1=(eee, empty_heap) /\ s2=(eee, empty_heap).
Proof. admit. Admitted.

Theorem nth_replace_same {t} : forall l m n (vv:t) x, m=n -> n < length l -> nth m (replacenth l n vv) x=vv.
        Proof.
            induction l.
            intros. inversion H0.
            destruct n. intros. rewrite H. simpl. reflexivity.
            intros. rewrite H. simpl. rewrite IHl. reflexivity. reflexivity. simpl in H0. inversion H0.
            omega. omega.
        Qed.

Theorem nth_replace_diff {t} : forall l m n (vv:t) x, m<>n -> nth m (replacenth l n vv) x=nth m l x.
        Proof.
            induction l.
            intros. simpl. reflexivity.
            intros. simpl. destruct n. destruct m. elim H. reflexivity. simpl. reflexivity.
            destruct m. simpl. reflexivity. simpl. rewrite IHl. reflexivity. omega.
        Qed.

Definition validPredicate {ev} (p : @Value ev) :=
    match p with
    | NatValue 0 => false
    | NatValue _ => true
    | _ => false
    end.

Fixpoint replaceExp (e : absExp ) (val: absExp) (rep:absExp) : absExp :=
   if beq_absExp e val then rep
   else
   match e with
   | AbsConstVal x => AbsConstVal x
   | AbsVar v => AbsVar v
   | AbsQVar v => AbsQVar v
   | AbsFun i l => AbsFun i (map (fun x => replaceExp x val rep) l)
   end.

Fixpoint replaceState (s : absState) (val: absExp) (rep: absExp) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (replaceState s1 val rep) (replaceState s2 val rep))
    | AbsOrStar s1 s2 => (AbsOrStar (replaceState s1 val rep) (replaceState s2 val rep))
    | AbsExistsT s => AbsExistsT (replaceState s val rep)
    | AbsExists e s => AbsExists (replaceExp e val rep) (replaceState s val rep)
    | AbsAll e s => AbsAll (replaceExp e val rep) (replaceState s val rep)
    | AbsEach e s => AbsEach (replaceExp e val rep) (replaceState s val rep)
    | AbsEmpty => AbsEmpty
    | AbsNone => AbsNone
    | AbsAny => AbsAny
    | AbsLeaf i l => AbsLeaf i (map (fun x => replaceExp x val rep) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (replaceExp e1 val rep) (replaceExp e2 val rep) (replaceExp e3 val rep)
    | AbsMagicWand s1 s2 => AbsMagicWand (replaceState s1 val rep) (replaceState s2 val rep)
    | AbsUpdateVar s i v => AbsUpdateVar (replaceState s val rep) i (replaceExp v val rep)
    | AbsUpdateWithLoc s i v => AbsUpdateWithLoc (replaceState s val rep) i (replaceExp v val rep)
    | AbsUpdateLoc s i v => AbsUpdateLoc (replaceState s val rep) (replaceExp i val rep) (replaceExp v val rep)
     | AbsUpdState s1 s2 s3 => AbsUpdState (replaceState s1 val rep) (replaceState s2 val rep) (replaceState s3 val rep)
    | AbsClosure s l => AbsClosure s (map (fun x => replaceExp x val rep) l)
   end.

Fixpoint pair_check {a} (f : a -> a -> bool) (l1 : list a) (l2 : list a) :=
    match l1,l2 with
    | nil,nil => true
    | (a::b),(c::d) => if f a c then pair_check f b d else false
    | _,_ => false
    end.

Fixpoint equivExp (e1 : absExp) (e2 : absExp) (val:absExp) (rep:absExp) : bool :=
   if beq_absExp e1 e2 then true
   else if beq_absExp e1 val && beq_absExp e2 rep then true
   else if beq_absExp e1 rep && beq_absExp e2 val then true
   else
   match e1,e2 with
   | AbsFun i1 l1,AbsFun i2 l2 => if beq_id i1 i2 then
                                      (fix go ll1 ll2 := match ll1,ll2 with
                                                        | nil, nil => true
                                                        | (ff1::rr1), (ff2::rr2) =>
                                                          if equivExp ff1 ff2 val rep then go rr1 rr2 else false
                                                        | _, _ => false
                                                        end) l1 l2
                                  else false
   | _,_ => false
   end.

Fixpoint equivState (s1 : absState) (s2 : absState) (val: absExp) (rep: absExp) : bool :=
   match s1,s2 with
    | AbsStar s1a s1b,AbsStar s2a s2b => (equivState s1a s2a val rep) && (equivState s1b s2b val rep)
    | AbsOrStar s1a s1b,AbsOrStar s2a s2b => (equivState s1a s2a val rep) && (equivState s1b s2b val rep)
    | AbsExistsT s1, AbsExistsT s2 => (equivState s1 s2 val rep)
    | AbsExists e1 s1, AbsExists e2 s2 => (equivExp e1 e2 val rep) && (equivState s1 s2 val rep)
    | AbsAll e1 s1, AbsAll e2 s2 => (equivExp e1 e2 val rep) && (equivState s1 s2 val rep)
    | AbsEach e1 s1, AbsEach e2 s2 => (equivExp e1 e2 val rep) && (equivState s1 s2 val rep)
    | AbsEmpty, AbsEmpty => true
    | AbsLeaf i1 l1, AbsLeaf i2 l2 =>
                                  if beq_id i1 i2 then
                                      (fix go ll1 ll2 := match ll1,ll2 with
                                                        | nil, nil => true
                                                        | (ff1::rr1), (ff2::rr2) =>
                                                          if equivExp ff1 ff2 val rep then go rr1 rr2 else false
                                                        | _, _ => false
                                                        end) l1 l2
                                  else false
    | AbsAccumulate i1 e1a e1b e1c, AbsAccumulate i2 e2a e2b e2c =>
             (equivExp e1a e2a val rep) && (equivExp e1b e2b val rep) && (equivExp e1c e2c val rep)
    | _, _ => false
   end.

Fixpoint maxBindingExp (e : absExp ) : nat :=
   match e with
   | AbsConstVal x => 0
   | AbsVar v => 0
   | AbsQVar v => S v
   | AbsFun i l => fold_left (fun x y => if ble_nat x y then y else x) (map maxBindingExp l) 0
   end.

Fixpoint clipBinding {ev} (b : list (@Value ev)) (n : nat) :=
    match b,n with
    | (f::r),(S n') => f::(clipBinding r n')
    | _,_ => nil
    end.

Theorem expressionSubLR : forall b b' b'' p st e h exp1 exp2 p',
    realizeState ([p]) b st ->
    validPredicate (absEval e b'' (exp1====exp2))=true ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    st = (e,h) ->
    p' = replaceExp p exp1 exp2 ->
    realizeState ([p']) b st.
Proof. admit. Admitted.

Theorem expressionNotEqualZero1 : forall b b' b'' p st e h exp p',
    realizeState (p) b st ->
    false=validPredicate (absEval e b'' (#0====exp)) ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    st = (e,h) ->
    p' = replaceState p ((#0) <<<< exp) (#1) ->
    realizeState (p') b st.
Proof. admit. Admitted.

Theorem expressionNotEqualZero2 : forall b b' b'' p st e h exp p',
    realizeState (p) b st ->
    false=validPredicate (absEval e b'' (#0====exp)) ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    st = (e,h) ->
    p' = replaceState p ((#0) ==== exp) (#0) ->
    realizeState (p') b st.
Proof. admit. Admitted.

Theorem expressionNotEqualZero3 : forall b b' b'' p st e h exp p',
    realizeState (p) b st ->
    false=validPredicate (absEval e b'' (#0====exp)) ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    st = (e,h) ->
    p' = replaceState p (exp ==== (#0)) (#0) ->
    realizeState (p') b st.
Proof. admit. Admitted.

Theorem expressionSubRL : forall b b' b'' p st e h exp1 exp2 p',
    realizeState (p) b st ->
    validPredicate (absEval e b'' (exp1====exp2))=true ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    st = (e,h) ->
    p' = replaceState p exp2 exp1 ->
    realizeState (p') b st.
Proof. admit. Admitted.

Theorem expressionSubRSLR : forall b b' b'' p st exp1 exp2 p',
    realizeState ([exp1====exp2]) b'' st ->
    realizeState (p) b st ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceState p exp1 exp2 ->
    realizeState (p') b st.
Proof. admit. Admitted.

Theorem expressionSubRSNeg : forall b b' b'' p st exp1 p',
    realizeState ([~~exp1]) b'' st ->
    realizeState (p) b st ->
    b' = clipBinding b (maxBindingExp (exp1)) ->
    b' = clipBinding b'' (maxBindingExp (exp1)) ->
    p' = replaceState p exp1 (#0) ->
    realizeState (p') b st.
Proof. admit. Admitted.

Theorem expressionSubRSRL : forall b b' b'' p st exp1 exp2 p',
    realizeState ([exp1====exp2]) b'' st ->
    realizeState (p) b st ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceState p exp2 exp1 ->
    realizeState (p') b st.
Proof. admit. Admitted.

Theorem expressionSubEval : forall b b' b'' p st exp val p' e,
    @NatValue unit val = absEval e b' exp ->
    realizeState (p) b'' st ->
    e = (fst st) ->
    p' = replaceState p  exp (#val) ->
    b = clipBinding b' (maxBindingExp exp) ->
    b = clipBinding b'' (maxBindingExp exp) ->
    realizeState (p') b'' st.
Proof. admit. Admitted.

Theorem expressionSubEvalEval : forall b p st exp1 exp2 p' e,
    absEval e b exp2 = absEval e b exp1 ->
    realizeState (p) b st ->
    e = (fst st) ->
    p' = replaceState p  exp1 exp2 ->
    realizeState (p') b st.
Proof. admit. Admitted.

Theorem expressionSubGRSLR : forall b b' b'' p st exp1 exp2 p',
    realizeState ([exp1====exp2]) b'' st ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceExp p exp1 exp2 ->
    realizeState ([p']) b st ->
    realizeState ([p]) b st.
Proof. admit. Admitted.

Theorem expressionSubGRSRL : forall b b' b'' p st exp1 exp2 p',
    realizeState ([exp1====exp2]) b'' st ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceExp p exp2 exp1 ->
    realizeState ([p']) b st ->
    realizeState ([p]) b st.
Proof. admit. Admitted.

Theorem expressionSubGLR : forall b b' e b'' p st exp1 exp2 p',
    validPredicate (absEval e b'' (exp1====exp2))=true ->
    e = (fst st) ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceExp p exp1 exp2 ->
    realizeState ([p']) b st ->
    realizeState ([p]) b st.
Proof. admit. Admitted.

Theorem expressionSubGRL : forall b b' b'' p st exp1 exp2 p' e,
    validPredicate (absEval e b'' (exp1====exp2))=true ->
    e = (fst st) ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceState p exp2 exp1 ->
    realizeState (p') b st ->
    realizeState (p) b st.
Proof. admit. Admitted.

Theorem expressionSubGRSNeg : forall b b' b'' p st exp p' e,
    realizeState ([exp]) b'' st ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    p' = replaceExp p (~~exp) (#0) ->
    e = (fst st) ->
    absEval e b p=
    absEval e b p'.
Proof. admit. Admitted.

Theorem expressionSubGRSOr1 : forall b b' b'' p st exp p' e x y,
    realizeState ([exp]) b'' st ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    p' = replaceState p ((exp\\//x)//\\y) (y) ->
    e = (fst st) ->
    realizeState (p') b st ->
    realizeState (p) b st.
Proof. admit. Admitted.

Theorem expressionSubGRSOr2 : forall b b' b'' p st exp p' e x y,
    realizeState ([exp]) b'' st ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    p' = replaceState p ((x\\//exp)//\\y) (y) ->
    e = (fst st) ->
    realizeState (p') b st ->
    realizeState (p) b st.
Proof. admit. Admitted.

Theorem expressionSubGRSNeg1 : forall b b' b'' p st exp p' e,
    realizeState ([exp]) b'' st ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    p' = replaceState p (~~exp) (#0) ->
    e = (fst st) ->
    realizeState (p') b st ->
    realizeState (p) b st.
Proof. admit. Admitted.

Theorem expressionSubRSVP : forall b b' b'' p st exp1 exp2 p' eee,
    realizeState ([exp1====exp2]) b st ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceExp p exp1 exp2 ->
    eee = fst st ->
    validPredicate (absEval eee b'' p)=validPredicate (absEval eee b'' p').
Proof. admit. Admitted.

Theorem removeQuantVar : forall n b e h var exp1 exp2,
    realizeState exp2 b (e,h) ->
    nth n b NoValue = NatValue (e var) ->
    equivState exp1 exp2 (!!var) (v(n)) = true ->
    realizeState exp1 b (e,h).
Proof. admit. Admitted.

Fixpoint removeReplaceExp (loc1 : absExp) (loc2 : absExp) (exp : absExp) :=
    match exp with
    | AbsFun (AbsNthId) (p::q::nil) =>
                match p,q with
                | (AbsFun (AbsReplaceNthId) (base::l1::val::nil)),l2 =>
                    if (beq_absExp loc1 l1 && beq_absExp loc2 l2) ||
                       (beq_absExp loc1 l2 && beq_absExp loc2 l1) then
                        AbsFun (AbsNthId) (base::l2::nil)
                    else
                        AbsFun (AbsNthId) (p::q::nil)
                | _,_ => AbsFun (AbsNthId) (p::q::nil)
                end
    | (AbsFun i l) => AbsFun i (map (removeReplaceExp loc1 loc2) l)
    | x => x
    end.

Fixpoint removeReplaceState (loc1 : absExp) (loc2 : absExp) (s:absState) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (removeReplaceState loc1 loc2 s1) (removeReplaceState loc1 loc2 s2))
    | AbsOrStar s1 s2 => (AbsOrStar (removeReplaceState loc1 loc2 s1) (removeReplaceState loc1 loc2 s2))
    | AbsExistsT s => AbsExistsT (removeReplaceState loc1 loc2 s)
    | AbsExists e s => AbsExists (removeReplaceExp loc1 loc2 e) (removeReplaceState loc1 loc2 s)
    | AbsAll e s => AbsAll (removeReplaceExp loc1 loc2 e) (removeReplaceState loc1 loc2 s)
    | AbsEach e s => AbsEach (removeReplaceExp loc1 loc2 e) (removeReplaceState loc1 loc2 s)
    | AbsEmpty => AbsEmpty
    | AbsNone => AbsNone
    | AbsAny => AbsAny
    | AbsLeaf i l => AbsLeaf i (map (removeReplaceExp loc1 loc2) l)
    | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (removeReplaceExp loc1 loc2 e1) (removeReplaceExp loc1 loc2 e2) (removeReplaceExp loc1 loc2 e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (removeReplaceState loc1 loc2 s1) (removeReplaceState loc1 loc2 s2)
    | AbsUpdateVar s i v => AbsUpdateVar (removeReplaceState loc1 loc2 s) i (removeReplaceExp loc1 loc2 v)
    | AbsUpdateWithLoc s i v => AbsUpdateWithLoc (removeReplaceState loc1 loc2 s) i (removeReplaceExp loc1 loc2 v)
    | AbsUpdateLoc s i v => AbsUpdateLoc (removeReplaceState loc1 loc2 s) (removeReplaceExp loc1 loc2 i) (removeReplaceExp loc1 loc2 v)
    | AbsUpdState s1 s2 s3 => AbsUpdState (removeReplaceState loc1 loc2 s1) (removeReplaceState loc1 loc2 s2) (removeReplaceState loc1 loc2 s3)
    | AbsClosure s l => AbsClosure s (map (removeReplaceExp loc1 loc2) l)
   end.

Theorem removeReplace : forall b b' b'' p st e h exp1 exp2 p',
    realizeState (p) b st ->
    validPredicate (absEval e b'' (exp1====exp2))=false ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    st = (e,h) ->
    p' = removeReplaceState exp1 exp2 p ->
    realizeState (p') b st.
Proof. admit. Admitted.

Fixpoint removeReplaceSameExp (l : absExp) (loc : absExp) (exp : absExp) :=
    match exp with
    | AbsFun (AbsNthId) (p::q::nil) =>
                match p,q with
                | (AbsFun (AbsReplaceNthId) (base::l1::val::nil)),l2 =>
                    if beq_absExp base l && beq_absExp l1 l2 &&
                       beq_absExp l1 loc then
                        val
                    else
                        AbsFun (AbsNthId) (p::q::nil)
                | _,_ => AbsFun (AbsNthId) (p::q::nil)
                end
    | (AbsFun i ll) => AbsFun i (map (removeReplaceSameExp l loc) ll)
    | x => x
    end.

Fixpoint removeReplaceSameState (loc1 : absExp) (loc2 : absExp) (s:absState) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (removeReplaceSameState loc1 loc2 s1) (removeReplaceSameState loc1 loc2 s2))
    | AbsOrStar s1 s2 => (AbsOrStar (removeReplaceSameState loc1 loc2 s1) (removeReplaceSameState loc1 loc2 s2))
    | AbsExistsT s => AbsExistsT (removeReplaceSameState loc1 loc2 s)
    | AbsExists e s => AbsExists (removeReplaceSameExp loc1 loc2 e) (removeReplaceSameState loc1 loc2 s)
    | AbsAll e s => AbsAll (removeReplaceSameExp loc1 loc2 e) (removeReplaceSameState loc1 loc2 s)
    | AbsEach e s => AbsEach (removeReplaceSameExp loc1 loc2 e) (removeReplaceSameState loc1 loc2 s)
    | AbsEmpty => AbsEmpty
    | AbsNone => AbsNone
    | AbsAny => AbsAny
    | AbsLeaf i l => AbsLeaf i (map (removeReplaceSameExp loc1 loc2) l)
    | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (removeReplaceSameExp loc1 loc2 e1) (removeReplaceSameExp loc1 loc2 e2) (removeReplaceSameExp loc1 loc2 e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (removeReplaceSameState loc1 loc2 s1) (removeReplaceSameState loc1 loc2 s2)
    | AbsUpdateVar s i v => AbsUpdateVar (removeReplaceSameState loc1 loc2 s) i (removeReplaceSameExp loc1 loc2 v)
    | AbsUpdateWithLoc s i v => AbsUpdateWithLoc (removeReplaceSameState loc1 loc2 s) i (removeReplaceSameExp loc1 loc2 v)
    | AbsUpdateLoc s i v => AbsUpdateLoc (removeReplaceSameState loc1 loc2 s) (removeReplaceSameExp loc1 loc2 i) (removeReplaceSameExp loc1 loc2 v)
    | AbsUpdState s1 s2 s3 => AbsUpdState (removeReplaceSameState loc1 loc2 s1) (removeReplaceSameState loc1 loc2 s2) (removeReplaceSameState loc1 loc2 s3)
    | AbsClosure s l => AbsClosure s (map (removeReplaceSameExp loc1 loc2) l)
   end.

Theorem removeReplaceSame : forall b p st l loc p' ll n,
    realizeState ([p]) b st ->
    p' = removeReplaceSameExp l loc p ->
    ListValue ll = absEval (fst st) b l ->
    NatValue n = absEval (fst st) b loc ->
    n < length ll ->
    realizeState ([p']) b st.
Proof. admit. Admitted.

Theorem realizeValidPredicate : forall st e h exp b,
    st = (e,h) ->
    (validPredicate (absEval e b exp)=true <-> realizeState ([exp]) b st).
Proof. admit. Admitted.

Theorem validPredicateSymmetry : forall b e exp1 exp2,
    validPredicate (absEval e b (exp1====exp2))=
    validPredicate (absEval e b (exp2====exp1)).
Proof. admit. Admitted.

Function mapSum (env : id -> nat) (b : list (@Value unit)) (values : list (@Value unit)) (e : absExp) : nat :=
  match values with
  | nil => 0
  | (ff::rr) => match (absEval env (b++(ff::nil)) e) with
                | NatValue x => (mapSum env b rr e)+x
                | _ => mapSum env b rr e
                end
  end.

Function singlePred (s : absState) :=
    match s with
    | [x] => Some x
    | (a ** b) => match singlePred a,singlePred b with
                | Some a,Some b => Some (a //\\ b)
                | _,_ => None
                end
    | (a *\/* b) => match singlePred a,singlePred b with
                  | Some a,Some b => Some (a \\// b)
                  | _,_ => None
                  end
    | _ => None
    end.

Theorem andSum8 : forall v0 v1 v2 v3 v4 v5 v6 v7 vv v r e s state ee,
    realizeState (SUM(r,e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::nil) s ->
    (forall x, In x vv ->
               realizeState state (v0::v1::v2::v3::v4::v5::v6::v7::x::nil) s) ->
    Some ee = singlePred state ->
    (@ListValue unit vv) = absEval (fst s) (v0::v1::v2::v3::v4::v5::v6::v7::nil) r ->
    realizeState (SUM(r,ee //\\ e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::nil) s.
Proof. admit. Admitted.

Theorem implySum8x10 : forall v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 vv v r e s state ee,
    realizeState (SUM(r,e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s ->
    (forall x, In x vv ->
               realizeState state (v0::v1::v2::v3::v4::v5::v6::v7::x::nil) s) ->
    Some ee = (singlePred state) ->
    (@ListValue unit vv) = absEval (fst s) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) r ->
    realizeState (SUM(r,(~~(addExpVar 8 (addExpVar 8 ee))) \\// e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s.
Proof. admit. Admitted.

Theorem andSum8x10 : forall v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 vv v r e s state ee,
    realizeState (SUM(r,e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s ->
    (forall x, In x vv ->
               realizeState state (v0::v1::v2::v3::v4::v5::v6::v7::x::nil) s) ->
    Some ee = (singlePred state) ->
    (@ListValue unit vv) = absEval (fst s) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) r ->
    realizeState (SUM(r,((addExpVar 8 (addExpVar 8 ee))) //\\ e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s.
Proof. admit. Admitted.

Theorem resolveSum8x10 : forall v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 vv v r e s state ee ff,
    realizeState (SUM(r,e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s ->
    (forall x, In x vv ->
               realizeState state (v0::v1::v2::v3::v4::v5::v6::v7::x::nil) s) ->
    Some ee = (singlePred state) ->
    (forall x s, In x vv ->
                 realizeState ([((addExpVar 8 (addExpVar 8 ee)))]) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::x::nil) (s,empty_heap) ->
                 realizeState ([e====ff]) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::x::nil) (s,empty_heap)) ->
    (@ListValue unit vv) = absEval (fst s) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) r ->
    realizeState (SUM(r,ff,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s.
Proof. admit. Admitted.

Theorem resolveSum9x10 : forall v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 vv v r e s state ee ff,
    realizeState (SUM(r,e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s ->
    (forall x, In x vv ->
               realizeState state (v0::v1::v2::v3::v4::v5::v6::v7::v8::x::nil) s) ->
    Some ee = (singlePred state) ->
    (forall x s, In x vv ->
                 realizeState ([(addExpVar 9 ee)]) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::x::nil) (s,empty_heap) ->
                 realizeState ([e====ff]) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::x::nil) (s,empty_heap)) ->
    (@ListValue unit vv) = absEval (fst s) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) r ->
    realizeState (SUM(r,ff,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s.
Proof. admit. Admitted.

Theorem sumDiff : forall s b r e s1 s2 sd x,
    realizeState (SUM(r,(e //\\ x),(#s1))) b s ->
    realizeState (SUM(r,e,(#s2))) b s ->
    sd = s2-s1 ->
    realizeState (SUM(r,(e //\\ (~~x)),(#sd))) b s.
Proof. admit. Admitted.

Theorem sumAllConv : forall r e b s,
    realizeState (SUM(r,e,#0)) b s ->
    realizeState (AbsAll r ([~~e])) b s.
Proof. admit. Admitted.

Function deletenth {t} (x : nat) (l : list t) :=
    match x,l with
    | 0, (f::r) => Some r
    | (S n),(f::r) => match deletenth n r with
                      | Some l => Some (f::l)
                      | _ => None
                      end
    | _,_ => None
    end.

Theorem dumpVar : forall state b s n b',
    realizeState state b s ->
    hasVnState state n=false ->
    Some b' = deletenth n b ->
    realizeState (removeStateVar n state) b' s.
Proof. admit. Admitted.

Theorem dumpVar2 : forall state b s n b',
    realizeState (removeStateVar n state) b' s ->
    hasVnState state n=false ->
    Some b' = deletenth n b ->
    realizeState state b s.
Proof. admit. Admitted.

Theorem mapSumExists : forall v e b vals exp,
    S v = mapSum e b vals exp ->
    exists x, In x vals /\ realizeState ([exp]) (b++(x::nil)) (e,empty_heap).
Proof. admit. Admitted.

Theorem mapSumNeg : forall e b vals exp,
    0 = mapSum e b vals exp ->
    forall x, In x vals -> realizeState ([~~exp]) (b++(x::nil)) (e,empty_heap).
Proof. admit. Admitted.

Theorem subRangeSet {ev} : forall x rl rl0 n v,
    rangeSet (ListValue (@findRecord ev n v)) = ListValue rl0 ->
    In x rl0 ->
    In (@NatValue ev n) rl ->
    rangeSet v = ListValue rl ->
    In x rl.
Proof. admit. Admitted.

Function replacenth {t} (x : nat) (e : t) (l : list t) :=
    match x,l with
    | 0, (f::r) => Some (e::r)
    | (S n),(f::r) => match replacenth n e r with
                      | Some l => Some (f::l)
                      | _ => None
                      end
    | _,_ => None
    end.

Theorem subBoundVar : forall b eee exp b' p p' n,
    nth n b' NoValue = absEval eee b exp ->
    realizeState p b' (eee, empty_heap) ->
    Some b = replacenth n (nth n b NoValue) b' ->
    p' = replaceState p v(n) exp ->
    realizeState p' b (eee,empty_heap).
Proof. admit. Admitted.

Theorem arrayLength : forall v len n b st l,
    realizeState (ARRAY(v,#len,v(n))) b st ->
    nth n b NoValue = ListValue l ->
    length l = len.
Proof. admit. Admitted.

Theorem sumExists : forall b eee r e n,
    realizeState (SUM(r,e,(#(S n)))) b (eee,empty_heap) ->
    realizeState (AbsExists r ([e])) b (eee,empty_heap).
Proof. admit. Admitted.

Theorem reverse: forall st x y b,
    realizeState ([x====y]) b st ->
    realizeState ([y====x]) b st.
Proof. admit. Admitted.

Theorem entailmentUnusedUpdated : forall s b state v e,
     realizeState (AbsUpdateVar state v e) b s ->
     hasVarState state v=false ->
     realizeState state b s.
Proof.
    admit.
Admitted.


Function allEmpty (s : absState) :=
    match s with
    | AbsEmpty => true
    | AbsStar a b => if allEmpty a then allEmpty b else false
    | AbsOrStar a b => if allEmpty a then allEmpty b else false
    | _ => false
    end.
    
Theorem emptyRealizeState : forall s b e,
    allEmpty(s)=true ->
    @realizeState s b (e,empty_heap).
Proof.
    admit.
Admitted.













































