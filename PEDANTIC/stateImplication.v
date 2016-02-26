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

Require Export SfLib.
Require Export ImpHeap.
Require Export AbsState.
Require Export PickElement.
Require Export AbsStateInstance.
Opaque unitEval.

(* Glue stuff *)
Fixpoint no_cell_terms {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) : bool :=
    match s with
    | AbsStar a b => if no_cell_terms a then no_cell_terms b else false
    | AbsExists e s => no_cell_terms s
    | AbsExistsT s => no_cell_terms s
    | AbsAll e s => no_cell_terms s
    | AbsEach e s => no_cell_terms s
    | AbsLeaf (AbsCellId) l => false
    | _ => true
    end.

Fixpoint no_r_terms {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) : bool :=
    match s with
    | AbsStar a b => if no_r_terms a then no_r_terms b else false
    | AbsExists e s => no_r_terms s
    | AbsExistsT s => no_r_terms s
    | AbsAll e s => no_r_terms s
    | AbsEach e s => no_r_terms s
    | AbsLeaf (Id x) l => if (beq_nat x 3) (*AbsCell*) then true else if (beq_nat x 1) (*AbsPredicate*) then true else false
    | _ => true
    end.

Fixpoint r_term_list {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) : list absState :=
    match s return list (@absState ev eq f t ac) with
    | AbsStar a b => (r_term_list a)++(r_term_list b)
    | AbsExists e s => r_term_list s
    | AbsExistsT s => r_term_list s
    | AbsAll e s => r_term_list s
    | AbsEach e s => r_term_list s
    | AbsLeaf (Id x) l => if beq_nat x 1 then nil else if beq_nat x 3 then nil else (AbsLeaf (Id x) l)::nil
    | _ => nil
    end.

Fixpoint predicate_list {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) : list absState :=
    match s return list (@absState ev eq f t ac) with
    | AbsStar a b => (predicate_list a)++(predicate_list b)
    | AbsExists e s => predicate_list s
    | AbsExistsT s => predicate_list s
    | AbsAll e s => predicate_list s
    | AbsEach e s => predicate_list s
    | AbsLeaf (AbsPredicateId) l => (AbsLeaf (AbsPredicateId) l)::nil
    | _ => nil
    end.

Fixpoint strip_front_exists {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) : (absState * nat) :=
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

Fixpoint map_over_exp {ev} {eq} {f} (l : list (nat * nat)) (limit1 : nat) (limit2 : nat) (e : @absExp ev eq f) : absExp :=
   match e return @absExp ev eq f with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar v => AbsQVar (if ble_nat limit2 v then (v+limit1)-limit2 else map_over l v)
   | AbsFun i ll => AbsFun i (map (map_over_exp l limit1 limit2) ll)
   end.

Fixpoint map_over_state {ev} {eq} {f} {t} {ac} (l : list (nat * nat)) (limit1 : nat) (limit2 : nat) (s : @absState ev eq f t ac) : absState :=
   match s return @absState ev eq f t ac with
    | AbsStar s1 s2 => (AbsStar (map_over_state l limit1 limit2 s1) (map_over_state l limit1 limit2 s2))
    | AbsOrStar s1 s2 => (AbsOrStar (map_over_state l limit1 limit2 s1) (map_over_state l limit1 limit2 s2))
    | AbsExists e s => AbsExists (map_over_exp l limit1 limit2 e) (map_over_state l limit1 limit2 s)
    | AbsExistsT s => AbsExistsT (map_over_state l limit1 limit2 s)
    | AbsAll e s => AbsAll (map_over_exp l limit1 limit2 e) (map_over_state l limit1 limit2 s)
    | AbsEach e s => AbsEach (map_over_exp l limit1 limit2 e) (map_over_state l limit1 limit2 s)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i ll => AbsLeaf i (map (map_over_exp l limit1 limit2) ll)
    | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (map_over_exp l limit1 limit2 e1) (map_over_exp l limit1 limit2 e2) (map_over_exp l limit1 limit2 e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (map_over_state l limit1 limit2 s1) (map_over_state l limit1 limit2 s2)
    | AbsUpdateVar s i e => AbsUpdateVar (map_over_state l limit1 limit2 s) i (map_over_exp l limit1 limit2 e)
    | AbsUpdState s1 s2 s3 => AbsUpdState (map_over_state l limit1 limit2 s1) (map_over_state l limit1 limit2 s2) (map_over_state l limit1 limit2 s3)
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

Fixpoint complete_mapping1 {ev} {eq} {f} {t} {ac} (x1 : nat) (l1 : nat) (l2 : nat) (s2 : @absState ev eq f t ac) (m : list (nat * nat)) :=
    match x1 with
    | 0 => (m,l1,l2,s2)
    | S x1' => if mem1 x1' m then complete_mapping1 x1' l1 l2 s2 m
               else complete_mapping1 x1' l1 (l2+1) (addStateVar l2 s2) ((x1',l2)::m)
    end.

Fixpoint complete_mapping2 {ev} {eq} {f} {t} {ac} (x2 : nat) (l1 : nat) (l2 : nat) (s1 : @absState ev eq f t ac) (m : list (nat * nat)) :=
    match x2 with
    | 0 => (m,l1,l2,s1)
    | S x2' => if mem2 x2' m then complete_mapping2 x2' l1 l2 s1 m
               else complete_mapping2 x2' (l1+1) l2 (addStateVar l1 s1) ((l1,x2')::m)
    end.

Fixpoint complete_mapping {ev} {eq} {f} {t} {ac} (l1 : nat) (l2 : nat) (m : list (nat * nat))
                          (s1 : @absState ev eq f t ac) (s2 : @absState ev eq f t ac) :=
    match complete_mapping1 l1 l1 l2 s2 m with
    | (m',l1',l2',s2') => match complete_mapping2 l2' l1' l2' s1 m' with
                          | (m'',l1'',l2'',s1'') => (m'',l1'',l2'',s1'',s2')
                          end
    end.

Fixpoint prove_state_implication {ev} {eq} {f} {t} {ac} (tl : nat) (s1: @absState ev eq f t ac) (s2 : @absState ev eq f t ac) (e : env) (h : heap) : Prop :=
    match tl return Prop with
    | 0 => realizeState s1 nil (e,h) -> realizeState s2 nil (e,empty_heap)
    | S n => exists x, prove_state_implication n (instantiateState s1 x) (instantiateState s2 x) e h
    end.

(*
 * This top level definition is responsible for proving implications.  It works by first pairing off
 * identical components and then setting up a proof goal for the remainder.
 *)
Inductive prove_implication {ev} {eq} {f} {t} {ac} : list (nat * nat) -> @absState ev eq f t ac -> nat -> @absState ev eq f t ac -> nat -> list (nat * nat) -> @absState ev eq f t ac -> Prop :=
    | CILPairR : forall s1 s2 s1' s2' l1 l2 vars vars' vars'' limit1 limit2 tl,
               Some (s1',s2',l1,l2,vars') = pick2RsNiF s1 s2 vars limit1 limit2 (@nil (list (@absExp ev eq f))) (@nil (list (@absExp ev eq f))) ->
               (*pick2RsNi s1 s2 vars limit1 limit2 (@nil (list (@absExp ev eq f))) (@nil (list (@absExp ev eq f))) l1 l2 s1' s2' vars' ->*)
               prove_implication vars' s1' limit1 s2' limit2 vars'' tl ->
               prove_implication vars s1 limit1 s2 limit2 vars'' tl
    (*| CILPairCell : forall s1 s2 s1' s2' loc1 loc2 val1 val2 vars vars' vars'' limit1 limit2 tl,
               pick2Cells s1 s2 vars limit1 limit2 nil nil loc1 loc2 val1 val2 s1' s2' vars' ->
               prove_implication vars' s1' limit1 s2' limit2 vars'' tl ->
               prove_implication vars s1 limit1 s2 limit2 vars'' tl*)
    | CILFinish : forall vars limit1 limit2 s1 s2,
                  prove_implication vars s1 limit1 s2 limit2 vars s1.

Ltac prove_implication := (eapply CILPairR;[solve [compute;reflexivity] | prove_implication]) ||
                          (eapply CILFinish;simpl;reflexivity).

(*
 * The top level state implication theorem.  One state implies another if we
 * can first pair off many of the identical components and then prove that
 * the first state implies the remaining components.
 *)
Theorem stateImplication {ev} {eq} {f} {t} {ac} : forall s state1 (state2 : @absState ev eq f t ac) state1' tl1 tl2 state2' state2'' vars mx l1x l2x state1x state2x state2x',
    realizeState state1 nil s ->
    (state1',tl1) = remove_top_existentials state1 ->
    (state2',tl2) = remove_top_existentials state2 ->
    prove_implication nil state2' tl2 state1' tl1 vars state2'' ->
    (mx,l2x,l1x,state2x,state1x) = complete_mapping tl2 tl1 vars state2'' state1' ->
    state2x' = map_over_state mx l1x l2x state2x ->
    (forall e h b, length b=l1x-> realizeState state1x b (e,h) -> realizeState state2x' b (e,empty_heap)) ->
    realizeState state2 nil s.
Proof. admit. Qed.

Definition basicStateImplication := @stateImplication unit eq_unit unitEval basicState basicAccumulate.

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
    | [H: context [(match env_p (id->option nat) ?X ?Y ?Z with | Some _ => _ | None => _ end)] |- _] => let xx:=fresh in remember (env_p (id->option nat) X Y Z) as xx; destruct xx; compute in H
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
     | [ |- context [env_p _ _ _ _]] => unfold env_p;simpl;try simplifyEval
     | [ |- context [env_p _ _ _]] => unfold env_p;simpl;try simplifyEval
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
Fixpoint destructState {ev} {eq} {f} {t} {ac} (a : @absState ev eq f t ac) (bindings : list (@Value ev)) (s : state) : Prop :=
    match a with
    | AbsStar as1 as2 => exists h1 h2,
                         (destructState as1 bindings (fst s,h1) /\
                          destructState as2 bindings (fst s,h2) /\
                          (forall v, h1 v=None \/ h2 v=None) /\
                          compose_heaps h1 h2=(snd s))
    | AbsOrStar as1 as2 => (destructState as1 bindings s) \/ (destructState as2 bindings s)
    | AbsExists e a => forall  e rl,
                       @absEval ev eq f (env_p _ _ s) bindings e = (ListValue rl) ->
                       (exists x, In x rl /\
                           destructState a (bindings++(x::nil)) s)
    | AbsExistsT a => (exists x, destructState a (bindings++(x::nil)) s)
    | AbsAccumulate i e1 e2 e3 => forall v3 vl,
                    absEval (env_p env heap s) bindings e1 = (ListValue vl) ->
                    absEval (env_p env heap s) bindings e3 = v3 ->
                    ac i (env_p _ _ s) bindings vl e2 v3
    | AbsAll e a => forall rl,
                    absEval (env_p _ _ s) bindings e = ListValue rl ->
                    (forall x, In x rl ->
                               destructState a (bindings++(x::nil)) s)
    | AbsEach e a => forall v rl states l,
                     absEval (env_p _ _ s) bindings e = v ->
                     v = ListValue rl ->
                     allFirsts rl l ->
                     allSeconds states l ->
                     (forall x y, In (x,y) l -> destructState a (bindings++(x::nil)) y) ->
                     fold_compose states s
    | AbsEmpty => (forall x, snd s x=None)
    | AbsLeaf i el => t i (map (absEval (env_p _ _ s) bindings) el) (snd s)
    | AbsMagicWand as1 as2 => exists h1 h2,
                            (destructState as1 bindings (fst s,h1) /\
                             destructState as2 bindings (fst s,h2) /\
                             (forall v, ~(h1 v=None) \/ h2 v=None) /\
                             compose_heaps h2 (snd s)=h1)
    | AbsUpdateVar ss i e => destructState ss bindings s
    | AbsUpdState s1 s2 s3 => destructState s1 bindings s
    end.

Theorem realizeDestructThm {ev} {eq} {f} {t} {ac} : forall s b st,
    @realizeState ev eq f t ac s b st -> destructState s b st.
Proof. admit. Qed.

Ltac removeExistentials :=
    repeat (match goal with
     | [ H:realizeState (AbsExistsT _) _ _ |- _ ] => (inversion H; subst; clear H)
     | [ H: exists _, _ |- _ ] => (inversion H;subst;clear H)
     end).

Theorem pickAssertion {ev} {eq} {f} {t} {ac} : forall fs s e P P' bind bind2 x,
    @realizeState ev eq f t ac P bind s ->
    spickElement P ([e]) P' ->
    fst s = fs ->
    x<>0 ->
    noQVarExp e=true ->
    absEval fs bind2 e = NatValue x.
Proof. admit. Qed.

Theorem pickTerm {ev} {eq} {f} {t} {ac} : forall P bind s fs e P',
    @realizeState ev eq f t ac P bind s ->
    spickElement P e P' ->
    allPredicates e ->
    fst s = fs ->
    @realizeState ev eq f t ac e bind (fs,empty_heap).
Proof. admit. Qed.

Ltac solvePickTerm X := eapply pickTerm;[apply X | solveSPickElement | solveAllPredicates | simpl; reflexivity].

Theorem pickData {ev} {eq} {f} {t} {ac} : forall P bind s fs e P',
    @realizeState ev eq f t ac P bind s ->
    spickElement P e P' ->
    fst s = fs ->
    (exists h, @realizeState ev eq f t ac e bind (fs,h)).
Proof. admit. Qed.

Ltac solvePickData X := eapply pickData;[apply X | solveSPickElement | simpl; reflexivity].

Theorem concreteComposeEmpty : forall s1 s2 eee,
    concreteCompose s1 s2 (eee, empty_heap) <-> s1=(eee, empty_heap) /\ s2=(eee, empty_heap).
Proof. admit. Qed.

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

Fixpoint replaceExp {ev} {eq} {f} (e : @absExp ev eq f ) (val:@absExp ev eq f) (rep:@absExp ev eq f) : @absExp ev eq f :=
   if beq_absExp e val then rep
   else
   match e with
   | AbsConstVal x => AbsConstVal x
   | AbsVar v => AbsVar v
   | AbsQVar v => AbsQVar v
   | AbsFun i l => AbsFun i (map (fun x => replaceExp x val rep) l)
   end.

Fixpoint replaceState {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) (val:@absExp ev eq f) (rep:@absExp ev eq f) : @absState ev eq f t ac :=
   match s with
    | AbsStar s1 s2 => (AbsStar (replaceState s1 val rep) (replaceState s2 val rep))
    | AbsOrStar s1 s2 => (AbsOrStar (replaceState s1 val rep) (replaceState s2 val rep))
    | AbsExistsT s => AbsExistsT (replaceState s val rep)
    | AbsExists e s => AbsExists (replaceExp e val rep) (replaceState s val rep)
    | AbsAll e s => AbsAll (replaceExp e val rep) (replaceState s val rep)
    | AbsEach e s => AbsEach (replaceExp e val rep) (replaceState s val rep)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i l => AbsLeaf i (map (fun x => replaceExp x val rep) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (replaceExp e1 val rep) (replaceExp e2 val rep) (replaceExp e3 val rep)
    | AbsMagicWand s1 s2 => AbsMagicWand (replaceState s1 val rep) (replaceState s2 val rep)
    | AbsUpdateVar s i v => AbsUpdateVar (replaceState s val rep) i (replaceExp v val rep)
    | AbsUpdState s1 s2 s3 => AbsUpdState (replaceState s1 val rep) (replaceState s2 val rep) (replaceState s3 val rep)
   end.

Fixpoint pair_check {a} (f : a -> a -> bool) (l1 : list a) (l2 : list a) :=
    match l1,l2 with
    | nil,nil => true
    | (a::b),(c::d) => if f a c then pair_check f b d else false
    | _,_ => false
    end.

Fixpoint equivExp {ev} {eq} {f} (e1 : @absExp ev eq f ) (e2 : @absExp ev eq f) (val:@absExp ev eq f) (rep:@absExp ev eq f) : bool :=
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

Fixpoint equivState {ev} {eq} {f} {t} {ac} (s1 : @absState ev eq f t ac) (s2 : @absState ev eq f t ac) (val:@absExp ev eq f) (rep:@absExp ev eq f) : bool :=
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

Fixpoint maxBindingExp {ev} {eq} {f} (e : @absExp ev eq f ) : nat :=
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

Theorem expressionSubLR {ev} {eq} {f} {t} {ac} : forall b b' b'' p st e h exp1 exp2 p',
    @realizeState ev eq f t ac ([p]) b st ->
    validPredicate (@absEval ev eq f e b'' (exp1====exp2))=true ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    st = (e,h) ->
    p' = replaceExp p exp1 exp2 ->
    @realizeState ev eq f t ac ([p']) b st.
Proof. admit. Qed.

Theorem expressionNotEqualZero1 {ev} {eq} {f} {t} {ac} : forall b b' b'' p st e h exp p',
    @realizeState ev eq f t ac (p) b st ->
    false=validPredicate (@absEval ev eq f e b'' (#0====exp)) ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    st = (e,h) ->
    p' = replaceState p ((#0) <<<< exp) (#1) ->
    @realizeState ev eq f t ac (p') b st.
Proof. admit. Qed.

Theorem expressionNotEqualZero2 {ev} {eq} {f} {t} {ac} : forall b b' b'' p st e h exp p',
    @realizeState ev eq f t ac (p) b st ->
    false=validPredicate (@absEval ev eq f e b'' (#0====exp)) ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    st = (e,h) ->
    p' = replaceState p ((#0) ==== exp) (#0) ->
    @realizeState ev eq f t ac (p') b st.
Proof. admit. Qed.

Theorem expressionNotEqualZero3 {ev} {eq} {f} {t} {ac} : forall b b' b'' p st e h exp p',
    @realizeState ev eq f t ac (p) b st ->
    false=validPredicate (@absEval ev eq f e b'' (#0====exp)) ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    st = (e,h) ->
    p' = replaceState p (exp ==== (#0)) (#0) ->
    @realizeState ev eq f t ac (p') b st.
Proof. admit. Qed.

Theorem expressionSubRL {ev} {eq} {f} {t} {ac} : forall b b' b'' p st e h exp1 exp2 p',
    @realizeState ev eq f t ac (p) b st ->
    validPredicate (@absEval ev eq f e b'' (exp1====exp2))=true ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    st = (e,h) ->
    p' = replaceState p exp2 exp1 ->
    @realizeState ev eq f t ac (p') b st.
Proof. admit. Qed.

Theorem expressionSubRSLR {ev} {eq} {f} {t} {ac} : forall b b' b'' p st exp1 exp2 p',
    @realizeState ev eq f t ac ([exp1====exp2]) b'' st ->
    @realizeState ev eq f t ac (p) b st ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceState p exp1 exp2 ->
    @realizeState ev eq f t ac (p') b st.
Proof. admit. Qed.

Theorem expressionSubRSNeg {ev} {eq} {f} {t} {ac} : forall b b' b'' p st exp1 p',
    @realizeState ev eq f t ac ([~~exp1]) b'' st ->
    @realizeState ev eq f t ac (p) b st ->
    b' = clipBinding b (maxBindingExp (exp1)) ->
    b' = clipBinding b'' (maxBindingExp (exp1)) ->
    p' = replaceState p exp1 (#0) ->
    @realizeState ev eq f t ac (p') b st.
Proof. admit. Qed.

Theorem expressionSubRSRL {ev} {eq} {f} {t} {ac} : forall b b' b'' p st exp1 exp2 p',
    @realizeState ev eq f t ac ([exp1====exp2]) b'' st ->
    @realizeState ev eq f t ac (p) b st ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceState p exp2 exp1 ->
    @realizeState ev eq f t ac (p') b st.
Proof. admit. Qed.

Theorem expressionSubEval {ev} {eq} {f} {t} {ac} : forall b b' b'' p st exp val p' e,
    @NatValue ev val = @absEval ev eq f e b' exp ->
    @realizeState ev eq f t ac (p) b'' st ->
    e = (fst st) ->
    p' = replaceState p  exp (#val) ->
    b = clipBinding b' (maxBindingExp exp) ->
    b = clipBinding b'' (maxBindingExp exp) ->
    @realizeState ev eq f t ac (p') b'' st.
Proof. admit. Qed.

Theorem expressionSubEvalEval {ev} {eq} {f} {t} {ac} : forall b p st exp1 exp2 p' e,
    @absEval ev eq f e b exp2 = @absEval ev eq f e b exp1 ->
    @realizeState ev eq f t ac (p) b st ->
    e = (fst st) ->
    p' = replaceState p  exp1 exp2 ->
    @realizeState ev eq f t ac (p') b st.
Proof. admit. Qed.

Theorem expressionSubGRSLR {ev} {eq} {f} {t} {ac} : forall b b' b'' p st exp1 exp2 p',
    @realizeState ev eq f t ac ([exp1====exp2]) b'' st ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceExp p exp1 exp2 ->
    @realizeState ev eq f t ac ([p']) b st ->
    @realizeState ev eq f t ac ([p]) b st.
Proof. admit. Qed.

Theorem expressionSubGRSRL {ev} {eq} {f} {t} {ac} : forall b b' b'' p st exp1 exp2 p',
    @realizeState ev eq f t ac ([exp1====exp2]) b'' st ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceExp p exp2 exp1 ->
    @realizeState ev eq f t ac ([p']) b st ->
    @realizeState ev eq f t ac ([p]) b st.
Proof. admit. Qed.

Theorem expressionSubGLR {ev} {eq} {f} {t} {ac} : forall b b' e b'' p st exp1 exp2 p',
    validPredicate (@absEval ev eq f e b'' (exp1====exp2))=true ->
    e = (fst st) ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceExp p exp1 exp2 ->
    @realizeState ev eq f t ac ([p']) b st ->
    @realizeState ev eq f t ac ([p]) b st.
Proof. admit. Qed.

Theorem expressionSubGRL {ev} {eq} {f} {t} {ac} : forall b b' b'' p st exp1 exp2 p' e,
    validPredicate (@absEval ev eq f e b'' (exp1====exp2))=true ->
    e = (fst st) ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceState p exp2 exp1 ->
    @realizeState ev eq f t ac (p') b st ->
    @realizeState ev eq f t ac (p) b st.
Proof. admit. Qed.

Theorem expressionSubGRSNeg {ev} {eq} {f} {t} {ac} : forall b b' b'' p st exp p' e,
    @realizeState ev eq f t ac ([exp]) b'' st ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    p' = replaceExp p (~~exp) (#0) ->
    e = (fst st) ->
    @absEval ev eq f e b p=
    @absEval ev eq f e b p'.
Proof. admit. Qed.

Theorem expressionSubGRSOr1 {ev} {eq} {f} {t} {ac} : forall b b' b'' p st exp p' e x y,
    @realizeState ev eq f t ac ([exp]) b'' st ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    p' = replaceState p ((exp\\//x)//\\y) (y) ->
    e = (fst st) ->
    @realizeState ev eq f t ac (p') b st ->
    @realizeState ev eq f t ac (p) b st.
Proof. admit. Qed.

Theorem expressionSubGRSOr2 {ev} {eq} {f} {t} {ac} : forall b b' b'' p st exp p' e x y,
    @realizeState ev eq f t ac ([exp]) b'' st ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    p' = replaceState p ((x\\//exp)//\\y) (y) ->
    e = (fst st) ->
    @realizeState ev eq f t ac (p') b st ->
    @realizeState ev eq f t ac (p) b st.
Proof. admit. Qed.

Theorem expressionSubGRSNeg1 {ev} {eq} {f} {t} {ac} : forall b b' b'' p st exp p' e,
    @realizeState ev eq f t ac ([exp]) b'' st ->
    b' = clipBinding b (maxBindingExp (exp)) ->
    b' = clipBinding b'' (maxBindingExp (exp)) ->
    p' = replaceState p (~~exp) (#0) ->
    e = (fst st) ->
    @realizeState ev eq f t ac (p') b st ->
    @realizeState ev eq f t ac (p) b st.
Proof. admit. Qed.

Theorem expressionSubRSVP {ev} {eq} {f} {t} {ac} : forall b b' b'' p st exp1 exp2 p' eee,
    @realizeState ev eq f t ac ([exp1====exp2]) b st ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    p' = replaceExp p exp1 exp2 ->
    eee = fst st ->
    validPredicate (@absEval ev eq f eee b'' p)=validPredicate (@absEval ev eq f eee b'' p').
Proof. admit. Qed.

Theorem removeQuantVar {ev} {eq} {f} {t} {ac} : forall n b e h var exp1 exp2,
    @realizeState ev eq f t ac exp2 b (e,h) ->
    nth n b NoValue = NatValue (e var) ->
    equivState exp1 exp2 (!!var) (v(n)) = true ->
    @realizeState ev eq f t ac exp1 b (e,h).
Proof. admit. Qed.

Fixpoint removeReplaceExp {ev} {eq} {f} (loc1 : @absExp ev eq f) (loc2 : @absExp ev eq f) (exp : @absExp ev eq f) :=
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

Fixpoint removeReplaceState {ev} {eq} {f} {t} {ac} (loc1 : @absExp ev eq f) (loc2 : @absExp ev eq f) (s:@absState ev eq f t ac) : @absState ev eq f t ac :=
   match s with
    | AbsStar s1 s2 => (AbsStar (removeReplaceState loc1 loc2 s1) (removeReplaceState loc1 loc2 s2))
    | AbsOrStar s1 s2 => (AbsOrStar (removeReplaceState loc1 loc2 s1) (removeReplaceState loc1 loc2 s2))
    | AbsExistsT s => AbsExistsT (removeReplaceState loc1 loc2 s)
    | AbsExists e s => AbsExists (removeReplaceExp loc1 loc2 e) (removeReplaceState loc1 loc2 s)
    | AbsAll e s => AbsAll (removeReplaceExp loc1 loc2 e) (removeReplaceState loc1 loc2 s)
    | AbsEach e s => AbsEach (removeReplaceExp loc1 loc2 e) (removeReplaceState loc1 loc2 s)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i l => AbsLeaf i (map (removeReplaceExp loc1 loc2) l)
    | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (removeReplaceExp loc1 loc2 e1) (removeReplaceExp loc1 loc2 e2) (removeReplaceExp loc1 loc2 e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (removeReplaceState loc1 loc2 s1) (removeReplaceState loc1 loc2 s2)
    | AbsUpdateVar s i v => AbsUpdateVar (removeReplaceState loc1 loc2 s) i (removeReplaceExp loc1 loc2 v)
    | AbsUpdState s1 s2 s3 => AbsUpdState (removeReplaceState loc1 loc2 s1) (removeReplaceState loc1 loc2 s2) (removeReplaceState loc1 loc2 s3)
   end.

Theorem removeReplace {ev} {eq} {f} {t} {ac} : forall b b' b'' p st e h exp1 exp2 p',
    @realizeState ev eq f t ac (p) b st ->
    validPredicate (@absEval ev eq f e b'' (exp1====exp2))=false ->
    b' = clipBinding b (maxBindingExp (exp1====exp2)) ->
    b' = clipBinding b'' (maxBindingExp (exp1====exp2)) ->
    st = (e,h) ->
    p' = removeReplaceState exp1 exp2 p ->
    @realizeState ev eq f t ac (p') b st.
Proof. admit. Qed.

Fixpoint removeReplaceSameExp {ev} {eq} {f} (l : @absExp ev eq f) (loc : @absExp ev eq f) (exp : @absExp ev eq f) :=
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

Fixpoint removeReplaceSameState {ev} {eq} {f} {t} {ac} (loc1 : @absExp ev eq f) (loc2 : @absExp ev eq f) (s:@absState ev eq f t ac) : @absState ev eq f t ac :=
   match s with
    | AbsStar s1 s2 => (AbsStar (removeReplaceSameState loc1 loc2 s1) (removeReplaceSameState loc1 loc2 s2))
    | AbsOrStar s1 s2 => (AbsOrStar (removeReplaceSameState loc1 loc2 s1) (removeReplaceSameState loc1 loc2 s2))
    | AbsExistsT s => AbsExistsT (removeReplaceSameState loc1 loc2 s)
    | AbsExists e s => AbsExists (removeReplaceSameExp loc1 loc2 e) (removeReplaceSameState loc1 loc2 s)
    | AbsAll e s => AbsAll (removeReplaceSameExp loc1 loc2 e) (removeReplaceSameState loc1 loc2 s)
    | AbsEach e s => AbsEach (removeReplaceSameExp loc1 loc2 e) (removeReplaceSameState loc1 loc2 s)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i l => AbsLeaf i (map (removeReplaceSameExp loc1 loc2) l)
    | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (removeReplaceSameExp loc1 loc2 e1) (removeReplaceSameExp loc1 loc2 e2) (removeReplaceSameExp loc1 loc2 e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (removeReplaceSameState loc1 loc2 s1) (removeReplaceSameState loc1 loc2 s2)
    | AbsUpdateVar s i v => AbsUpdateVar (removeReplaceSameState loc1 loc2 s) i (removeReplaceSameExp loc1 loc2 v)
    | AbsUpdState s1 s2 s3 => AbsUpdState (removeReplaceSameState loc1 loc2 s1) (removeReplaceSameState loc1 loc2 s2) (removeReplaceSameState loc1 loc2 s3)
   end.

Theorem removeReplaceSame {ev} {eq} {f} {t} {ac} : forall b p st l loc p' ll n,
    @realizeState ev eq f t ac ([p]) b st ->
    p' = removeReplaceSameExp l loc p ->
    ListValue ll = @absEval ev eq f (fst st) b l ->
    NatValue n = @absEval ev eq f (fst st) b loc ->
    n < length ll ->
    @realizeState ev eq f t ac ([p']) b st.
Proof. admit. Qed.

Theorem realizeValidPredicate {ev} {eq} {f} {t} {ac} : forall st e h exp b,
    st = (e,h) ->
    (validPredicate (@absEval ev eq f e b exp)=true <-> @realizeState ev eq f t ac ([exp]) b st).
Proof. admit. Qed.

Theorem validPredicateSymmetry {ev} {eq} {f} : forall b e exp1 exp2,
    validPredicate (@absEval ev eq f e b (exp1====exp2))=
    validPredicate (@absEval ev eq f e b (exp2====exp1)).
Proof. admit. Qed.

Function mapSum {t} {teq} {f} (env : id -> nat) (b : list (@Value t)) (values : list (@Value t)) (e : @absExp t teq f) : nat :=
  match values with
  | nil => 0
  | (ff::rr) => match (@absEval t teq f env (b++(ff::nil)) e) with
                | NatValue x => (mapSum env b rr e)+x
                | _ => mapSum env b rr e
                end
  end.

Function singlePred {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) :=
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

Theorem andSum8 {ev} {eq} {f} {t} {ac} : forall v0 v1 v2 v3 v4 v5 v6 v7 vv v r e s state ee,
    @realizeState ev eq f t ac (SUM(r,e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::nil) s ->
    (forall x, In x vv ->
               realizeState state (v0::v1::v2::v3::v4::v5::v6::v7::x::nil) s) ->
    Some ee = @singlePred ev eq f t ac state ->
    (@ListValue ev vv) = @absEval ev eq f (fst s) (v0::v1::v2::v3::v4::v5::v6::v7::nil) r ->
    @realizeState ev eq f t ac (SUM(r,ee //\\ e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::nil) s.
Proof. admit. Qed.

Theorem implySum8x10 {ev} {eq} {f} {t} {ac} : forall v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 vv v r e s state ee,
    @realizeState ev eq f t ac (SUM(r,e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s ->
    (forall x, In x vv ->
               realizeState state (v0::v1::v2::v3::v4::v5::v6::v7::x::nil) s) ->
    Some ee = (@singlePred ev eq f t ac state) ->
    (@ListValue ev vv) = @absEval ev eq f (fst s) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) r ->
    @realizeState ev eq f t ac (SUM(r,(~~(addExpVar 8 (addExpVar 8 ee))) \\// e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s.
Proof. admit. Qed.

Theorem andSum8x10 {ev} {eq} {f} {t} {ac} : forall v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 vv v r e s state ee,
    @realizeState ev eq f t ac (SUM(r,e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s ->
    (forall x, In x vv ->
               realizeState state (v0::v1::v2::v3::v4::v5::v6::v7::x::nil) s) ->
    Some ee = (@singlePred ev eq f t ac state) ->
    (@ListValue ev vv) = @absEval ev eq f (fst s) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) r ->
    @realizeState ev eq f t ac (SUM(r,((addExpVar 8 (addExpVar 8 ee))) //\\ e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s.
Proof. admit. Qed.

Theorem resolveSum8x10 {ev} {eq} {f} {t} {ac} : forall v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 vv v r e s state ee ff,
    @realizeState ev eq f t ac (SUM(r,e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s ->
    (forall x, In x vv ->
               realizeState state (v0::v1::v2::v3::v4::v5::v6::v7::x::nil) s) ->
    Some ee = (@singlePred ev eq f t ac state) ->
    (forall x s, In x vv ->
                 @realizeState ev eq f t ac ([((addExpVar 8 (addExpVar 8 ee)))]) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::x::nil) (s,empty_heap) ->
                 @realizeState ev eq f t ac ([e====ff]) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::x::nil) (s,empty_heap)) ->
    (@ListValue ev vv) = @absEval ev eq f (fst s) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) r ->
    @realizeState ev eq f t ac (SUM(r,ff,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s.
Proof. admit. Qed.

Theorem resolveSum9x10 {ev} {eq} {f} {t} {ac} : forall v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 vv v r e s state ee ff,
    @realizeState ev eq f t ac (SUM(r,e,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s ->
    (forall x, In x vv ->
               realizeState state (v0::v1::v2::v3::v4::v5::v6::v7::v8::x::nil) s) ->
    Some ee = (@singlePred ev eq f t ac state) ->
    (forall x s, In x vv ->
                 @realizeState ev eq f t ac ([(addExpVar 9 ee)]) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::x::nil) (s,empty_heap) ->
                 @realizeState ev eq f t ac ([e====ff]) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::x::nil) (s,empty_heap)) ->
    (@ListValue ev vv) = @absEval ev eq f (fst s) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) r ->
    @realizeState ev eq f t ac (SUM(r,ff,v)) (v0::v1::v2::v3::v4::v5::v6::v7::v8::v9::nil) s.
Proof. admit. Qed.

Theorem sumDiff {ev} {eq} {f} {t} {ac} : forall s b r e s1 s2 sd x,
    @realizeState ev eq f t ac (SUM(r,(e //\\ x),(#s1))) b s ->
    @realizeState ev eq f t ac (SUM(r,e,(#s2))) b s ->
    sd = s2-s1 ->
    @realizeState ev eq f t ac (SUM(r,(e //\\ (~~x)),(#sd))) b s.
Proof. admit. Qed.

Theorem sumAllConv {ev} {eq} {f} {t} {ac} : forall r e b s,
    @realizeState ev eq f t ac (SUM(r,e,#0)) b s ->
    @realizeState ev eq f t ac (AbsAll r ([~~e])) b s.
Proof. admit. Qed.

Function deletenth {t} (x : nat) (l : list t) :=
    match x,l with
    | 0, (f::r) => Some r
    | (S n),(f::r) => match deletenth n r with
                      | Some l => Some (f::l)
                      | _ => None
                      end
    | _,_ => None
    end.

Theorem dumpVar {ev} {eq} {f} {t} {ac} : forall state b s n b',
    @realizeState ev eq f t ac state b s ->
    hasVnState state n=false ->
    Some b' = deletenth n b ->
    @realizeState ev eq f t ac (removeStateVar n state) b' s.
Proof. admit. Qed.

Theorem dumpVar2 {ev} {eq} {f} {t} {ac} : forall state b s n b',
    @realizeState ev eq f t ac (removeStateVar n state) b' s ->
    hasVnState state n=false ->
    Some b' = deletenth n b ->
    @realizeState ev eq f t ac state b s.
Proof. admit. Qed.

Theorem mapSumExists {ev} {eq} {f} {t} {ac} : forall v e b vals exp,
    S v = @mapSum ev eq f e b vals exp ->
    exists x, In x vals /\ @realizeState ev eq f t ac ([exp]) (b++(x::nil)) (e,empty_heap).
Proof. admit. Qed.

Theorem mapSumNeg {ev} {eq} {f} {t} {ac} : forall e b vals exp,
    0 = @mapSum ev eq f e b vals exp ->
    forall x, In x vals -> @realizeState ev eq f t ac ([~~exp]) (b++(x::nil)) (e,empty_heap).
Proof. admit. Qed.

Theorem subRangeSet {ev} : forall x rl rl0 n v,
    rangeSet (@findRecord ev n v) = ListValue rl0 ->
    In x rl0 ->
    In (@NatValue ev n) rl ->
    rangeSet v = ListValue rl ->
    In x rl.
Proof. admit. Qed.

Function replacenth {t} (x : nat) (e : t) (l : list t) :=
    match x,l with
    | 0, (f::r) => Some (e::r)
    | (S n),(f::r) => match replacenth n e r with
                      | Some l => Some (f::l)
                      | _ => None
                      end
    | _,_ => None
    end.

Theorem subBoundVar {ev} {eq} {f} {t} {ac} : forall b eee exp b' p p' n,
    nth n b' NoValue = @absEval ev eq f eee b exp ->
    @realizeState ev eq f t ac p b' (eee, empty_heap) ->
    Some b = replacenth n (nth n b NoValue) b' ->
    p' = replaceState p v(n) exp ->
    @realizeState ev eq f t ac p' b (eee,empty_heap).
Proof. admit. Qed.

Theorem arrayLength {ev} {eq} {f} {t} {ac} : forall v len n b st l,
    @realizeState ev eq f t ac (ARRAY(v,#len,v(n))) b st ->
    nth n b NoValue = ListValue l ->
    length l = len.
Proof. admit. Qed.

Theorem sumExists {ev} {eq} {f} {t} {ac} : forall b eee r e n,
    @realizeState ev eq f t ac (SUM(r,e,(#(S n)))) b (eee,empty_heap) ->
    @realizeState ev eq f t ac (AbsExists r ([e])) b (eee,empty_heap).
Proof. admit. Qed.

Theorem reverse {ev} {eq} {f} {t} {ac} : forall st x y b,
    @realizeState ev eq f t ac ([x====y]) b st ->
    @realizeState ev eq f t ac ([y====x]) b st.
Proof. admit. Qed.





