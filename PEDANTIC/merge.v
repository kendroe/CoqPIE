(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * Merge.v
 * This file contains many useful definitions for merging two abstract states into
 * a single state implied by both.
 *
 * Key definitions:
 *     MergeStatesTheorem
 *     doMergeStates
 *
 **********************************************************************************)

Require Export SfLib.
Require Export ImpHeap.
Require Export AbsState.
Require Export PickElement.
Require Export AbsExecute.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Fold.
Opaque unitEval.

Fixpoint merge_equiv {ev} {eq} {f} (a : list (@absExp ev eq f)) (t : (@absExp ev eq f)) (b : list (list (@absExp ev eq f))) :=
    match b with
    | nil => ((t::a)::nil)
    | (x::y) => if mem_absExp t x then ((a++x)::y) else x::(merge_equiv a t y)
    end.

Fixpoint add_equiv {ev} {eq} {f} (equiv : (list (list (@absExp ev eq f)))) (t1 : (@absExp ev eq f)) (t2 : (@absExp ev eq f)) :=
    match equiv with
    | (a::b) => if mem_absExp t1 a then
                    if mem_absExp t2 a then (a::b) else merge_equiv a t2 b
                else
                    if mem_absExp t2 a then merge_equiv a t1 b else a::(add_equiv b t1 t2)
    | nil => (t1::t2::nil)::nil
    end.

Inductive build_equivalents {ev} {eq} {f} {t} {ac} : @absState ev eq f t ac -> (list (list (@absExp ev eq f))) -> Prop :=
    | BEAdd : forall s s' l r e e',
            spickElement s ([l====r]) s' ->
            build_equivalents s' e ->
            e' = add_equiv e l r ->
            build_equivalents s e'
    | BEDone : forall s, build_equivalents s nil.

Ltac solveBuildEquivalents := solve [eapply BEAdd;[solveSPickElement|solveBuildEquivalents|(compute;reflexivity)]||eapply BEDone].

Fixpoint map_var (m : list (nat * nat)) (v : nat) : option nat :=
   match m with
   | nil => None
   | ((a,x)::r) => if beq_nat x v then Some a else map_var r v
   end.

Fixpoint map_var_right (m : list (nat * nat)) (v : nat) : option nat :=
   match m with
   | nil => None
   | ((a,x)::r) => if beq_nat a v then Some x else map_var r v
   end.

Fixpoint fold_list {EV} {EQ} {T} (l : list (option (@absExp EV EQ T))) :=
   match l with
   | nil => Some nil
   | (f::r) => match f,fold_list r with
               | Some x,Some y => Some (x::y)
               | _,_ => None
               end
   end.

Fixpoint mapAbsQVar {EV} {EQ} {T} (m : list (nat * nat)) (e : @absExp EV EQ T) : option (@absExp EV EQ T) :=
   match e with
   | AbsConstVal v => Some (AbsConstVal v)
   | AbsVar vv => Some (AbsVar vv)
   | AbsQVar v => match map_var m v with | None => None | Some x => Some (AbsQVar x) end
   | AbsFun i el => match fold_list (map (mapAbsQVar m) el) with
                    | None => None
                    | Some l => Some (AbsFun i l)
                    end 
   end.

Fixpoint mapAbsQVarState {EV} {EQ} {F} {T} {AC} (t1 : nat) (t2 : nat) (m : list (nat * nat)) (s : @absState EV EQ F T AC) : option (@absState EV EQ F T AC) :=
   match s with
    | AbsStar s1 s2 => match mapAbsQVarState t1 t2 m s1,mapAbsQVarState t1 t2 m s2 with
                       | Some a, Some b => Some (AbsStar a b)
                       | _, _ => None
                       end
    | AbsOrStar s1 s2 => match mapAbsQVarState t1 t2 m s1,mapAbsQVarState t1 t2 m s2 with
                         | Some a, Some b => Some (AbsOrStar a b)
                         | _, _ => None
                         end
    | AbsExists e s => match mapAbsQVar m e, mapAbsQVarState (t1+1) (t2+1) ((t1,t2)::m) s with
                       | Some a, Some b => Some (AbsExists a b)
                       | _, _ => None
                       end
    | AbsExistsT s => match mapAbsQVarState (t1+1) (t2+1) ((t1,t2)::m) s with
                      | Some x => Some (AbsExistsT x)
                      | None => None
                      end
    | AbsAll e s => match mapAbsQVar m e, mapAbsQVarState (t1+1) (t2+1) ((t1,t2)::m) s with
                    | Some a, Some b => Some (AbsAll a b)
                    | _, _ => None
                    end
    | AbsEach e s => match mapAbsQVar m e, mapAbsQVarState (t1+1) (t2+1) ((t1,t2)::m) s with
                     | Some a, Some b => Some (AbsEach a b)
                     | _, _ => None
                     end
    | AbsEmpty => Some AbsEmpty
    | AbsAccumulate a b c d => match (mapAbsQVar m b),(mapAbsQVar ((t1,t2)::m) c),(mapAbsQVar m d) with
                               | Some bb,Some cc, Some dd => Some (AbsAccumulate a bb cc dd)
                               | _,_,_ => None
                               end
    | AbsLeaf i el => match fold_list (map (mapAbsQVar m) el) with
                      | None => None
                      | Some l => Some (AbsLeaf i l)
                      end
    | AbsMagicWand s1 s2 => match mapAbsQVarState t1 t2 m s1,mapAbsQVarState t1 t2 m s2 with
                       | Some a, Some b => Some (AbsMagicWand a b)
                       | _, _ => None
                       end
    | AbsUpdateVar s i v => match mapAbsQVarState t1 t2 m s,mapAbsQVar m v with
                       | Some a, Some b => Some (AbsUpdateVar a i b)
                       | _, _ => None
                       end
    | AbsUpdState s1 s2 s3 => match mapAbsQVarState t1 t2 m s1,mapAbsQVarState t1 t2 m s2,mapAbsQVarState t1 t2 m s3 with
                       | Some a, Some b, Some c => Some (AbsUpdState a b c)
                       | _, _, _ => None
                       end
   end.


Fixpoint find_list {ev} {eq} {f} t equiv :=
    match equiv with
    | (ff::r) => if @mem_absExp ev eq f t ff then ff else find_list t r
    | nil => (t::nil)
    end.

Fixpoint zero_term {ev} {eq} {f} t equiv :=
    match find_list t equiv with
    | l => @mem_absExp ev eq f (#0) l
    end.

Fixpoint matches_z {ev} {eq} {f} tlist_a equiv :=
    match tlist_a with
    | nil => false
    | (ff::r) => @zero_term ev eq f ff equiv
    end.

Fixpoint matches_zero {ev} {eq} {f} t equiv1 equiv2 :=
    @matches_z ev eq f (find_list t equiv1) equiv2.

Fixpoint null_term {ev} {eq} {f} t equiv :=
    match find_list t equiv with
    | l => @mem_absExp ev eq f (AbsConstVal (ListValue nil)) l
    end.

Fixpoint matches_n {ev} {eq} {f} tlist_a equiv :=
    match tlist_a with
    | nil => false
    | (ff::r) => @null_term ev eq f ff equiv
    end.

Fixpoint matches_null {ev} {eq} {f} t equiv1 equiv2 :=
    @matches_n ev eq f (find_list t equiv1) equiv2.

Fixpoint e_exp {ev} {eq} {f} equiv t1 t2 :=
    match equiv with
    | (ff::r) => if @mem_absExp ev eq f t1 ff then if @mem_absExp ev eq f t2 ff then true
                else e_exp r t1 t2
                else e_exp r t1 t2
    | _ => false
    end.

Fixpoint equiv_exp {ev} {eq} {f} equiv t1 t2 :=
    if @beq_absExp ev eq f t1 t2 then
        true
    else  e_exp equiv t1 t2.

Fixpoint build_equals {ev} {eq} {f} {t} {ac} (x : @absExp ev eq f) (l : list (@absExp ev eq f)) : @absState ev eq f t ac :=
    match l with
    | nil => AbsEmpty
    | a::b => (([x====a]) ** (build_equals x b))
    end.

Fixpoint build_equivs {ev} {eq} {f} {t} {ac} (l : list (list (@absExp ev eq f))) : @absState ev eq f t ac :=
    match l with
    | nil => AbsEmpty
    | (a::r)::b => (build_equals a r) ** (build_equivs b)
    | _::b => build_equivs b
    end.

(*
 * This inductive definition contains the meat of the merging environment.
 * Note the use of pick2RsNi.  There is a subtle issue that the merge operation
 * also has the secondary task of finding an appropriate mapping between
 * bound variables in the two states.  pick2RsNi requires that any quantified
 * variables being matched up in the first parameter of a TREE or cell construct,
 * or the only term in a predicate construct, that the mappings already be present.
 * This forces a top down match of the states.  For example, merging the following
 * two states:
 *     X++++#0 |-> v(0) *
 *     X++++#1 |-> v(1) *
 *     TREE(v(0),v(4),#2,#0::nil)
 * and
 *     X++++#0 |-> v(3) *
 *     X++++#1 |-> v(4) *
 *     TREE(v(0),v(5),#2,#0::nil)
 * will produce:
 *     X++++#0 |-> v(0) *
 *     X++++#1 |-> v(1) *
 *     TREE(v(0),v(4),#2,#0::nil)
 *
 * However matching,
 *     v(1)++++#0 |-> v(0) *
 *     v(1)++++#1 |-> v(1) *
 *     TREE(v(0),v(4),#2,#0::nil)
 * and
 *     v(2)++++#0 |-> v(3) *
 *     v(2)++++#1 |-> v(4) *
 *     TREE(v(0),v(5),#2,#0::nil)
 * will not match unless the input mapping alread maps v(1) to v(2).
 *
 * The parameters are as follows:
 *
 *    #1 : absState - input of the first of the two states being merged
 *                    (top AbsExistsT quantifiers stripped)
 *    #2 : absState - input of the second of the two states being merged
 *                    (top AbsExistsT quantifiers stripped)
 *    #3 : nat - # of quantified variables in first state
 *    #4 : nat - # of quantified variables in second state
 *    #5 : (list (nat * nat)) - input mapping between bound variables
 *    #6 : list (list absExp) - equivalent expressions in first state (for pick2RsNi)
 *    #7 : list (list absExp) - equivalent expressions in second state (for pick2RsNi)
 *    #8 : absState - output of the merged state (with AbsExistsT's stripped off)
 *    #9 : list (nat * nat) - output mapping between bound variables
 *                            (mappings added by pick2RsNi)
 *)
Inductive doMergeStates {ev} {eq} {f} {t} {ac} : @absState ev eq f t ac -> 
                                                 @absState ev eq f t ac ->
                                                 nat -> nat -> (list (nat * nat)) ->
                                                 (list (list (@absExp ev eq f))) ->
                                                 (list (list (@absExp ev eq f))) ->
                                                 @absState ev eq f t ac ->
                                                 @absState ev eq f t ac ->
                                                 (list (nat *nat)) -> nat -> Prop :=
     (* Pair two arbitrary predicates by 'oring' them together in the merged state *)
   | DMOrPredicates1: forall a b a' b' m m' t1 t2 equiv1 equiv2 p1 p2 p2' res tx pairs,
       spickElement a ([p1]) a' ->
       spickElement b ([p2]) b' ->
       Some p2' = @mapAbsQVar ev eq f m p2 ->
       doMergeStates a' b' t1 t2 m equiv1 equiv2 res (([p1]) ** pairs) m' tx ->
       doMergeStates a b t1 t2 m equiv1 equiv2 (([p1 \\// p2']) ** res) pairs m' tx
      (* Pair two predicates where the one from the second state implies the one from the first state *)
   | DMImplyPredicates1: forall a b b' m m' t1 t2 equiv1 equiv2 p2 p2' res tx pairs,
       (*spickElement a (p1) a' ->*)
       spickElement b (p2) b' ->
       Some p2' = @mapAbsQVarState ev eq f t ac t1 t2 m p2 ->
       (forall eee hhh bbb, length bbb=t1 -> realizeState (a ** pairs ** (build_equivs equiv1)) bbb (eee,hhh) -> realizeState p2' bbb (eee,empty_heap)) ->
       doMergeStates a b' t1 t2 m equiv1 equiv2 res pairs m' tx ->
       doMergeStates a b t1 t2 m equiv1 equiv2 (p2' ** res) pairs m' tx
      (* Pair two predicates where the one from the first state implies the one from the second state *)
   | DMImplyPredicates2: forall a b a' b' m m' t1 t2 equiv1 equiv2 p1 p2 p2' res tx pairs,
       spickElement a ([p1]) a' ->
       spickElement b ([p2]) b' ->
       Some p2' = @mapAbsQVar ev eq f m p2 ->
       (forall e b, @absEval ev eq f e b p1 = NatValue 0 -> @absEval ev eq f e b p2' = NatValue 0) ->
       doMergeStates a' b' t1 t2 m equiv1 equiv2 res (([p1]) ** pairs) m' tx ->
       doMergeStates a b t1 t2 m equiv1 equiv2 (([p1]) ** res) pairs m' tx
     (* Finish the pairing process--can only be done when only predicates are left *)
   | DMFinish : forall a b t1 t2 equiv1 equiv2 m m' pairs,
       allPredicates a ->
       allPredicates b ->
       doMergeStates a b t1 t2 m equiv1 equiv2 AbsEmpty pairs m' t1
     (* Remove identical RFun constructs from the two abstract states *)
   | DMRemoveZeroTree1 : forall a a' b b' equiv1 equiv2 t1 t2 m m' r rr h ff s res tx pairs,
       spickElement a (TREE(rr,(AbsQVar h),ff,s)) a' ->
       equiv_exp equiv2 r rr=true ->
       b' = ((addStateVar t2 b) ** [v(t2)====(AbsConstVal (ListValue nil))]) ->
       matches_zero r equiv1 equiv2=true ->
       doMergeStates a' b' t1 (t2+1) ((h,t2)::m) equiv1 ((AbsQVar t2::(AbsConstVal (ListValue nil))::nil)::equiv2) res (pairs ** (TREE(rr,(AbsQVar h),ff,s))) m' tx ->
       doMergeStates a b t1 t2 m equiv1 equiv2 (TREE(r,(AbsQVar h),ff,s) ** res) pairs m' tx
   (*| DMRemoveZeroTree2 : forall a a' b' b equiv1 equiv2 t1 t2 m m' r rr h ff s res tt tx pairs,
       spickElement b (TREE(rr,(AbsQVar h),ff,s)) b' ->
       equiv_exp equiv1 r rr=true ->
       a' = ((addStateVar t1 a) ** [v(t1)====(AbsConstVal (ListValue nil))]) ->
       Some tt = mapStateLeft (t1+1) t2 ((t1,h)::m) (TREE(r,(AbsQVar h),ff,s)) ->
       matches_zero r equiv2 equiv1=true ->
       doMergeStates a' b' (t1+1) t2 ((t1,h)::m) ((AbsQVar t1::(AbsConstVal (ListValue nil))::nil)::equiv1) equiv2 res m' tx ->
       doMergeStates a b t1 t2 m equiv1 equiv2 (AbsExistsT (tt ** res)) m' tx*)
   | DMRemoveZeroAll1 : forall a a' b equiv1 equiv2 t1 t2 m m' h p res hh tx pairs,
       spickElement a (AbsAll TreeRecords(AbsQVar h) p) a' ->
       Some hh = map_var_right m h ->
       null_term (AbsQVar hh) equiv2=true ->
       doMergeStates a' b t1 t2 m equiv1 equiv2 res ((AbsAll TreeRecords(AbsQVar h) p) ** pairs) m' tx ->
       doMergeStates a b t1 t2 m equiv1 equiv2 ((AbsAll TreeRecords(AbsQVar h) p) ** res) pairs m' tx
   | DMRemoveZeroAll2 : forall a b' b equiv1 equiv2 t1 t2 m m' h p res tt hh tx pairs,
       spickElement b (AbsAll TreeRecords(AbsQVar h) p) b' ->
       Some tt = mapStateLeft t1 t2 m (AbsAll TreeRecords(AbsQVar h) p) ->
       Some hh = (map_var m h) ->
       null_term (AbsQVar hh) equiv1=true ->
       doMergeStates a b' t1 t2 m equiv1 equiv2 res pairs m' tx ->
       doMergeStates a b t1 t2 m equiv1 equiv2 (tt ** res) pairs m' tx
   | DMAddPair : forall a b t1 t2 m m' equiv1 equiv2 l r res tx pairs,
                 l < t1 ->
                 r < t2 ->
                 no_first l m=true ->
                 no_second r m=true ->
                 doMergeStates a b t1 t2 ((l,r)::m) equiv1 equiv2 res pairs m' tx ->
                 doMergeStates a b t1 t2 m equiv1 equiv2 res pairs m' tx
   | DMRemoveR : forall a b equiv1 equiv2 t1 t2 h1 h2 m' m'' a' b' m res tx pairs,
       Some (a',b',h1,h2,m') = pick2RsNiF a b m t1 t2 equiv1 equiv2 ->
       (*pick2RsNi a b m t1 t2 equiv1 equiv2 h1 h2 a' b' m' ->*)
       doMergeStates a' b' t1 t2 m' equiv1 equiv2 res (h1 ** pairs) m'' tx ->
       doMergeStates a b t1 t2 m equiv1 equiv2 (h1 ** res) pairs m'' tx.

Ltac DMRemoveZeroTree1 x := eapply DMRemoveZeroTree1 with (r := x);[solveSPickElement | (compute;reflexivity) | (compute;reflexivity) | (compute;reflexivity) | idtac].

(*Ltac DMRemoveZeroTree2 x := eapply DMRemoveZeroTree2 with (r := x);[solveSPickElement | (compute;reflexivity) | (compute;reflexivity) | (compute;reflexivity) | (compute;reflexivity) | idtac].*)

Ltac DMRemoveZeroAll1 := eapply DMRemoveZeroAll1;[solveSPickElement | (compute;reflexivity) | (compute;reflexivity) | idtac].

Ltac DMRemoveZeroAll2 := eapply DMRemoveZeroAll2;[solveSPickElement | (compute;reflexivity) | (compute;reflexivity) | (compute;reflexivity) | idtac].

Fixpoint addNExistsT {ev} {eq} {f} {t} {ac} n e :=
    match n with
    | 0 => e
    | (S n1) => addNExistsT n1 (@AbsExistsT ev eq f t ac e)
    end.
(*
 * This is the theorem that sets up state merging through pairing of the components
 *)
Theorem MergeStatesTheorem {ev} {eq} {f} {t} {ac} : forall s1 s2 t1 t2 s1' s2' m sm sm' equiv1 equiv2 tx,
    (s1',t1) = @remove_top_existentials ev eq f t ac s1 ->
    (s2',t2) = @remove_top_existentials ev eq f t ac s2 ->
    build_equivalents s1' equiv1 ->
    build_equivalents s2' equiv2 ->
    doMergeStates s1' s2' t1 t2 nil equiv1 equiv2 sm AbsEmpty m tx ->
    sm' = addNExistsT t1 sm ->
    mergeStates s1 s2 sm'.
Proof. admit. Qed.

(*
 * Tactics for automating the merge process
 *)
Ltac doMergeStates :=
        (eapply DMRemoveR; [(solve [compute;reflexivity]) | doMergeStates]) ||
        (idtac).

Ltac startMerge :=
    eapply MergeStatesTheorem;[
        (compute; reflexivity) |
        (compute; reflexivity) |
        solveBuildEquivalents |
        solveBuildEquivalents |
        idtac |
        (compute; reflexivity)].

Ltac finishMerge := eapply DMFinish;[solveAllPredicates | solveAllPredicates].

(* **************************************************************************
 *
 * Finally, we have auxiliary theorems for performing a fold before merging.
 *
 ****************************************************************************)

Theorem foldHeapTheorem: forall ev eq f t ac s s' env sr,
    realizeState s env sr -> @foldHeap ev eq f t ac s s' -> realizeState s' env sr.
Proof. admit. Qed.

Theorem foldLeft : forall ev eq f t ac s s' sx m,
    @foldHeap ev eq f t ac s s' ->
    mergeStates s' sx m ->
    mergeStates s sx m.
Proof.
    unfold mergeStates. intros. inversion H0. subst. clear H0. split.

    intros. apply H1. eapply foldHeapTheorem. eapply H0. apply H.

    intros. apply H2. apply H0.
Qed.

Theorem foldRight : forall ev eq f t ac s s' sx m,
    @foldHeap ev eq f t ac s s' ->
    mergeStates sx s' m ->
    mergeStates sx s m.
Proof.
    unfold mergeStates. intros. inversion H0. subst. clear H0. split.

    intros. eapply H1. apply H0.

    intros. eapply H2. eapply foldHeapTheorem. apply H0. apply H.
Qed.

Theorem foldAllTheorem: forall ev eq f t ac s s' env sr,
    realizeState s env sr -> @foldAll ev eq f t ac s s' -> realizeState s' env sr.
Proof. admit. Qed.


Theorem foldAllLeft : forall ev eq f t ac s s' sx m,
    @foldAll ev eq f t ac s s' ->
    mergeStates s' sx m ->
    mergeStates s sx m.
Proof.
    unfold mergeStates. intros. inversion H0. subst. clear H0. split.

    intros. apply H1. eapply foldAllTheorem. eapply H0. apply H.

    intros. apply H2. apply H0.
Qed.

Theorem foldAllRight : forall ev eq f t ac s s' sx m,
    @foldAll ev eq f t ac s s' ->
    mergeStates sx s' m ->
    mergeStates sx s m.
Proof.
    unfold mergeStates. intros. inversion H0. subst. clear H0. split.

    intros. eapply H1. apply H0.

    intros. eapply H2. eapply foldAllTheorem. apply H0. apply H.
Qed.


