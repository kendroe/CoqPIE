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

Fixpoint merge_equiv (a : list absExp) (t : absExp) (b : list (list absExp)) :=
    match b with
    | nil => ((t::a)::nil)
    | (x::y) => if mem_absExp t x then ((a++x)::y) else x::(merge_equiv a t y)
    end.

Fixpoint add_equiv (equiv : (list (list absExp))) (t1 : absExp) (t2 : absExp) :=
    match equiv with
    | (a::b) => if mem_absExp t1 a then
                    if mem_absExp t2 a then (a::b) else merge_equiv a t2 b
                else
                    if mem_absExp t2 a then merge_equiv a t1 b else a::(add_equiv b t1 t2)
    | nil => (t1::t2::nil)::nil
    end.

Inductive build_equivalents : absState -> (list (list absExp)) -> Prop :=
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

Fixpoint fold_list (l : list (option absExp)) :=
   match l with
   | nil => Some nil
   | (f::r) => match f,fold_list r with
               | Some x,Some y => Some (x::y)
               | _,_ => None
               end
   end.

Fixpoint mapAbsQVar (m : list (nat * nat)) (e : absExp) : option absExp :=
   match e with
   | AbsConstVal v => Some (AbsConstVal v)
   | AbsVar vv => Some (AbsVar vv)
   | AbsQVar v => match map_var m v with | None => None | Some x => Some (AbsQVar x) end
   | AbsFun i el => match fold_list (map (mapAbsQVar m) el) with
                    | None => None
                    | Some l => Some (AbsFun i l)
                    end 
   end.

Fixpoint mapAbsQVarState (t1 : nat) (t2 : nat) (m : list (nat * nat)) (s : absState) : option absState :=
   match s with
    | AbsStar s1 s2 => match mapAbsQVarState t1 t2 m s1,mapAbsQVarState t1 t2 m s2 with
                       | Some a, Some b => Some (AbsStar a b)
                       | _, _ => None
                       end
    | AbsOrStar s1 s2 => match mapAbsQVarState t1 t2 m s1,mapAbsQVarState t1 t2 m s2 with
                         | Some a, Some b => Some (AbsOrStar a b)
                         | _, _ => None
                         end
    | AbsExists e s => match mapAbsQVar m e, mapAbsQVarState (t1+1) (t2+1) ((0,0)::(push_pairs m)) s with
                       | Some a, Some b => Some (AbsExists a b)
                       | _, _ => None
                       end
    | AbsExistsT s => match mapAbsQVarState (t1+1) (t2+1) ((0,0)::(push_pairs m)) s with
                      | Some x => Some (AbsExistsT x)
                      | None => None
                      end
    | AbsAll e s => match mapAbsQVar m e, mapAbsQVarState (t1+1) (t2+1) ((0,0)::(push_pairs m)) s with
                    | Some a, Some b => Some (AbsAll a b)
                    | _, _ => None
                    end
    | AbsEach e s => match mapAbsQVar m e, mapAbsQVarState (t1+1) (t2+1) ((0,0)::(push_pairs m)) s with
                     | Some a, Some b => Some (AbsEach a b)
                     | _, _ => None
                     end
    | AbsEmpty => Some AbsEmpty
    | AbsNone => Some AbsNone
    | AbsAny => Some AbsAny
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
    | AbsUpdateLoc s i v => match mapAbsQVarState t1 t2 m s,mapAbsQVar m i,mapAbsQVar m v with
                       | Some a, Some b, Some c => Some (AbsUpdateLoc a b c)
                       | _, _, _ => None
                       end
    | AbsUpdateWithLoc s i v => match mapAbsQVarState t1 t2 m s,mapAbsQVar m v with
                       | Some a, Some b => Some (AbsUpdateWithLoc a i b)
                       | _, _ => None
                       end
    | AbsUpdState s1 s2 s3 => match mapAbsQVarState t1 t2 m s1,mapAbsQVarState t1 t2 m s2,mapAbsQVarState t1 t2 m s3 with
                       | Some a, Some b, Some c => Some (AbsUpdState a b c)
                       | _, _, _ => None
                       end
    | AbsClosure s el => match fold_list (map (mapAbsQVar m) el) with
                         | None => None
                         | Some l => Some (AbsClosure s l)
                         end
   end.


Fixpoint find_list t equiv :=
    match equiv with
    | (ff::r) => if mem_absExp t ff then ff else find_list t r
    | nil => (t::nil)
    end.

Fixpoint zero_term t equiv :=
    match find_list t equiv with
    | l => mem_absExp (#0) l
    end.

Fixpoint matches_z tlist_a equiv :=
    match tlist_a with
    | nil => false
    | (ff::r) => zero_term ff equiv
    end.

Fixpoint matches_zero t equiv1 equiv2 :=
    matches_z (find_list t equiv1) equiv2.

Fixpoint null_term t equiv :=
    match find_list t equiv with
    | l => mem_absExp (AbsConstVal (ListValue nil)) l
    end.

Fixpoint matches_n tlist_a equiv :=
    match tlist_a with
    | nil => false
    | (ff::r) => null_term ff equiv
    end.

Fixpoint matches_null t equiv1 equiv2 :=
    matches_n (find_list t equiv1) equiv2.

Fixpoint e_exp equiv t1 t2 :=
    match equiv with
    | (ff::r) => if mem_absExp t1 ff then if mem_absExp t2 ff then true
                else e_exp r t1 t2
                else e_exp r t1 t2
    | _ => false
    end.

Fixpoint equiv_exp equiv t1 t2 :=
    if beq_absExp t1 t2 then
        true
    else  e_exp equiv t1 t2.

Fixpoint build_equals (x : absExp) (l : list absExp) : absState :=
    match l with
    | nil => AbsEmpty
    | a::b => (([x====a]) ** (build_equals x b))
    end.

Fixpoint build_equivs (l : list (list absExp)) : absState :=
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
Inductive doMergeStates : absState -> 
                                                 absState ->
                                                 nat -> nat -> (list (nat * nat)) ->
                                                 (list (list absExp)) ->
                                                 (list (list absExp)) ->
                                                 absState ->
                                                 absState ->
                                                 (list (nat *nat)) -> nat -> Prop :=
     (* Pair two arbitrary predicates by 'oring' them together in the merged state *)
   | DMOrPredicates1: forall a b a' b' m m' t1 t2 equiv1 equiv2 p1 p2 p2' res tx pairs,
       spickElement a ([p1]) a' ->
       spickElement b ([p2]) b' ->
       Some p2' = mapAbsQVar m p2 ->
       doMergeStates a' b' t1 t2 m equiv1 equiv2 res (([p1 \\// p2']) ** pairs) m' tx ->
       doMergeStates a b t1 t2 m equiv1 equiv2 (([p1 \\// p2']) ** res) pairs m' tx
     (* Pair two arbitrary predicates by 'oring' them together in the merged state *)
   | DMOrPredicates2: forall a b a' b' m m' t1 t2 equiv1 equiv2 p1 p2 p2' res tx pairs,
       spickElement (a ** (build_equivs equiv1)) ([p1]) a' ->
       spickElement (b ** (build_equivs equiv2)) ([p2]) b' ->
       Some p2' = mapAbsQVar m p2 ->
       doMergeStates a b t1 t2 m equiv1 equiv2 res (([p1 \\// p2']) ** pairs) m' tx ->
       doMergeStates a b t1 t2 m equiv1 equiv2 (([p1 \\// p2']) ** res) pairs m' tx
      (* Pair two predicates where the one from the second state implies the one from the first state *)
   | DMImplyPredicates1: forall a b b' m m' t1 t2 equiv1 equiv2 p2 p2' res tx pairs,
       (*spickElement a (p1) a' ->*)
       spickElement b (p2) b' ->
       Some p2' = mapAbsQVarState t1 t2 m p2 ->
       (forall eee hhh bbb, length bbb=t1 -> realizeState (a ** pairs ** (build_equivs equiv1)) bbb (eee,hhh) -> realizeState p2' bbb (eee,empty_heap)) ->
       doMergeStates a b' t1 t2 m equiv1 equiv2 res pairs m' tx ->
       doMergeStates a b t1 t2 m equiv1 equiv2 (p2' ** res) pairs m' tx
      (* Pair two predicates where the one from the first state implies the one from the second state *)
   | DMImplyPredicates2: forall a b a' b' m m' t1 t2 equiv1 equiv2 p1 res tx pairs,
       spickElement a (p1) a' ->
       Some b' = mapAbsQVarState t1 t2 m b ->
       (forall eee hhh bbb, length bbb=t1 -> realizeState (b' ** pairs ** (build_equivs equiv1)) bbb (eee,hhh) -> realizeState p1 bbb (eee,empty_heap)) ->
       doMergeStates a' b t1 t2 m equiv1 equiv2 res (p1 ** pairs) m' tx ->
       doMergeStates a b t1 t2 m equiv1 equiv2 (p1 ** res) pairs m' tx
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

Fixpoint addNExistsT n e :=
    match n with
    | 0 => e
    | (S n1) => addNExistsT n1 (AbsExistsT e)
    end.
(*
 * This is the theorem that sets up state merging through pairing of the components
 *)
Theorem MergeStatesTheorem : forall s1 s2 t1 t2 s1' s2' m sm sm' equiv1 equiv2 tx,
    (s1',t1) = remove_top_existentials s1 ->
    (s2',t2) = remove_top_existentials s2 ->
    build_equivalents s1' equiv1 ->
    build_equivalents s2' equiv2 ->
    doMergeStates s1' s2' t1 t2 nil equiv1 equiv2 sm AbsEmpty m tx ->
    sm' = addNExistsT t1 sm ->
    mergeStates s1 s2 sm'.
Proof. admit. Admitted.

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

Theorem foldHeapTheorem: forall s s' env sr,
    realizeState s env sr -> foldHeap s s' -> realizeState s' env sr.
Proof. admit. Admitted.

Theorem foldLeft : forall s s' sx m,
    foldHeap s s' ->
    mergeStates s' sx m ->
    mergeStates s sx m.
Proof.
    (*unfold mergeStates. intros. inversion H0. subst. clear H0. split.

    intros. apply H1. eapply foldHeapTheorem. eapply H0. apply H.

    intros. apply H2. apply H0.*) admit.
Admitted.

Theorem foldRight : forall s s' sx m,
    foldHeap s s' ->
    mergeStates sx s' m ->
    mergeStates sx s m.
Proof.
    (*unfold mergeStates. intros. inversion H0. subst. clear H0. split.

    intros. eapply H1. apply H0.

    intros. eapply H2. eapply foldHeapTheorem. apply H0. apply H.*) admit.
Admitted.

Theorem foldAllTheorem: forall s s' env sr,
    realizeState s env sr -> foldAll s s' -> realizeState s' env sr.
Proof. admit. Admitted.


Theorem foldAllLeft : forall s s' sx m,
    foldAll s s' ->
    mergeStates s' sx m ->
    mergeStates s sx m.
Proof.
    (*unfold mergeStates. intros. inversion H0. subst. clear H0. split.

    intros. apply H1. eapply foldAllTheorem. eapply H0. apply H.

    intros. apply H2. apply H0.*) admit.
Admitted.

Theorem foldAllRight : forall s s' sx m,
    foldAll s s' ->
    mergeStates sx s' m ->
    mergeStates sx s m.
Proof.
    (*unfold mergeStates. intros. inversion H0. subst. clear H0. split.

    intros. eapply H1. apply H0.

    intros. eapply H2. eapply foldAllTheorem. apply H0. apply H.*) admit.
Admitted.

Theorem mergeReturnStatesTrivial1: forall Q r r1,
    mergeReturnStates AbsNone Q Q r1 r r.
Proof.
    admit.
Admitted.

Theorem mergeReturnStatesTrivial2: forall Q r r1,
    mergeReturnStates Q AbsNone Q r r1 r.
Proof.
    admit.
Admitted.

Theorem mergeStatesTrivial1: forall Q,
    mergeStates AbsNone Q Q.
Proof.
    admit.
Admitted.

Theorem mergeStatesTrivial2: forall Q,
    mergeStates Q AbsNone Q.
Proof.
    admit.
Admitted.

Fixpoint stripVar (v : id) (s: absState) : option absState :=
    match s with
    | AbsExists e s => if hasVarExp e v then Some AbsEmpty else
                       match stripVar v s with
                       | Some s => Some (AbsExists e s)
                       | None => None
                       end
    | AbsAll e s => if hasVarExp e v then Some AbsEmpty else
                       match stripVar v s with
                       | Some s => Some (AbsAll e s)
                       | None => None
                       end
    | AbsEach e s => if hasVarExp e v then Some AbsEmpty else
                       match stripVar v s with
                       | Some s => Some (AbsEach e s)
                       | None => None
                       end
    | AbsExistsT s => match stripVar v s with
                      | Some s => Some (AbsExistsT s)
                      | None => None
                      end
    | AbsStar a b => match stripVar v a,stripVar v b with
                     | Some a,Some b => Some (AbsStar a b)
                     | _,_ => None
                     end
    | AbsOrStar a b => match stripVar v a,stripVar v b with
                       | Some a,Some b => Some (AbsOrStar a b)
                       | _,_ => None
                       end
    | AbsMagicWand a b => match stripVar v a,stripVar v b with
                          | Some a,Some b => Some (AbsMagicWand a b)
                          | _,_ => None
                          end
    | AbsUpdState a b c => match stripVar v a,stripVar v b,stripVar v c with
                         | Some a,Some b,Some c => Some (AbsUpdState a b c)
                         | _,_,_ => None
                         end
    | ([x]) => if hasVarExp x v then Some AbsEmpty else Some ([x])
    | AbsAccumulate i a b c => if hasVarExp a v then Some AbsEmpty else
                               if hasVarExp b v then Some AbsEmpty else
                               if hasVarExp c v then Some AbsEmpty else
                               Some (AbsAccumulate i a b c)
    | AbsLeaf i vl => if hasVarExpList vl v then None else Some (AbsLeaf i vl)
    | AbsEmpty => Some AbsEmpty
    | AbsAny => Some AbsAny
    | AbsNone => Some AbsNone
    | AbsUpdateVar s i e => if beq_id i v then stripVar v s
                            else if hasVarExp e v then None else
                            match stripVar v s with
                            | Some s => Some (AbsUpdateVar s i e)
                            | None => None
                            end
    | AbsUpdateWithLoc s i e => if beq_id i v then stripVar v s
                                else if hasVarExp e v then None else
                                match stripVar v s with
                                | Some s => Some (AbsUpdateWithLoc s i e)
                                | None => None
                                end
    | AbsUpdateLoc s i e => if hasVarExp i v then None else
                            if hasVarExp e v then None else
                            match stripVar v s with
                            | Some s => Some (AbsUpdateLoc s i e)
                            | None => None
                            end
    | AbsClosure s el => if hasVarExpList el v then None else Some (AbsClosure s el)
    end.

Fixpoint stripVarInside (v : id) (s: absState) :=
    match s with
    | AbsExistsT s => AbsExistsT (stripVarInside v s)
    | AbsStar a b => AbsStar (stripVarInside v a) (stripVarInside v b)
    | AbsMagicWand a b => AbsMagicWand (stripVarInside v a) (stripVarInside v b)
    | AbsUpdateVar s i e => if beq_id i v then AbsUpdateVar
                            (match (stripVar v s) with Some s => s | _ => s end) i e else
                            AbsUpdateVar (stripVarInside v s) i e
    | AbsUpdateWithLoc s i e => if beq_id i v then AbsUpdateWithLoc
                                (match (stripVar v s) with Some s => s | _ => s end) i e else
                                AbsUpdateWithLoc (stripVarInside v s) i e
    | AbsUpdateLoc s i e => AbsUpdateLoc (stripVarInside v s) i e
    | x => x
    end.

Theorem mergeStripVarLeft: forall v left left' right merge,
    Some left' = stripVar v left ->
    mergeStates left' right merge ->
    mergeStates left right merge.
Proof.
    admit.
Admitted.

Theorem mergeStripVarRight: forall v left right' right merge,
    Some right' = stripVar v right ->
    mergeStates left right' merge ->
    mergeStates left right merge.
Proof.
    admit.
Admitted.

Theorem mergeStripVarInsideLeft: forall v left left' right merge,
    left' = stripVarInside v left ->
    mergeStates left' right merge ->
    mergeStates left right merge.
Proof.
    admit.
Admitted.

Theorem mergeStripVarInsideRight: forall v left right' right merge,
    right' = stripVarInside v right ->
    mergeStates left right' merge ->
    mergeStates left right merge.
Proof.
    admit.
Admitted.

Fixpoint findInTree (v : absExp) (s : absState) : option (absExp * absState) :=
    match s with
    | AbsStar a b => match findInTree v a with
                     | Some (t,a') => Some (t, AbsStar a' b)
                     | None => match findInTree v b with
                               | Some (t,b') => Some(t,AbsStar a b')
                               | None => None
                               end
                     end
    | [ (vv inTree x)] => if beq_absExp v vv then Some (x,AbsEmpty) else None
    | _ => None
    end.

Fixpoint findTheTree (v : absExp) (s : absState) : option absState :=
    match s with
    | AbsStar a b => match findTheTree v a with
                     | Some a' => Some a'
                     | None => match findTheTree v b with
                               | Some b' => Some b'
                               | None => None
                               end
                     end
    | (TREE(r,d,n,f)) => if beq_absExp d v then Some (TREE(r,d,n,f)) else None
    | _ => None
    end.

Fixpoint propagateLoc2 (v : id) (e : absExp) (s : absState) :=
    match e with
    | ((x)++++(#n)) => match findInTree x s with
                       | None => None
                       | Some (tf,s') => match findTheTree tf s' with
                                         | Some (TREE(ee,vv,nn,f)) => if mem_absExp (#n) f then (if hasVarState s' v then
                              match (substVarState (addStateVar 0 s') v v(0)) with
                              | Some xx => Some (AbsStar (AbsExistsT (xx ** [v(0) inTree (substVar (addExpVar 0 vv) v v(0))])) (if hasVarExp x v then ([(!!v) inTree vv \\// (!!v)====(#0)]) else ([(!!v) inTree vv \\// (!!v)====(#0)]) ** ([x inTree vv])))
                              | _ => None
                              end
                          else
                              Some (AbsStar s' (if hasVarExp x v then ([(!!v) inTree vv \\// (!!v)====(#0)]) else ([(!!v) inTree vv \\// (!!v)====(#0)] ** [x inTree vv])))) else None
                                         | _ => None
                                         end
                       end
    | (x) => match findInTree x s with
                       | None => None
                       | Some (tf,s') => match findTheTree tf s' with
                                         | Some (TREE(ee,vv,nn,f)) => if mem_absExp (#0) f then (if hasVarState s' v then
                              match (substVarState (addStateVar 0 s') v v(0)) with
                              | Some xx => Some (AbsStar (AbsExistsT (xx ** ([v(0) inTree (substVar (addExpVar 0 vv) v v(0))]))) (if hasVarExp x v then ([(!!v) inTree vv \\// (!!v)====(#0)]) else ([(!!v) inTree vv \\// (!!v)====(#0)]) ** [x inTree vv]))
                              | _ => None
                              end
                          else
                              Some (AbsStar s' (if hasVarExp x v then ([(!!v) inTree vv \\// (!!v)====(#0)]) else ([(!!v) inTree vv \\// (!!v)====(#0)] ** [x inTree vv])))) else None
                                         | _ => None
                                         end
                     end
    end.

Fixpoint propagateLoc (v : id) (e : absExp) (s : absState) :=
    match e with
    | ((x)++++(#n)) => match findInTree x s with
                       | None => None
                       | Some (tf,s') => match findTheTree tf s' with
                                         | Some (TREE(ee,vv,nn,f)) => if mem_absExp (#n) f then (if hasVarState s' v then None else Some (AbsStar s' (if hasVarExp x v then ([(!!v) inTree vv \\// (!!v)====(#0)]) else ([(!!v) inTree vv \\// (!!v)====(#0)] ** [x inTree vv])))) else None
                                         | _ => None
                                         end
                       end
    | (x) => match findInTree x s with
                       | None => None
                       | Some (tf,s') => match findTheTree tf s' with
                                         | Some (TREE(ee,vv,nn,f)) => if mem_absExp (#0) f then (if hasVarState s' v then None else Some (AbsStar s' (if hasVarExp x v then ([(!!v) inTree vv \\// (!!v)====(#0)]) else ([(!!v) inTree vv \\// (!!v)====(#0)] ** [x inTree vv])))) else None
                                         | _ => None
                                         end
                     end
    end.

Fixpoint removeUpdateWithLocTraverse2 (s : absState) : absState :=
    match s with
    | AbsUpdateWithLoc s i v => match propagateLoc2 i v s with
                                | Some s' => s'
                                | None => AbsUpdateWithLoc (removeUpdateWithLocTraverse2 s) i v
                                end
    | AbsStar l r => AbsStar (removeUpdateWithLocTraverse2 l) (removeUpdateWithLocTraverse2 r)
    | AbsUpdateLoc s i v => AbsUpdateLoc (removeUpdateWithLocTraverse2 s) i v
    | AbsUpdateVar s i v => AbsUpdateVar (removeUpdateWithLocTraverse2 s) i v
    | AbsExistsT s => AbsExistsT (removeUpdateWithLocTraverse2 s)
    | x => x
    end.

Fixpoint removeUpdateWithLocTraverse (s : absState) : absState :=
    match s with
    | AbsUpdateWithLoc s i v => match propagateLoc i v s with
                                | Some s' => s'
                                | None => AbsUpdateWithLoc (removeUpdateWithLocTraverse s) i v
                                end
    | AbsStar l r => AbsStar (removeUpdateWithLocTraverse l) (removeUpdateWithLocTraverse r)
    | AbsUpdateLoc s i v => AbsUpdateLoc (removeUpdateWithLocTraverse s) i v
    | AbsUpdateVar s i v => AbsUpdateVar (removeUpdateWithLocTraverse s) i v
    | AbsExistsT s => AbsExistsT (removeUpdateWithLocTraverse s)
    | x => x
    end.

Theorem removeUpdateWithLocTraverseLeft : forall l r m,
    mergeStates (removeUpdateWithLocTraverse l) r m ->
    mergeStates l r m.
Proof.
    admit.
Admitted.

Theorem removeUpdateWithLocTraverseRight : forall l r m,
    mergeStates l (removeUpdateWithLocTraverse r) m ->
    mergeStates l r m.
Proof.
    admit.
Admitted.

Theorem removeUpdateWithLocTraverseLeft2 : forall l r m,
    mergeStates (removeUpdateWithLocTraverse2 l) r m ->
    mergeStates l r m.
Proof.
    admit.
Admitted.

Theorem removeUpdateWithLocTraverseRight2 : forall l r m,
    mergeStates l (removeUpdateWithLocTraverse2 r) m ->
    mergeStates l r m.
Proof.
    admit.
Admitted.

Fixpoint getConstraints (s : absState) : list absState :=
    match s with
    | AbsStar a b => (getConstraints a)++(getConstraints b)
    | ([x]) => ([x])::nil
    | _ => nil
    end.

Fixpoint stripStates v (l : list absState) :=
    match l with
    | nil => nil
    | (a::b) => if hasVarState a v then stripStates v b else a::(stripStates v b)
    end.

Fixpoint mapRelevantConstraints (v : id) (v' : id) (l : list absState) :=
    match l with
    | (f::r) => if hasVarState f v then (replaceStateExp (!!v) (!!v') f)::(mapRelevantConstraints v v' r) else (mapRelevantConstraints v v' r)
    | nil => nil
    end.

Fixpoint findPromoteConstraints (v : id) (e : absExp) (s : absState) (l : list absState) : list absState :=
    match s with
    | AbsStar a b => (findPromoteConstraints v e a ((getConstraints b)++l))++(findPromoteConstraints v e b ((getConstraints a)++l))
    | AbsUpdateVar s i vv => stripStates i (findPromoteConstraints v e s (stripStates i l))
    | AbsUpdateWithLoc s i vv => if beq_absExp e vv then (mapRelevantConstraints i v l) else stripStates i (findPromoteConstraints v e s (stripStates i l))
    | _ => nil
    end.

Fixpoint fold_star l root :=
    match l with
    | nil => root
    | (a::b) => fold_star b (root ** a)
    end.

Fixpoint promoteConstraints (s : absState) : absState :=
    match s with
    | AbsUpdateWithLoc s i v => fold_star (findPromoteConstraints i v s nil) (AbsUpdateWithLoc (promoteConstraints s) i v)
    | AbsStar l r => AbsStar (promoteConstraints l) (promoteConstraints r)
    | AbsUpdateLoc s i v => AbsUpdateLoc (promoteConstraints s) i v
    | AbsUpdateVar s i v => AbsUpdateVar (promoteConstraints s) i v
    | AbsExistsT s => AbsExistsT (promoteConstraints s)
    | x => x
    end.

Theorem promoteConstraintsLeft : forall l r m,
    mergeStates (promoteConstraints l) r m ->
    mergeStates l r m.
Proof.
    admit.
Admitted.

Theorem promoteConstraintsRight : forall l r m,
    mergeStates l (promoteConstraints r) m ->
    mergeStates l r m.
Proof.
    admit.
Admitted.

Fixpoint findCell (l : absExp) (s: absState) : option (absState * absState) :=
    match s with
    | AbsStar a b => match findCell l a with
                     | Some (x,y) => Some(x, AbsStar y b)
                     | None => match findCell l b with
                               | Some (x,y) => Some (x, AbsStar a y)
                               | None => None
                               end
                     end
    | (x |-> y) => if beq_absExp l x then Some ((x |-> y),AbsEmpty) else None
    | _ => None
    end.

Fixpoint reverseOr (s : absState) : absState :=
    match s with
    | AbsStar x y => AbsStar (reverseOr x) (reverseOr y)
    | AbsExistsT x => AbsExistsT (reverseOr x)
    | AbsOrStar ([x]) ([y]) => [x \\// y]
    | x => x
    end.

Theorem reverseOrLeft : forall l r m,
    mergeStates (reverseOr l) r m ->
    mergeStates l r m.
Proof.
    admit.
Admitted.

Theorem reverseOrRight : forall l r m,
    mergeStates l (reverseOr r) m ->
    mergeStates l r m.
Proof.
    admit.
Admitted.


























