(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * SatSolverAux1.v
 * This file contains the proof of correctness of a tree traversal algorithm using
 * the PEDANTIC verification framework.
 *
 **********************************************************************************)

Require Import Omega.
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
Require Export UpdateHelper.
Require Export ClosureHelper.
Require Export MagicWandExistsHelper.
Opaque haveVarInvariant.
Opaque basicEval.

Set Printing Depth 200.

Theorem precond1Core :
    (exists st, realizeState
        ([!!(backtrack)] **
         AbsClosure (invariant ** ([#0 <<<< v(2)] *\/* [v(5) ==== #0]))
           (!!(clauses)
            :: !!(assignments_to_do_head)
               :: !!(stack) :: !!(assignments) :: !!(watches) :: nil)) nil
        st) ->
    (exists st, realizeState (AbsMagicWand
        ([!!(backtrack)] **
         AbsClosure (invariant ** ([#0 <<<< v(2)] *\/* [v(5) ==== #0]))
           (!!(clauses)
            :: !!(assignments_to_do_head)
               :: !!(stack) :: !!(assignments) :: !!(watches) :: nil))
        (AbsExistsT
           (AbsExistsT
              (AbsExistsT
                 (AbsExistsT
                    (!!(stack) ++++ #3 |-> v(3) **
                     !!(stack) ++++ #2 |-> v(2) **
                     !!(stack) ++++ #1 |-> v(1) ** !!(stack) |-> v(0)))))))
     nil st).
Proof.
    (*intros. destruct H.
    eapply ex_intro.
    eapply breakTopClosureThm1. unfold invariant. unfold invariantCore.
    unfold invariantCoreNoTail. compute. reflexivity.
    eapply breakTopClosureThm2 in H. Focus 2. unfold invariant. unfold invariantCore.
    unfold invariantCoreNoTail. compute. reflexivity.
    eapply breakTopClosureThm1. compute. reflexivity.
    simplify. propagateExists. propagateExists. propagateExists. propagateExists.
    propagateExists.
    eapply unfold_rs1.
    unfoldHeap (@AbsVar unit eq_unit (@basicEval unit) stack).
    eapply breakTopClosureThm2 in H. Focus 2. compute. reflexivity.
    simplifyHyp H. propagateExistsHyp H. propagateExistsHyp H. propagateExistsHyp H.
    propagateExistsHyp H. propagateExistsHyp H. eapply unfold_rs2 in H. Focus 2.
    unfoldHeap (@AbsVar unit eq_unit (@basicEval unit) stack).
    simplify. simplifyHyp H. simplify. simplifyHyp H.
 

    eapply magicWandStateExists. simpl. reflexivity. eapply ex_intro.
    apply H. simpl. reflexivity. simpl. reflexivity.
    simpl. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsSimp. compute. reflexivity.
    eapply propagateInExistsId. reflexivity.
    compute. reflexivity.

    Grab Existential Variables. apply x.*)
    admit.
Admitted.

Theorem preCond1 : forall x0,
    realizeState
         (AbsUpdateWithLoc
            (AbsUpdateWithLoc
               (AbsUpdateWithLoc
                  (AbsUpdateVar
                     ([!!(backtrack)] **
                      AbsUpdateVar
                        ([#1] **
                         AbsClosure loopInvariant
                           (!!(clauses)
                            :: !!(assignments_to_do_head)
                               :: !!(stack)
                                  :: !!(assignments) :: !!(watches) :: nil))
                        have_var #0) backtrack #0) 
                  varx !!(stack) ++++ #stack_var_offset) 
               valuex !!(stack) ++++ #stack_val_offset) 
            ssss !!(stack) ++++ #next_offset) nil x0 ->
    exists s, realizeState
       (AbsMagicWand
          (AbsUpdateWithLoc
             (AbsUpdateWithLoc
                (AbsUpdateWithLoc
                   (AbsUpdateVar
                      ([!!(backtrack)] **
                       AbsUpdateVar
                         ([#1] **
                          AbsClosure loopInvariant
                            (!!(clauses)
                             :: !!(assignments_to_do_head)
                                :: !!(stack)
                                   :: !!(assignments) :: !!(watches) :: nil))
                         have_var #0) backtrack #0) 
                   varx !!(stack) ++++ #stack_var_offset) 
                valuex !!(stack) ++++ #stack_val_offset) 
             ssss !!(stack) ++++ #next_offset)
          (AbsExistsT
             (AbsExistsT
                (AbsExistsT
                   (AbsExistsT
                      (AbsExistsT
                         (v(0) ++++ #3 |-> v(4) **
                          v(0) ++++ #2 |-> v(3) **
                          v(0) ++++ #1 |-> v(2) **
                          v(0) ++++ #0 |-> v(1) ** [!!(stack) ==== v(0)])))))))
       nil s.
Proof.
    (*intros.
    decomposeUpdates.
    simplifyTheHyp H.
    decomposeUpdates.

    eapply simplifyExists. compute. reflexivity.
    eapply simplifyExists. compute. reflexivity.
    eapply simplifyExists. compute. reflexivity.
    eapply simplifyExists. compute. reflexivity.
    eapply simplifyExists. compute. reflexivity.

    eapply existsWithLoc.
    eapply existsWithLoc.
    eapply existsWithLoc.
    eapply existsVar.
    eapply existsVar.
    eapply precond1Core.
    eapply ex_intro.
    apply H.


Grab Existential Variables.
    apply x4. apply 0. apply x4. apply 0.*)
    admit.
Admitted.

Fixpoint isNat {ev} (v: @Value ev) :=
    match v with
    | NatValue _ => True
    | _ => False
    end.

Inductive ValueType := ListType | NatType | BoolType| AnyType.

Fixpoint expValue {ev} {eq} {f} (vt : ValueType) (ex : @absExp ev eq f) (bindings: list (@Value ev)) (e : env) : @Value ev :=
    match vt with
    | NatType => match ex with
                 | AbsConstVal x => x
                 | AbsVar x => NatValue (e x)
                 | AbsQVar x => nth x (rev bindings) NoValue
                 | AbsFun AbsPlusId (x::y::nil) => match expValue NatType x bindings e,
                                                         expValue NatType y bindings e with
                                                   | NatValue a, NatValue b => NatValue (a+b)
                                                   | _, _ => NoValue
                                                   end
                 | AbsFun AbsMinusId (x::y::nil) => match expValue NatType x bindings e,
                                                          expValue NatType y bindings e with
                                                    | NatValue a, NatValue b => NatValue (a-b)
                                                    | _, _ => NoValue
                                                    end
                 | AbsFun AbsTimesId (x::y::nil) => match expValue ListType x bindings e,
                                                          expValue NatType y bindings e with
                                                    | ListValue a, NatValue b => nth b a NoValue
                                                    | _, _ => NoValue
                                                    end
                 | AbsFun AbsNthId (x::y::nil) => match expValue NatType x bindings e,
                                                          expValue NatType y bindings e with
                                                    | NatValue a, NatValue b => NatValue (a*b)
                                                    | _, _ => NoValue
                                                    end
                 | _ => NoValue
                 end
    | ListType => match ex with
                  | AbsQVar x => nth x (rev bindings) NoValue
                  | _ => NoValue
                  end
    | _ => NoValue
    end.

Fixpoint mergeConditions cond1 cond2 :=
    match cond1, cond2 with
    | None, None => None
    | Some x, None => Some x
    | None, Some x => Some x
    | Some x, Some y => Some (x /\ y)
    end.
Fixpoint expValid {ev} {eq} {f} (vt : ValueType) (ex : @absExp ev eq f) (bindings: list (@Value ev)) (e : env) : option Prop :=
    match vt with
    | NatType => match ex with
                 | AbsConstVal _ => None
                 | AbsVar _ => None
                 | AbsQVar x => match nth x (rev bindings) NoValue with | NatValue _ => None | _ => Some False end
                 | AbsFun AbsPlusId (x::y::nil) => mergeConditions
                                                   (expValid vt x bindings e)
                                                   (expValid vt y bindings e)
                 | AbsFun AbsMinusId (x::y::nil) => mergeConditions
                                                    (expValid vt x bindings e)
                                                    (expValid vt y bindings e)
                 | AbsFun AbsTimesId (x::y::nil) => mergeConditions
                                                    (expValid vt x bindings e)
                                                    (expValid vt y bindings e)
                 | AbsFun AbsIteId (x::y::z::nil) => mergeConditions (mergeConditions
                                                      (expValid vt z bindings e)
                                                      (expValid vt y bindings e))
                                                     (expValid BoolType x bindings e)
                 | _ => Some False
                 end
    | AnyType => match ex with
                 | AbsConstVal _ => None
                 | AbsVar _ => None
                 | AbsQVar x => None
                 | _ => Some False
                 end
    | _ => Some False
    end.

Fixpoint findTree {ev} {eq} {f} {t} {ac} (state : @absState ev eq f t ac) (e: @absExp ev eq f) : option (@absState ev eq f t ac) :=
    match state with
    | AbsUpdateVar s a b => if @hasVarExp ev eq f e a then None else findTree s e
    | AbsUpdateWithLoc s a b => if @hasVarExp ev eq f e a then None else findTree s e
    | AbsStar a b => match findTree a e with
                     | Some x => Some x
                     | None => findTree b e
                     end
    (*| AbsExistsT s => findTree s (N e)*)
    | TREE(root,var,size,p) => if beq_absExp root e then Some (TREE(root,var,size,p)) else None
    | _ => None
    end.

Fixpoint expAssertion {ev} {eq} {f} (ex : @absExp ev eq f) (bindings: list (@Value ev)) (e : env) :=
    match ex with
    | AbsConstVal (NatValue (S _)) => True
    | AbsConstVal _ => False
    | AbsVar v => (e v) > 0
    | AbsQVar n => match nth n (rev bindings) NoValue with
                   | NatValue (S 0) => True
                   | _ => False
                   end
    | AbsFun AbsLessId el => match map (absEval e bindings) el with
                             | (NatValue l::NatValue r::nil) =>  (l < r)
                             | _ => False
                             end
    | AbsFun AbsEqualId el => match map (absEval e bindings) el with
                              | (NatValue l::NatValue r::nil) =>  (l = r)
                              | _ => False
                              end
    | AbsFun AbsNotId (a::nil) => ~ (expAssertion a bindings e)
    | AbsFun AbsAndId (a::b::nil) => (expAssertion a bindings e) /\ (expAssertion b bindings e)
    | AbsFun AbsOrId (a::b::nil) => (expAssertion a bindings e) \/ (expAssertion b bindings e)
    | AbsFun AbsMemberId (a::b::nil) => match expValid NatType a bindings e,expValue NatType a bindings e with
                                        | None,NatValue x => match expValid AnyType b bindings e,expValue ListType b bindings e with
                                                             | None,y => Rmember x y=true
                                                             | Some p,y => p -> Rmember x y=true
                                                             end
                                        | Some q,NatValue x => match expValid AnyType b bindings e,expValue ListType b bindings e with
                                                             | None,y => q -> Rmember x y=true
                                                             | Some p,y => q -> p -> Rmember x y=true
                                                             end
                                        | _,_ => False
                                        end
    | AbsFun f el => match absEval e bindings ex with
                     | NatValue x => (x > 0)
                     | _ => False
                     end
    end.

Fixpoint isField {ev} {eq} {f} (ff : nat) (l : list (@absExp ev eq f)) (bindings : list (@Value ev)) (st : state) :=
    match l with
    | nil => false
    | (h::r) => match expValue NatType h bindings (fst st) with
                      | NatValue q=> if beq_nat q ff then true else isField ff r bindings st
                      | _ => isField ff r bindings st
                      end
    end.

Fixpoint foldAssertions {t} (b : t) (a : list (t -> Prop)) :=
    match a with
    | f::r => (f b) /\ foldAssertions b r
    | nil => True
    end.

Fixpoint extractList {t} (l : @Value t) :=
    match l with
    | ListValue v => v
    | _ => nil
    end.

Fixpoint stateAssertions {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) (st : state) :=
    match s with
    | AbsStar a b => (stateAssertions a st)++(stateAssertions b st)
    | AbsMagicWand a b => (stateAssertions a st)++(stateAssertions b st)
    | AbsOrStar a b => (fun bindings => ((foldAssertions bindings (stateAssertions a st)) \/ (foldAssertions bindings (stateAssertions b st))))::nil
    | AbsUpdateVar s a b => (fun bindings => (match expValid NatType b bindings (fst st),(NatValue (fst st a)=(expValue NatType b bindings (fst st))) with
                            | Some x,y => (x -> y)
                            | None,y => y
                            end))::(fun bindings => (exists vv, (foldAssertions bindings (stateAssertions s (override (fst st) a vv,snd st)))))::nil
    | AbsUpdateWithLoc s l (AbsFun AbsPlusId (aa::bb::nil)) =>
          (fun bindings => (exists vv, (foldAssertions bindings (stateAssertions s (override (fst st) l vv,snd st)))))::
          match findTree s aa with
          | Some (TREE(_,v,s,ff)) => (fun bindings => (expAssertion (AbsFun AbsLessId (bb::s::nil)) bindings (fst st) ->
                                  forall ll vvv bbv, (NatValue ll=expValue NatType (AbsFun AbsPlusId (aa::bb::nil)) bindings (fst st) ->
                                  (ListValue vvv)=expValue ListType v bindings (fst st) ->
                                  NatValue bbv=expValue NatType bb bindings (fst st) ->
                                  isField ll ff bindings st=false ->
                                  (NatValue (fst st l)=(nth (bbv+1) vvv NoValue)))) /\
                                  (expAssertion (AbsFun AbsLessId (bb::s::nil)) bindings (fst st) ->
                                   forall ll vvv qq bbv, (NatValue ll=expValue NatType (AbsFun AbsPlusId (aa::bb::nil)) bindings (fst st) ->
                                  (ListValue vvv)=expValue ListType v bindings (fst st) ->
                                  isField ll ff bindings st=true ->
                                  NatValue bbv=expValue NatType bb bindings (fst st) ->
                                  (ListValue qq=(nth (bbv+1) vvv NoValue)) ->
                                  NatValue (fst st l)=(nth 0 qq NoValue))))
          | _ => (fun bindings => True)
          end::nil
    | AbsExistsT s => (fun bindings => (exists v, (foldAssertions (bindings++(v::nil)) (stateAssertions s st))))::nil
    | AbsAll TreeRecords(v) s => map (fun (x : list Value -> Prop) => (fun bindings => forall vv vl, 
                           expValue ListType v bindings (fst st)=vv->
                           rangeSet vv=ListValue vl ->
                           forall v, (In (NatValue v) vl -> (x (bindings++((NatValue v)::nil)))))) (stateAssertions s st)
    | AbsAll range(#ss,#ee) s =>
                             map (fun (x : list Value -> Prop) => (fun bindings => forall v, (ss<=v -> v < ee -> x (bindings++((NatValue v)::nil))))) (stateAssertions s st)
    | AbsAll range(ss,ee) s => (map (fun (x : list Value -> Prop) => (fun bindings => forall sss eee,
                             expValue NatType ss bindings (fst st)=NatValue sss->
                             expValue NatType ee bindings (fst st)=NatValue eee->
                             forall v, (sss<=v -> v < eee -> x (bindings++((NatValue v)::nil))))) (stateAssertions s st))
    | AbsAll e s => map (fun (x : list Value -> Prop) => (fun bindings => forall vl, absEval (env_p st) bindings e = (ListValue vl) ->
                           forall v, (In v vl -> x (bindings++(v::nil))))) (stateAssertions s st)
    | [x] => (fun bindings => (@expAssertion ev eq f x bindings (fst st)))::nil
    | ARRAY(!!root,#count,v(n)) => (fun bindings => exists h,
                             (match (nth n (rev bindings) NoValue) with
                             | ListValue vl => anyHeapv ((fst st) root) count h vl /\ (forall x v, h x = Some v -> (snd st) x = Some v)
                             | _ => False
                             end))::nil
    | ARRAY(root,count,v) => (fun bindings => (exists r c vv h,
                             NatValue r=expValue NatType root bindings (fst st) ->
                             NatValue c=expValue NatType count bindings (fst st) ->
                             ListValue vv=expValue ListType v bindings (fst st) ->
                             anyHeapv r c h vv))::nil
    | TREE(!!root,v(x),#count,(#next::nil)) =>
                                     (fun bindings => (exists h,
                                         Tree (fst st root) count (next::nil)
                                              (nth x (rev bindings) NoValue) h))::nil
    | TREE(root,v,count,children) => (fun bindings => (forall c vr childrenr rootr countr, exists h,
                                     childrenr = map (fun cc => expValue NatType cc bindings (fst st)) children ->
                                     vr = expValue ListType v bindings (fst st) ->
                                     NatValue countr = expValue NatType count bindings (fst st) ->
                                     NatValue rootr = expValue NatType root bindings (fst st) ->
                                     strip_nat_values childrenr c -> Tree rootr countr c vr h))::nil
                                     
    | _ => (fun x => True)::nil
    end.

Theorem stateAssertionThm: forall ev eq f t ac st b s,
    @realizeState ev eq f t ac st b s -> foldAssertions b (@stateAssertions ev eq f t ac st s).
Proof.
    admit.
Admitted.

Theorem heapMap : forall t base size h l, @anyHeapv t base size h l -> (forall i, (i < size -> exists nv, (h (base+i)=Some nv /\ nth (i+1) l NoValue=NatValue nv))).
Proof.
    admit.
Admitted.

Theorem glue1 : forall (s : state), (let (x, _) := s in x)=env_p s.
Proof.
    admit.
Admitted.

Theorem glue2 : forall (s : state), (let (_, x) := s in x)=heap_p s.
Proof.
    admit.
Admitted.

Ltac decomposeStep := match goal with
     | [ H: match ?Q with NatValue _ => _ | ListValue _ => False | NoValue => False | OtherValue _ => False end |- _ ] => remember Q; destruct Q
     | [ H: match ?Q with NatValue _ => False | ListValue _ => _ | NoValue => False | OtherValue _ => False end |- _ ] => remember Q; destruct Q
     | [ Q: False |- _ ] => inversion Q
     end.

Opaque numericRange.
Opaque rangeSet.
Opaque Rmember.
Opaque In.
Opaque nth.

Theorem dumb1: forall x, x + 2 = S (S x).
Proof.
    admit.
Admitted.

Theorem dumb2: forall x, x + 2 + 1 = x + 3.
Proof.
    admit.
Admitted.

Theorem rangeSetIsList {ev} : forall a b c d e, @Tree ev a b c d e -> exists v, @ListValue ev v=rangeSet d.
Proof.
    admit.
Admitted.

Theorem rootInTree {ev} : forall a b c d e f, @Tree ev a b c d e -> @ListValue ev f = rangeSet d -> In (NatValue a) f.
Proof. admit. Admitted.

Theorem rootIsRecord {ev}: forall a b c d e, @Tree ev a b c d e -> extractList d = findRecord a d.
Proof. admit. Admitted.

Theorem dumb3 : forall x n, S x <= n -> x < n. Proof. admit. Admitted.


Theorem preCond2: forall (s : state) (n : nat) (b : id -> nat), realizeState
    (AbsUpdateVar
       (AbsUpdateVar
          (AbsMagicWand
             (AbsUpdateWithLoc
                (AbsUpdateWithLoc
                   (AbsUpdateWithLoc
                      (AbsUpdateVar
                         ([!!(backtrack)] **
                          AbsUpdateVar
                            ([#1] **
                             AbsClosure loopInvariant
                               (!!(clauses)
                                :: !!(assignments_to_do_head)
                                   :: !!(stack)
                                      :: !!(assignments)
                                         :: !!(watches) :: !!(backtrack) :: nil)) 
                            have_var #0) backtrack 
                         #0) varx !!(stack) ++++ #stack_var_offset) 
                   valuex !!(stack) ++++ #stack_val_offset) 
                ssss !!(stack) ++++ #next_offset)
             (AbsExistsT
                (AbsExistsT
                   (AbsExistsT
                      (AbsExistsT
                         (AbsExistsT
                            (v(0) ++++ #3 |-> v(4) **
                             v(0) ++++ #2 |-> v(3) **
                             v(0) ++++ #1 |-> v(2) **
                             v(0) ++++ #0 |-> v(1) ** [!!(stack) ==== v(0)])))))))
          stack !!(ssss)) have_var #1)
           nil s -> NatValue n =
       basicEval AbsPlusId
         (NatValue (env_p s assignments) :: @NatValue unit (env_p s varx) :: nil) -> heap_p s n <> None.
Proof.
    intros. eapply breakTopClosureThm2 in H. Focus 2. unfold loopInvariant. unfold invariant.
    unfold invariantCore. unfold invariantCoreNoTail. compute. reflexivity.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    
    eapply breakTopClosureThm2 in H. Focus 2. compute. reflexivity.
    eapply propagateExistsEquiv1 in H. Focus 2. compute. reflexivity.
    eapply propagateExistsEquiv1 in H. Focus 2. compute. reflexivity.
    eapply propagateExistsEquiv1 in H. Focus 2. compute. reflexivity.
    eapply propagateExistsEquiv1 in H. Focus 2. compute. reflexivity.
    eapply propagateExistsEquiv1 in H. Focus 2. compute. reflexivity.

    eapply unfold_rs2 in H. Focus 2.
    unfoldHeap (@AbsVar unit eq_unit (@basicEval unit) stack).
    Transparent nth.
    simplifyTheHyp H.

    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.
    eapply localizeExistsThm2 in H. Focus 2. compute. reflexivity.

    eapply clearMagicWandUpdateWithLocThm in H. Focus 2. compute. reflexivity.
    eapply removeMagicWandThm in H. Focus 2. compute. reflexivity.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.
    simplifyTheHyp H.

    eapply stateAssertionThm in H. compute in H.
    crunch. 

    destruct x3. eapply dumb3 in H27. Transparent basicEval. simpl in H0.
    inversion H0; subst; clear H0. rewrite <- glue1.
    destruct x0. inversion H26. inversion H26; subst; clear H26.

    assert (exists nv, (x14 (((let (x, _) := s in x) assignments)+((let (x, _) := s in x) varx)) = Some nv /\ nth (((let (x, _) := s in x) varx)+1) l NoValue = NatValue nv)).

        eapply heapMap. apply H0. inversion H13; subst; clear H13. apply H27.

    inversion H3; subst; clear H3.

    assert(exists x, heap_p s ((let (x3, _) := s in x3) assignments + (let (x3, _) := s in x3) varx)=Some x).
        eapply ex_intro. eapply H2. eapply H4.

    inversion H3; subst; clear H3.

    rewrite H5. intro X. inversion X.

    inversion H26. inversion H26.

    inversion H27. inversion H27. inversion H27.

    clear H.
    compute. intros.
    eapply stateAssertionThm in H. compute in H. crunch.

    remember ((let (x4, _) := s0 in x4) stack). destruct n0. inversion H15.
   
    eapply ex_intro. simpl. reflexivity.


Qed.

Opaque basicEval.

Theorem mergeTheorem1 : mergeStates
     (AbsUpdateVar
        (AbsUpdateVar
           ([!!(ssss) ==== #0] **
            AbsUpdateWithLoc ([~~ #3 <<<< !!(iiii)] ** haveVarInvariant) 
              ssss !!(assignments) ++++ !!(iiii)) varx 
           !!(iiii)) have_var #1)
     ([~~ !!(ssss) ==== #0] **
      AbsUpdateWithLoc ([~~ #3 <<<< !!(iiii)] ** haveVarInvariant) 
        ssss !!(assignments) ++++ !!(iiii)) haveVarInvariant.
Proof.
    admit.
Admitted.


Theorem noResult1 : forall x0 st st' f,
        ceval f st
        (CIf (!ssss === A0) (varx ::= !iiii; have_var ::= A1) (SKIP))
        st' x0 -> x0 = NoResult.
Proof.
    (*intros x0 st st' f H.*)
 admit.
Admitted.


Theorem entailment1 : forall s : state,
   realizeState (AbsUpdateVar haveVarInvariant iiii !!(iiii) ++++ #1) nil s ->
   realizeState haveVarInvariant nil s.
Proof.
    admit.
Admitted.


Theorem entailment2 : forall x0 : state,
   realizeState
     (AbsUpdateVar
        (AbsUpdateVar
           ([~~ !!(backtrack)] **
            AbsUpdateVar ([#1] ** invariant) have_var #0) 
           valuex #1) iiii #0) nil x0 -> realizeState haveVarInvariant nil x0.
Proof.
    admit.
Admitted.


Theorem mergeTheorem2 : mergeStates
     (AbsUpdateLoc
        (AbsUpdateVar
           (AbsUpdateVar
              (AbsMagicWand
                 (AbsUpdateWithLoc
                    (AbsUpdateWithLoc
                       (AbsUpdateWithLoc
                          (AbsUpdateVar
                             ([!!(backtrack)] **
                              AbsUpdateVar ([#1] ** invariant) have_var #0)
                             backtrack #0) varx
                          !!(stack) ++++ #stack_var_offset) 
                       valuex !!(stack) ++++ #stack_val_offset) 
                    ssss !!(stack) ++++ #next_offset)
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (AbsExistsT
                                (v(0) ++++ #3 |-> v(4) **
                                 v(0) ++++ #2 |-> v(3) **
                                 v(0) ++++ #1 |-> v(2) **
                                 v(0) ++++ #0 |-> v(1) **
                                 [!!(stack) ==== v(0)]))))))) 
              stack !!(ssss)) have_var #1) !!(assignments) ++++ !!(varx) 
        #0)
     (match NoResult with
      | NoResult => [~~ (convertToAbsExp (!iiii <<= A3))]
      | Return _ => AbsEmpty
      | Exception _ _ => AbsEmpty
      end ** haveVarInvariant) invariant.
Proof.
    admit.
Admitted.




Theorem validRefTheorem1 : forall s n b, id -> nat -> realizeState
        (AbsExistsT
           (AbsExistsT
              (AbsExistsT
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (v(0) ++++ #4 |-> v(5) **
                           v(0) ++++ #3 |-> v(4) **
                           v(0) ++++ #2 |-> v(3) **
                           v(0) ++++ #1 |-> v(2) **
                           v(0) ++++ #0 |-> v(1) **
                           [!!(todo) ==== v(0)] **
                           AbsExistsT
                             ([~~ !!(have_var) ==== #0] **
                              pushAbsVarState
                                (pushAbsVarState
                                   (pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (quantifyAbsVarState invariant
                                                  todo)))))))))))))) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b todo) :: @NatValue unit next_offset :: nil) -> heap_p s n <> None.
Proof.
 admit.
Admitted.


Theorem validRefTheorem2 : forall s n b, id -> nat -> realizeState
        (AbsUpdateLoc
           (AbsExistsT
              (AbsExistsT
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (v(0) ++++ #4 |-> v(5) **
                              v(0) ++++ #3 |-> v(4) **
                              v(0) ++++ #2 |-> v(3) **
                              v(0) ++++ #1 |-> v(2) **
                              v(0) ++++ #0 |-> v(1) **
                              [!!(todo) ==== v(0)] **
                              AbsExistsT
                                ([~~ !!(have_var) ==== #0] **
                                 pushAbsVarState
                                   (pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  invariant 
                                                  todo))))))))))))))
           !!(todo) ++++ #next_offset !!(assignments_to_do_head)) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b todo) :: @NatValue unit prev_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem validRefTheorem3 : forall s n b, id -> nat -> realizeState
        ([~~ !!(assignments_to_do_tail) ==== #0] **
         AbsUpdateLoc
           (AbsUpdateLoc
              (AbsExistsT
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (AbsExistsT
                                (v(0) ++++ #4 |-> v(5) **
                                 v(0) ++++ #3 |-> v(4) **
                                 v(0) ++++ #2 |-> v(3) **
                                 v(0) ++++ #1 |-> v(2) **
                                 v(0) ++++ #0 |-> v(1) **
                                 [!!(todo) ==== v(0)] **
                                 AbsExistsT
                                   ([~~ !!(have_var) ==== #0] **
                                    pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  invariant 
                                                  todo))))))))))))))
              !!(todo) ++++ #next_offset !!(assignments_to_do_head))
           !!(todo) ++++ #prev_offset #0) nil s -> NatValue n =
       basicEval assignments_to_do_head
         (NatValue (b assignments_to_do_head) :: @NatValue unit prev_offset :: nil) -> heap_p s n <> None.
Proof.
    admit.
Admitted.


Theorem mergeTheorem3 : mergeStates
     (AbsUpdateVar
        ([!!(assignments_to_do_tail) ==== #0] **
         AbsUpdateLoc
           (AbsUpdateLoc
              (AbsExistsT
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (AbsExistsT
                                (v(0) ++++ #4 |-> v(5) **
                                 v(0) ++++ #3 |-> v(4) **
                                 v(0) ++++ #2 |-> v(3) **
                                 v(0) ++++ #1 |-> v(2) **
                                 v(0) ++++ #0 |-> v(1) **
                                 [!!(todo) ==== v(0)] **
                                 AbsExistsT
                                   ([~~ !!(have_var) ==== #0] **
                                    pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  invariant 
                                                  todo))))))))))))))
              !!(todo) ++++ #next_offset !!(assignments_to_do_head))
           !!(todo) ++++ #prev_offset #0) assignments_to_do_tail 
        !!(todo))
     (AbsUpdateLoc
        ([~~ !!(assignments_to_do_tail) ==== #0] **
         AbsUpdateLoc
           (AbsUpdateLoc
              (AbsExistsT
                 (AbsExistsT
                    (AbsExistsT
                       (AbsExistsT
                          (AbsExistsT
                             (AbsExistsT
                                (v(0) ++++ #4 |-> v(5) **
                                 v(0) ++++ #3 |-> v(4) **
                                 v(0) ++++ #2 |-> v(3) **
                                 v(0) ++++ #1 |-> v(2) **
                                 v(0) ++++ #0 |-> v(1) **
                                 [!!(todo) ==== v(0)] **
                                 AbsExistsT
                                   ([~~ !!(have_var) ==== #0] **
                                    pushAbsVarState
                                      (pushAbsVarState
                                         (pushAbsVarState
                                            (pushAbsVarState
                                               (pushAbsVarState
                                                  (pushAbsVarState
                                                  (quantifyAbsVarState
                                                  invariant 
                                                  todo))))))))))))))
              !!(todo) ++++ #next_offset !!(assignments_to_do_head))
           !!(todo) ++++ #prev_offset #0)
        !!(assignments_to_do_head) ++++ #prev_offset 
        !!(todo)) invariant.
Proof.
    admit.
Admitted.























































































































































































































