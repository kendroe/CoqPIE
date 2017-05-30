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
Require Export UpdateHelper.
Require Export ClosureHelper.
Require Export MagicWandExistsHelper.

Set Printing Depth 200.

Fixpoint isNat (v: @Value unit) :=
    match v with
    | NatValue _ => True
    | _ => False
    end.

Inductive ValueType := ListType | NatType | BoolType| AnyType.

Fixpoint expValue (vt : ValueType) (ex : absExp) (bindings: list (@Value unit)) (e : env) : @Value unit :=
    match vt with
    | NatType => match ex with
                 | AbsConstVal x => x
                 | AbsVar x => NatValue (e x)
                 | AbsQVar x => nth x bindings NoValue
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
                  | AbsQVar x => nth x bindings NoValue
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
Fixpoint expValid (vt : ValueType) (ex : absExp) (bindings: list (@Value unit)) (e : env) : option Prop :=
    match vt with
    | NatType => match ex with
                 | AbsConstVal _ => None
                 | AbsVar _ => None
                 | AbsQVar x => match nth x bindings NoValue with | NatValue _ => None | _ => Some False end
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

Fixpoint findTree (state : absState) (e: absExp) : option (absState) :=
    match state with
    | AbsUpdateVar s a b => if hasVarExp e a then None else findTree s e
    | AbsUpdateWithLoc s a b => if hasVarExp e a then None else findTree s e
    | AbsStar a b => match findTree a e with
                     | Some x => Some x
                     | None => findTree b e
                     end
    (*| AbsExistsT s => findTree s (N e)*)
    | TREE(root,var,size,p) => if beq_absExp root e then Some (TREE(root,var,size,p)) else None
    | ARRAY(root,a,b) => if beq_absExp root e then Some (ARRAY(root,a,b)) else None
    | _ => None
    end.

Fixpoint expAssertion (ex : absExp) (bindings: list (@Value unit)) (e : env) :=
    match ex with
    | AbsConstVal (NatValue (S _)) => True
    | AbsConstVal _ => False
    | AbsVar v => (e v) > 0
    | AbsQVar n => match nth n bindings NoValue with
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

Fixpoint isField  (ff : nat) (l : list absExp) (bindings : list (@Value unit)) (st : state) :=
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

Fixpoint stateAssertions (s : absState) (st : state) :=
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
          | Some (ARRAY(_,s,v)) => (fun bindings => (expAssertion (AbsFun AbsLessId (bb::s::nil)) bindings (fst st) ->
                                  forall ll vvv bbv, (NatValue ll=expValue NatType (AbsFun AbsPlusId (aa::bb::nil)) bindings (fst st) ->
                                  (ListValue vvv)=expValue ListType v bindings (fst st) ->
                                  NatValue bbv=expValue NatType bb bindings (fst st) ->
                                  (NatValue (fst st l)=(nth (bbv+1) vvv NoValue)))))
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
    | AbsExistsT s => (fun bindings => (exists v, (foldAssertions (v::bindings) (stateAssertions s st))))::nil
    | AbsAll TreeRecords(v) s => map (fun (x : list Value -> Prop) => (fun bindings => forall vv vl, 
                           expValue ListType v bindings (fst st)=vv->
                           rangeSet vv=ListValue vl ->
                           forall v, (In (NatValue v) vl -> (x ((NatValue v)::bindings))))) (stateAssertions s st)
    | AbsAll range(#ss,#ee) s =>
                             map (fun (x : list Value -> Prop) => (fun bindings => forall v, (ss<=v -> v < ee -> x ((NatValue v)::bindings)))) (stateAssertions s st)
    | AbsAll range(ss,ee) s => (map (fun (x : list Value -> Prop) => (fun bindings => forall sss eee,
                             expValue NatType ss bindings (fst st)=NatValue sss->
                             expValue NatType ee bindings (fst st)=NatValue eee->
                             forall v, (sss<=v -> v < eee -> x (bindings++((NatValue v)::nil))))) (stateAssertions s st))
    | AbsAll e s => map (fun (x : list Value -> Prop) => (fun bindings => forall vl, absEval (env_p st) bindings e = (ListValue vl) ->
                           forall v, (In v vl -> x (v::bindings)))) (stateAssertions s st)
    | [x] => (fun bindings => (expAssertion x bindings (fst st)))::nil
    | ARRAY(!!root,#count,v(n)) => (fun bindings => exists h,
                             (match (nth n bindings NoValue) with
                             | ListValue vl => anyHeapv ((fst st) root) count h vl /\ (forall x v, h x = Some v -> (snd st) x = Some v)
                             | _ => False
                             end))::nil
    | ARRAY(root,count,v) => (fun bindings => (exists r c vv h,
                             NatValue r=expValue NatType root bindings (fst st) ->
                             NatValue c=expValue NatType count bindings (fst st) ->
                             ListValue vv=expValue ListType v bindings (fst st) ->
                             anyHeapv r c h vv))::nil
    | (x |-> y) => (fun bindings => (exists xx, NatValue xx = expValue NatType x bindings (fst st)) /\
                                    (exists yy, NatValue yy = expValue NatType y bindings (fst st)) /\
                                    (forall xx yy,
                                     NatValue xx = expValue NatType x bindings (fst st) ->
                                     NatValue yy = expValue NatType y bindings (fst st) ->
                                     (xx > 0 /\ (snd st xx)=Some yy)))::nil
    | TREE(!!root,v(x),#count,(#next::nil)) =>
                                     (fun bindings => (exists h,
                                         Tree (fst st root) count (next::nil)
                                              (nth x bindings NoValue) h /\ (forall x v, h x = Some v -> (snd st) x = Some v)))::nil
    | TREE(root,v,count,children) => (fun bindings => (forall c vr childrenr rootr countr, exists h,
                                     childrenr = map (fun cc => expValue NatType cc bindings (fst st)) children ->
                                     vr = expValue ListType v bindings (fst st) ->
                                     NatValue countr = expValue NatType count bindings (fst st) ->
                                     NatValue rootr = expValue NatType root bindings (fst st) ->
                                     strip_nat_values childrenr c -> Tree rootr countr c vr h))::nil
                                     
    | _ => (fun x => True)::nil
    end.

Theorem stateAssertionThm: forall st b s,
    realizeState st b s -> foldAssertions b (stateAssertions st s).
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

Theorem rangeSetIsList : forall a b c d e, @Tree unit a b c d e -> exists v, @ListValue unit v=rangeSet d.
Proof.
    admit.
Admitted.

Theorem rootInTree : forall a b c d e f, @Tree unit a b c d e -> @ListValue unit f = rangeSet d -> In (NatValue a) f.
Proof. admit. Admitted.

Theorem rootIsRecord: forall a b c d e, @Tree unit a b c d e -> extractList d = findRecord a d.
Proof. admit. Admitted.



















