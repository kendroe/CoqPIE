(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * AbsStateInstance.v
 * This file contains definitions needed to instantiate the abstract state.
 *
 * Key definitions:
 *    basicEval (used to fill in f parameter of absExp)
 *    basicState (used to fill in the t parameter of absState)
 *    convertToAbsExp (used by forward propagation tactic proofs)
 *    supportsBasicFunctionality - instantiation of supportsFunctionality
 *    absStateBasic - instantiated version of absState with the above
 *
 * This file also contains much of the notation used for display abstract states.
 * There are a few pieces in absState.v
 *
 **********************************************************************************)

Require Export SfLib.
Require Export SfLibExtras.
Require Export ImpHeap.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export AbsState.

(**********************************************************************************
 *
 * Recursive heap declarations
 *
 *
 * This section contains the declarations to build up the definition of Tree
 * which represent the recursively defined heap elements such as trees and linked
 * lists.
 **********************************************************************************)

Inductive anyHeap : nat -> nat -> heap -> Prop :=
    | AnyHeapBase : forall start,
                    anyHeap start 0 (fun x => None)
    | AnyHeapNext : forall start next heap y,
                    anyHeap (S start) next heap ->
                    anyHeap start (S next) (fun x => if beq_nat x start then Some y else heap x).

Inductive Rcell : nat -> (list nat) -> heap -> nat -> Prop :=
  | RCellBase : forall l ll h,
                Rcell l ll h l
  | RCellNext : forall l ll index h n nn,
                mem_nat index ll=true ->
                h (n+index)=Some nn ->
                Rcell l ll h n ->
                Rcell l ll h nn.

Inductive mergeHeaps : (list heap) -> heap -> Prop :=
  | MHBase : mergeHeaps nil (fun x => None)
  | MHNext : forall f r h1 h2 h,
             mergeHeaps r h2 ->
             (forall x, h1 x=None \/ h2 x=None) ->
             h = (fun x => match h1 x with None => h2 x | Some x => Some x end) ->
             mergeHeaps (f::r) h.

Inductive heapWithIndexList {t} : (list nat) -> (list heap) -> (list (@Value t)) -> (list (nat * heap * (@Value t))) -> Prop :=
  | HWIBase : heapWithIndexList nil nil nil nil
  | HWINext : forall ir hr ihr br i h b,
              heapWithIndexList ir hr br ihr ->
              heapWithIndexList (i::ir) (h::hr) (b::br) ((i,h,b)::ihr).

Fixpoint findIndex {t} (n : nat) (h : heap) (l : list (nat * heap * (@Value t))) : @Value t :=
    match l with
    | nil => match h n with
             | Some x => NatValue x
             | None => NatValue 0
             end
    | ((nn,hh,v)::r) => if beq_nat n nn then v else findIndex n h r
    end.

Fixpoint buildList {t} (i : nat) (size : nat) (h : heap) (l : list (nat * heap * (@Value t))) : list (@Value t) :=
    match size with
    | 0 => nil
    | (S s) => (findIndex i h l)::(buildList (S i) s h l)
    end.

Inductive ihmem {t} : nat -> heap -> @Value t -> (list (nat * heap * (@Value t))) -> Prop :=
  | IHBase : forall n h v hl,
             ihmem n h v ((n,h,v)::hl)
  | IHNext : forall n h v f hl,
             ihmem n h v hl ->
             ihmem n h v (f::hl).

(*
 * Recursive definition for the TREE construct--used in the definition of basicState
 *
 * Parameters:
 *    #1 - root of tree
 *    #2 - size of each node in the tree
 *    #3 - list of offsets to fields for each node
 *    #4 - functional representation of the tree
 *    #5 - concrete heap (Must be exact heap for the tree)
 *)
Inductive Tree {t} : nat -> nat -> (list nat) -> (@Value t) -> heap -> Prop :=
  | TreeNext : forall root size indices heaps ihlist h0 h1 heap values vals,
            size > 0 ->
            anyHeap root size h0 ->
            heapWithIndexList indices heaps values ihlist ->
            not(root=0) ->
            (forall i h v x, ihmem i h v ihlist -> Some x=h0 (root+x) -> Tree x size indices v h) ->
            mergeHeaps heaps h1 ->
            (forall l, (h1 l=None \/ h0 l=None)) ->
            heap = (fun x => match h1 x with None =>  h0 x | Some x => Some x end) ->
            vals = buildList root size heap ihlist ->
            Tree root size indices (ListValue ((NatValue root)::vals)) heap
  | TreeBase : forall size index h,
            size > 0 ->
            (forall v, h v=None) ->
            Tree 0 size index (ListValue ((NatValue 0)::nil)) h.

Fixpoint flatten {t} (v : @Value t) (loc : nat) : list ((@Value t) * nat) :=
    match v with
    | (ListValue ((NatValue loc)::ll)) =>
        (v,loc)::((fix go (x : list (@Value t)) l :=
             match x with
             | (f::r) => (flatten f l)++(go r (l+1))
             | _ => nil
             end) ll loc)
    | x => (v,loc)::nil
    end.

Fixpoint rmemberFullList {t} (n : nat) (v : (list ((@Value t) * nat))) : bool :=
    match v with
    | ((val,loc)::r) => if beq_nat loc n then true else rmemberFullList n r
    | _ => false
    end.

Fixpoint rmemberList {t} (n : nat) (v : (list ((@Value t) * nat))) : bool :=
    match v with
    | ((ListValue ((NatValue xx)::ll),loc)::r) => if beq_nat loc n then true else rmemberList n r
    | (_::r) => rmemberList n r
    | _ => false
    end.

(*
 * Rmember is a predicate used in AbsPredicate constructs to determine whether a nat
 * is in fact a pointer to the head of any of the nodes in the list or tree represented
 * by an RFun construct.
 *
 * Parameters:
 *    l - location to test
 *    tree - a tree (which is the same form as parameter #4 to tree above
 *
 * This definition is used in basicEval for the 'inTree' function
 *)
Definition Rmember {t} (l : nat) (tree : @Value t) : bool :=
    rmemberList l (flatten tree 0).

(*Theorem rootIsMember : forall root size fields heap,
    root <> 0 ->
    R root size fields heap ->
    Rmember root root fields heap.
Proof. adxxmit. Qed.*)

(*
 * Rinclude is the same as Rmember except that it tests whether the location is a pointer to
 * any cell within a node rather than just the first.  It is used for 'inTreeLoc' defined in
 * basicEval
 *
 * Parameters:
 *    l - location to test
 *    tree - a tree (which is the same form as parameter #4 to tree above
 *)
Definition Rinclude {t} (l : nat) (tree : @Value t) : bool :=
    rmemberFullList l (flatten tree 0).

Inductive strip_nat_values {t} : (list (@Value t)) -> (list nat) -> Prop :=
   | SNVNil : strip_nat_values nil nil
   | SNVCons : forall v a b,
               strip_nat_values a b ->
               strip_nat_values ((NatValue v)::a) (v::b).

Ltac simplifyStripNatValues :=
    match goal with
    | [ |- strip_nat_values _ nil] => apply SNVNil
    | [ |- strip_nat_values nil _] => apply SNVNil
    | [ |- strip_nat_values _ (_::_)] => (apply SNVCons);try simplifyStripNatValues
    | [ |- strip_nat_values (_::_) _] => (apply SNVCons);try simplifyStripNatValues
    end.

(*Hint Immediate SNVNil.*)
Hint Constructors strip_nat_values.

Fixpoint findRecord {t} (l : nat) (v : @Value t) :=
    match v with
    | (ListValue ((NatValue x)::r)) =>
                 if beq_nat x l then
                     (ListValue ((NatValue x)::r))
                 else (fix go ll :=
                          match ll with
                          | nil => NoValue
                          | (f::r) => match findRecord l f with
                                      | NoValue => go r
                                      | x => x
                                      end
                          end) r
    | _ => NoValue
    end.

Inductive valueIndexList {t} : (list nat) -> (list (@Value t)) -> (list (nat * (@Value t))) -> Prop :=
  | VIBase : valueIndexList nil nil nil
  | VINext : forall ir br i b ibr,
              valueIndexList ir br ibr ->
              valueIndexList (i::ir) (b::br) ((i,b)::ibr).

Inductive imem {t} : nat -> @Value t -> (list (nat * (@Value t))) -> Prop :=
  | IBase : forall n v hl,
            imem n v ((n,v)::hl)
  | INext : forall n v f hl,
            imem n v hl ->
            imem n v (f::hl).

Inductive updateRec {t} : (list (nat * (@Value t))) -> nat -> list (@Value t) -> list (@Value t) -> Prop :=
  | UBase : forall n vl,
            updateRec vl n nil nil
  | UMem : forall n v vl or nr x,
           imem n v vl ->
           updateRec vl (n+1) or nr ->
           updateRec vl n (x::or) (v::nr)
  | UDef1 : forall n v vl or nr x,
            not(imem n v vl) ->
            updateRec vl (n+1) or nr ->
            updateRec vl n ((NatValue x)::or) ((NatValue x)::or)
  | UDef2 : forall n v vl or nr x rr,
            not(imem n v vl) ->
            updateRec vl (n+1) or nr ->
            updateRec vl n ((ListValue ((NatValue x)::rr))::or) ((NatValue x)::or).

Inductive Path {t} : nat -> nat -> (list nat) -> (@Value t) -> (@Value t) -> Prop :=
  | PathNext : forall root size indices baseData rec vals ivals rec2,
            size > 0 ->
            not(root=0) ->
            (ListValue ((NatValue root)::rec)) = findRecord root baseData ->
            valueIndexList indices vals ivals ->
            (forall i x v r, imem i v ivals -> ((ListValue ((NatValue x)::r))=nth i rec NoValue /\ Path x size indices baseData v)) ->
            updateRec ivals 0 rec rec2 ->
            Path root size indices baseData (ListValue (NatValue root::rec2))
  | PathBase : forall size l h,
            size > 0 ->
            Path 0 size l h (ListValue ((NatValue 0)::nil)).

Fixpoint rangeSet {t} (v : @Value t) : @Value t :=
  match v with
  | (ListValue (NatValue loc::r)) =>
            (fix go (x : (list (@Value t))) :=
                    match x with
                    | (f::l) => match (rangeSet f,go l) with
                                | ((ListValue l),(ListValue y)) => (ListValue (l++y))
                                | _ => NoValue
                                end
                    | _ => (ListValue nil)
                    end) r
  | (NatValue _) => (ListValue nil)
  | _ => NoValue
  end.

Fixpoint numericRange {t} (s : nat) (e : nat) : @Value t :=
    if beq_nat s e then (ListValue nil)
    else match e with
         | 0 => (ListValue (nil))
         | (S e') => match numericRange s e' with
                     (ListValue l) => (ListValue (l++((NatValue e')::nil)))
                     | _ => NoValue
                     end
         end.

Fixpoint replacenth {t} (l : list t) (n : nat) (e : t) :=
    match l,n with
    | (f::r),0 => (e::r)
    | (f::r),(S n1) => (f::(replacenth r n1 e))
    | l,_ => l
    end.

(***************************************************************************
 *
 * basicEval
 *
 * This is used to fill in the 'f' parameter in absExp.
 *
 ***************************************************************************)

Notation "'AbsNthId'" := (Id 1) (at level 1).
Notation "'AbsPlusId'" := (Id 2) (at level 1).
Notation "'AbsMinusId'" := (Id 3) (at level 1).
Notation "'AbsTimesId'" := (Id 4) (at level 1).
Notation "'AbsEqualId'" := (Id 5) (at level 1).
Notation "'AbsLessId'" := (Id 6) (at level 1).
Notation "'AbsMemberId'" := (Id 7) (at level 1).
Notation "'AbsIncludeId'" := (Id 8) (at level 1).
Notation "'AbsImplyId'" := (Id 9) (at level 1).
Notation "'AbsNotId'" := (Id 10) (at level 1).
Notation "'AbsAndId'" := (Id 11) (at level 1).
Notation "'AbsOrId'" := (Id 12) (at level 1).
Notation "'AbsIteId'" := (Id 13) (at level 1).
Notation "'AbsFindId'" := (Id 14) (at level 1).
Notation "'AbsListId'" := (Id 15) (at level 1).
Notation "'AbsRangeSetId'" := (Id 16) (at level 1).
Notation "'AbsRangeNumericId'" := (Id 17) (at level 1).
Notation "'AbsReplaceNthId'" := (Id 18) (at level 1).

Fixpoint basicEval {t} (op : id) (args : list (@Value t)) : @Value t :=
    match (op,args) with
    | (AbsNthId,((ListValue l)::(NatValue f)::nil)) => nth f l NoValue
    | (AbsPlusId,((NatValue l)::(NatValue r)::nil)) => (NatValue (l+r))
    | (AbsMinusId,((NatValue l)::(NatValue r)::nil)) => (NatValue (l-r))
    | (AbsTimesId,((NatValue l)::(NatValue r)::nil)) => (NatValue (l*r))
    | (AbsEqualId,((NatValue l)::(NatValue r)::nil)) => if beq_nat l r then (NatValue 1) else (NatValue 0)
    | (AbsLessId,((NatValue l)::(NatValue r)::nil)) => if ble_nat r l then (NatValue 0) else (NatValue 1)
    | (AbsMemberId,((NatValue l)::tree::nil)) => if Rmember l tree then (NatValue 1) else (NatValue 0)
    | (AbsIncludeId,((NatValue l)::tree::nil)) => if Rinclude l tree then (NatValue 1) else (NatValue 0)
    | (AbsImplyId,((NatValue l)::r::nil)) => if beq_nat l 0 then NatValue 1 else r
    | (AbsNotId,((NatValue l)::nil)) => if beq_nat l 0 then NatValue 1 else NatValue 0
    | (AbsAndId,((NatValue l)::r::nil)) => if beq_nat l 0 then NatValue 0 else r
    | (AbsOrId,((NatValue l)::r::nil)) => if beq_nat l 0 then r else (NatValue l)
    | (AbsIteId,((NatValue c)::t::e::nil)) => if beq_nat c 0 then e else t
    | (AbsFindId,(v::(NatValue x)::nil)) => @findRecord t x v
    | (AbsListId,l) => @ListValue t l
    | (AbsRangeSetId,(f::nil)) => rangeSet f
    | (AbsRangeNumericId,((NatValue s)::(NatValue e)::nil)) => numericRange s e
    | (AbsReplaceNthId,((ListValue l)::(NatValue n)::e::nil)) => (ListValue (replacenth l n e))
    | _ => NoValue
    end.

(* This function is used in absExecute in defining (and proving) many tactics *)
Fixpoint convertToAbsExp {ev} {eq} {f} (e : aexp) : @absExp ev eq f :=
  match e with
  | ANum v => AbsConstVal (NatValue v)
  | AVar id => AbsVar id
  | APlus l r => AbsFun (Id 2) ((convertToAbsExp l)::(convertToAbsExp r)::nil)
  | AMinus l r => AbsFun (Id 3) ((convertToAbsExp l)::(convertToAbsExp r)::nil)
  | AMult l r => AbsFun (Id 4) ((convertToAbsExp l)::(convertToAbsExp r)::nil)
  | AEq l r => AbsFun (Id 5) ((convertToAbsExp l)::(convertToAbsExp r)::nil)
  | ALe l r => AbsFun (Id 10) ((AbsFun (Id 6) ((convertToAbsExp r)::(convertToAbsExp l)::nil))::nil)
  | ALand l r => AbsFun (Id 11) ((convertToAbsExp l)::(convertToAbsExp r)::nil)
  | ALor l r => AbsFun (Id 12) ((convertToAbsExp l)::(convertToAbsExp r)::nil)
  | ALnot t => AbsFun (Id 10) ((convertToAbsExp t)::nil)
  end.

(***************************************************************************
 *
 * basicState
 *
 * This is used to fill in the 't' parameter in absState.
 *
 ***************************************************************************)

Notation "'AbsPredicateId'" := (Id 1) (at level 1).
Notation "'AbsTreeId'" := (Id 2) (at level 1).
Notation "'AbsCellId'" := (Id 3) (at level 1).
Notation "'AbsArrayId'" := (Id 4) (at level 1).
Notation "'AbsPathId'" := (Id 5) (at level 1).

Inductive anyHeapv {t} : nat -> nat -> heap -> (list (@Value t)) -> Prop :=
    | AnyHeapvBase : forall start,
                     anyHeapv start 0 (fun x => None) nil
    | AnyHeapvNext : forall start next heap y r,
                     anyHeapv (S start) next heap r ->
                     anyHeapv start (S next) (fun x => if beq_nat x start then Some y else heap x)
                                    ((NatValue y)::r).

Inductive basicState {t} : id -> list (@Value t) -> heap -> Prop :=
  | BTStatePredicate : forall e h,
                       e<>0 ->
                       (forall x, h x = None) ->
                       basicState AbsPredicateId ((NatValue e)::nil) h
  | BStateTree : forall r s f h ff tt,
                 Tree r s f tt h ->
                 strip_nat_values ff f ->
                 basicState AbsTreeId ((NatValue r)::tt::(NatValue s)::ff) h
  | BStatePath : forall r s f base path h ff,
                 Path r s f base path ->
                 strip_nat_values ff f ->
                 (forall x, h x = None) ->
                 basicState AbsPathId ((NatValue r)::base::path::(NatValue s)::ff) h
  | BStateArray : forall r s h vl,
                  anyHeapv r s h vl->
                  basicState AbsArrayId ((NatValue r)::(NatValue s)::(ListValue vl)::nil) h
  | BTStateCell : forall v l h,
                  h l = Some v ->
                  l<>0 ->
                  (forall x, x<>l -> h x=None) ->
                  basicState AbsCellId ((NatValue l)::(NatValue v)::nil) h.

Notation "'[' x ']'" := (AbsLeaf (Id 1) (x::nil))
  (at level 20).
Notation "x '|->' y" := (AbsLeaf (Id 3) (x::y::nil))
  (at level 20).
Notation "'TREE(' r ',' f ',' s ',' l ')'" := (AbsLeaf (Id 2) (r::f::s::l))
  (at level 20).
Notation "'Path(' r ',' f ',' p ',' s ',' l ')'" := (AbsLeaf (Id 5) (r::f::p::s::l))
  (at level 20).
Notation "'ARRAY(' r ',' s ',' v ')'" := (AbsLeaf (Id 4) (r::s::v::nil))
  (at level 20).


(***************************************************************************
 *
 * basicAccumulate
 *
 * This is used to fill in the 'ac' parameter in absState.  For now, this is
 * a place holder.  There are no actual definitions.
 *
 ***************************************************************************)

Notation "'AbsSumId'" := (Id 1) (at level 1).

Inductive sumValues {t} {teq} {f} : (id -> nat) -> (list (@Value t)) -> (list (@Value t)) -> (@absExp t teq f) -> (@Value t) -> Prop :=
  | SumNil : forall b e env,
             sumValues env b nil e (NatValue 0)
  | SumCons : forall b e x ff r env y v,
              sumValues env b r e (NatValue x) ->
              absEval env (b++(ff::nil)) e = NatValue v ->
              y = x+v ->
              sumValues env b (ff::r) e (NatValue y).

Inductive basicAccumulate {t} {teq} {f} : id -> (id -> nat) -> (list (@Value t)) -> (list (@Value t)) ->
                                          (@absExp t teq f) ->
                                          (@Value t) -> Prop :=
  | BASum : forall env b e l tt,
            sumValues env b l e tt ->
            basicAccumulate AbsSumId env b l e tt.

Notation "'SUM(' e ',' f ',' t ')'" := (AbsAccumulate AbsSumId e f t) (at level 20).

(***************************************************************************
 *
 * absStateBasic
 *
 * Instantiated version of absState with 'f' instantiated to basicEval,
 * 't' instantiated to basicState and 'ac' basicAccumulate.  This is the
 * instantiation of AbsState that is useful for our derivation in
 * TreeTraversal.v.  The 'ev' parameter is instantiated to 'unit' and 'eq'
 * is instantiated to a function 'eq_unit' which we define below.
 *
 ***************************************************************************)

Definition absExpBasicF {t} {teq} := @absExp t teq (@basicEval t).

Definition absStateBasicF {t} {teq} {f} := @absState t teq f
                                           (@basicState t) (@basicAccumulate t teq f).

Definition unitEval := @basicEval unit.
Opaque unitEval.

Definition eq_unit (a : unit) (b : unit) := true.
Definition absExpBasic := @absExpBasicF unit eq_unit.
Definition absStateBasic := @absState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)).

(*************************************************************************
 *
 * Notations for the functions defined in basicEval
 *
 *************************************************************************)

Notation "'nth(' d ',' n ')'" := (AbsFun (Id 1) (d::n::nil))
  (at level 3).
(*Definition AbsFieldRef {ev} {eq} {f} := @AbsFun ev eq f AbsFieldRefId.*)
Notation "x '++++' y" := (AbsFun (Id 2) (x::y::nil))
  (at level 4).
(*Definition AbsPlus {ev} {eq} {f} := @AbsFun ev eq f AbsPlusId.*)
Notation "x '----' y" := (AbsFun (Id 3) (x::y::nil))
  (at level 4).
(*Definition AbsMinus {ev} {eq} {f} := @AbsFun ev eq f AbsMinusId.*)
Notation "x '****' y" := (AbsFun (Id 4) (x::y::nil))
  (at level 5).
(*Definition AbsTimes {ev} {eq} {f} := @AbsFun ev eq f AbsTimesId.*)
Notation "x '====' y" := (AbsFun (Id 5) (x::y::nil))
  (at level 6).
(*Definition AbsEqual {ev} {eq} {f} := @AbsFun ev eq f AbsEqualId.*)
Notation "x '<<<<' y" := (AbsFun (Id 6) (x::y::nil))
  (at level 6).
(*Definition AbsLess {ev} {eq} {f} := @AbsFun ev eq f AbsLessId.*)
Notation "x 'inTree' t" := (AbsFun (Id 7) (x::t::nil))
  (at level 5).
(*Definition AbsRMember {ev} {eq} {f} := @AbsFun ev eq f AbsRMemberId.*)
Notation "x 'inTreeLoc' t" := (AbsFun (Id 8) (x::t::nil))
  (at level 5).
(*Definition AbsRInclude {ev} {eq} {f} := @AbsFun ev eq f AbsRIncludeId.*)
Notation "x '-->>' y" := (AbsFun (Id 9) (x::y::nil))
  (at level 10).
(*Definition AbsImply {ev} {eq} {f} := @AbsFun ev eq f AbsImplyId.*)
Notation "'~~' x" := (AbsFun (Id 10) (x::nil))
  (at level 7).
(*Definition AbsNot {ev} {eq} {f} := @AbsFun ev eq f AbsNotId.*)
Notation "x '//\\' y" := (AbsFun (Id 11) (x::y::nil))
  (at level 8).
(*Definition AbsAnd {ev} {eq} {f} := @AbsFun ev eq f AbsAndId.*)
Notation "x '\\//' y" := (AbsFun (Id 12) (x::y::nil))
  (at level 9).
(*Definition AbsOr {ev} {eq} {f} := @AbsFun ev eq f AbsOrId.*)
Notation "'ite(' x ',' y ',' z ')'" := (AbsFun (Id 13) (x::y::z::nil))
  (at level 10).
(*Definition AbsIte {ev} {eq} {f} := @AbsFun ev eq f AbsIteId.*)
Notation "'find(' x ',' y ')'" := (AbsFun (Id 14) (x::y::nil))
  (at level 3).
(*Definition AbsFindRecord {ev} {eq} {f} := @AbsFun ev eq f AbsFindRecordId.*)
Notation "'list(' x ')'" := (AbsFun (Id 15) (x))
  (at level 3).
(*Definition AbsBuildList {ev} {eq} {f} := @AbsFun ev eq f AbsBuildListId.*)
Notation "'TreeRecords(' x ')'" := (AbsFun (Id 16) (x::nil))
  (at level 3).
(*Definition AbsRecordList {ev} {eq} {f} := @AbsFun ev eq f AbsRecordListId.*)
Notation "'range(' x ',' y ')'" := (AbsFun (Id 17) (x::y::nil))
  (at level 3).
(*Definition AbsRangeList {ev} {eq} {f} := @AbsFun ev eq f AbsRangeListId.*)
Notation "'--(' a ',' b ')--->' c" := (AbsFun (Id 1) ((AbsFun (Id 14) (a::b::nil))::(AbsFun (Id 3) (c::#1::nil))::nil))
  (at level 3).
Notation "'--(' a ',' b ')-->' c" := (AbsFun (Id 1) ((AbsFun (Id 14) (a::b::nil))::(AbsConstVal (NatValue (c+1)))::nil))
  (at level 3).
Notation "'replacenth(' d ',' n ',' e ')'" := (AbsFun (Id 18) (d::n::e::nil))
  (at level 3).

(****************************************************************************
 *
 * supportsBasicFunctionality
 *
 * instantiation of supportsFunctionality
 *
 ****************************************************************************)

Definition supportsBasicFunctionality ev eq f t ac v:=
    supportsFunctionality unit eq_unit (@basicEval unit) 18 basicState 4 (@basicAccumulate unit eq_unit (@basicEval unit)) 0
                          ev eq f t ac (fun (x:ev) => tt) (fun x => (v:ev)).
