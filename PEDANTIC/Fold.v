(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * Fold.v
 * This file contains the definition of foldHeap which folds together individual
 * cells and TREE predicates into a single TREE predicate.
 *
 * Key definitions:
 *     foldState
 *     foldAll
 *
 **********************************************************************************)

Require Export SfLib.
Require Export ImpHeap.
Require Export AbsState.
Require Export AbsStateInstance.
Require Export PickElement.
Require Export AbsExecute.
Require Export Coq.Logic.FunctionalExtensionality.
Opaque unitEval.

(*
 * pickNCells picks out the cells that are to be included in the folded RFun term.  It also generates
 * a portion of the predicate used to map the original components to the folded components
 *
 * Parameters:
 *    #1 : absState - input of state from which to pick the cells
 *    #2 : absState - output of state in which the cells have been removed
 *    #3 : nat - number of cells that need to be picked
 *    #4 : absExp - root of folded tree
 *    #5 : list absState - output of the list of cells picked
 *)
Inductive pickNCells  {ev} {eq} {f} {t} {ac} : @absState ev eq f t ac -> @absState ev eq f t ac -> nat -> @absExp ev eq f -> list (@absState ev eq f t ac) -> Prop :=
    | PNCBase : forall state root,
                pickNCells state state 0 root nil
    | PNCInductive : forall state state1 state2 size root v cells,
                     spickElement state (root++++#size |-> v) state1 ->
                     pickNCells state1 state2 size root cells ->
                     pickNCells state state2 (S size) root (cells++(root++++#size |-> v)::nil).
Hint Constructors pickNCells.

Ltac pickNCells := (eapply PNCBase || (eapply PNCInductive;[solveSPickElement | pickNCells])).

Inductive strip_fields {ev} {eq} {f} : list (@absExp ev eq f) -> list nat -> Prop :=
    | SFNil : strip_fields nil nil
    | SFCons : forall n r1 r2,
               strip_fields r1 r2 ->
               strip_fields ((#n)::r1) (n::r2).
Hint Constructors strip_fields.

(*
 * pickNHeaps picks out the heaps that are to be included in the folded RFun term.  It also generates
 * a portion of the predicate used to map the original components to the folded components
 *
 * Parameters:
 *    #1 : absState - input of state from which to pick the heaps
 *    #2 : absState - output of state in which the heaps have been removed
 *    #3 : list nat - heaps that need to be picked (starts out the same as #5)
 *    #4 : nat - size parameter from RFun
 *    #5 : list nat - fields parameter from RFun
 *    #6 : list (nat * absState) - output of the list of heaps picked (associated with their field
 *                                 offset)
 *)
Inductive pickNHeaps {ev} {eq} {f} {t} {ac} : @absState ev eq f t ac -> @absState ev eq f t ac -> (list nat) -> nat -> list nat -> list (@absState ev eq f t ac)-> list (nat * (@absState ev eq f t ac)) -> Prop :=
    | PNHBase : forall state size fields cells,
                pickNHeaps state state nil size fields cells nil
    | PNHInductive : forall state state1 state2 base fff r root ff fields cells size heap hr e_fields,
                strip_fields fields e_fields ->
                nth fff cells AbsEmpty = ((root++++#ff) |-> base) ->
                spickElement state (TREE(base,v(heap),#size,fields)) state1 ->
                pickNHeaps state1 state2 r size e_fields cells hr ->
                pickNHeaps state state2 (fff::r) size e_fields cells ((fff,TREE(base,v(heap),#size,fields))::hr).
Hint Constructors pickNHeaps.

Ltac pickNHeaps := (eapply PNHInductive;[auto | (simpl;reflexivity) | solveSPickElement | pickNHeaps]) ||
                   eapply PNHBase.

Fixpoint folded_heap {ev} {eq} {f} {t} {ac} (v : nat) (heaps : list (nat * (@absState ev eq f t ac))) : option nat :=
   match heaps with
   | ((x,TREE(root,v(h),size,fields))::r) => if beq_nat h v then Some x else folded_heap v r
   | (_::r) => folded_heap v r
   | _ => None
   end.

Fixpoint noFold {ev} {eq} {f} {t} {ac} (e : @absExp ev eq f) (heaps : list (nat * (@absState ev eq f t ac))) : bool :=
   match e with
   | AbsConstVal v => true
   | AbsVar vv => true
   | AbsQVar v => match folded_heap v heaps with Some _ => false | None => true end
   | AbsFun i l => (fix go l := match l with
                                | nil    => true
                                | (a::b) => if noFold a heaps then go b else false
                                end) l
   end.

Fixpoint foldExp {ev} {eq} {f} {t} {ac} (e : @absExp ev eq f) (heaps : list (nat * (@absState ev eq f t ac))) : @absExp ev eq f :=
   match e with
   | AbsConstVal v => (AbsConstVal v)
   | AbsVar vv => (AbsVar vv)
   | AbsQVar v => match folded_heap v heaps with None => (AbsQVar (S v)) | Some x => nth(v(0),#(x+1)) end
   | AbsFun i l => AbsFun i ((fix go l := match l with
                                | nil       => nil
                                | (a::b)    => (foldExp a heaps)::(go b)
                                end) l)
   end.

Fixpoint foldState {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) (heaps : list (nat * (@absState ev eq f t ac))) : @absState ev eq f t ac :=
   match s with
    | AbsStar s1 s2 => (AbsStar (foldState s1 heaps) (foldState s2 heaps))
    | AbsOrStar s1 s2 => (AbsOrStar (foldState s1 heaps) (foldState s2 heaps))
    | AbsExistsT s => AbsExistsT (foldState s heaps)
    | AbsExists e s => AbsExists (foldExp e heaps) (foldState s heaps)
    | AbsAll e s => AbsAll (foldExp e heaps) (foldState s heaps)
    | AbsEach e s => AbsEach (foldExp e heaps) (foldState s heaps)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i l => AbsLeaf i (map (fun x => foldExp x heaps) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (foldExp e1 heaps) (foldExp e2 heaps) (foldExp e3 heaps)
    | AbsMagicWand s1 s2 => AbsMagicWand (foldState s1 heaps) (foldState s2 heaps)
    | AbsUpdateVar s i e => AbsUpdateVar (foldState s heaps) i (foldExp e heaps)
    | AbsUpdState s1 s2 s3 => AbsUpdState (foldState s1 heaps) (foldState s2 heaps) (foldState s3 heaps)
   end.

Fixpoint build_equations {ev} {eq} {f} {t} {ac} (heap : @absExp ev eq f) (cells : list (@absState ev eq f t ac)) (fields : list nat) : @absState ev eq f t ac :=
    match cells with
    | nil => AbsEmpty
    | ((l++++#o |-> val)::r) => if mem_nat o fields then
                                    ([nth(nth(heap,#(o+1)),#0)====(pushAbsVar val)]) ** (build_equations heap r fields)
                                else
                                    ([nth(heap,#(o+1))====(pushAbsVar val)]) ** (build_equations heap r fields)
    | (_::r) => build_equations heap r fields
    end.

(*
 * This is the main fold function.  It picks out the CellFun and RFun components to be folded and replaces
 * them all with a single RFun component.
 *
 *
 * Parameters:
 *  #1 : absState - state to be folded
 *  #2 : absState - output of folded state
 *)
Inductive foldHeap {ev} {eq} {f} {t} {ac} : @absState ev eq f t ac -> @absState ev eq f t ac -> Prop :=
    FoldHeap : forall state state2 hvars size fields e_fields cells root r r' r'',
         strip_fields e_fields fields ->
         r = getRoot state ->
         pickNCells r r' size root cells ->
         pickNHeaps r' r'' fields size fields cells hvars ->
         state2 = AbsExistsT (replaceRoot state ((TREE(root,v(0),#size,e_fields) ** (build_equations (v(0)) cells fields) ** (foldState r'' hvars)))) ->
         foldHeap state state2.

Fixpoint getRootLevel {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) : nat :=
    match s with
    | AbsExistsT s => S (getRootLevel s)
    | _ => 0
    end.

(*
 * This is an auxiliary definition that folds up absAll definitions corresponding to the
 * TREE that has just been folded by foldHeap.
 *
 *
 * Parameters:
 *  #1 : absState - state to be folded
 *  #2 : absState - output of folded state
 *)
Inductive foldAll {ev} {eq} {f} {t} {ac} : @absState ev eq f t ac -> @absState ev eq f t ac -> Prop :=
    FoldAll : forall state root root' root'' r roott roott' x n np cond cond' cond'' size e_fields fields var y state2,
        root = getRoot state ->
        n = getRootLevel state ->
        spickElement root (AbsAll TreeRecords(nth(v(x),#np)) cond) root' ->
        spickElement root' (TREE(r, v(x), #size, fields)) roott ->
        spickElement roott ([nth(v(x),y)====var]) roott' ->
        strip_fields fields e_fields ->
        cond' = replaceStateExp (nth(find(nth(v(x),#np),v(n)),y)) (var) cond ->
        cond'' = replaceStateExp nth(v(x),#np) v(x) cond ->
        spickElement root' cond' root'' ->
        state2 = replaceRoot state (AbsStar (AbsAll TreeRecords(v(x)) cond'') root'') ->
        foldAll state state2.

(*
 * Tactics to automate the fold operations above
 *)
Ltac foldHeap R F S :=
     eapply FoldHeap with (root := R) (fields := F) (size := S);[
                auto |
                (simpl; reflexivity) |
                pickNCells |
                pickNHeaps |
                (simpl; reflexivity)].

Ltac foldAll x :=
     eapply FoldAll;[
         (simpl; reflexivity) |
         (simpl; reflexivity) |
         solveSPickElement |
         solveSPickElement |
         (instantiate (3 := #x);solveSPickElement) |
         auto |
         (simpl; reflexivity) |
         (simpl; reflexivity) |
         solveSPickElement |
         (simpl; reflexivity)].

Theorem foldSum {ev} {eq} {f} {t} {ac} : forall v e ttt t1 t2 b s e',
    @realizeState ev eq f t ac (SUM(range(#0,v),e,t1)) b s ->
    @realizeState ev eq f t ac (SUM(range(v++++#1,ttt),e,t2)) b s ->
    e' = replaceExpVar (length b) v e ->
    @realizeState ev eq f t ac (SUM(range(#0,ttt),e,t1++++t2++++e')) b s.
Proof. admit. Qed.

