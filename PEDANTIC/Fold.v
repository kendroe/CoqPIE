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
Inductive pickNCells : absState -> absState -> nat -> absExp -> list absState -> Prop :=
    | PNCBase : forall state root,
                pickNCells state state 0 root nil
    | PNCInductive0 : forall state state1 state2 root v cells,
                     spickElement state (root |-> v) state1 ->
                     pickNCells state1 state2 0 root cells ->
                     pickNCells state state2 (S 0) root (cells++(root++++#0 |-> v)::nil)     | PNCInductive : forall state state1 state2 size root v cells,
                     spickElement state (root++++#size |-> v) state1 ->
                     pickNCells state1 state2 size root cells ->
                     pickNCells state state2 (S size) root (cells++(root++++#size |-> v)::nil).
Hint Constructors pickNCells.

Ltac pickNCells := (eapply PNCBase || (eapply PNCInductive0;[solveSPickElement | pickNCells]) || (eapply PNCInductive;[solveSPickElement | pickNCells])).

Inductive strip_fields : list absExp -> list nat -> Prop :=
    | SFNil : strip_fields nil nil
    | SFCons : forall n r1 r2,
               strip_fields r1 r2 ->
               strip_fields ((#n)::r1) (n::r2).
Hint Constructors strip_fields.

Ltac stripFields := ((eapply SFCons;stripFields) || eapply SFNil).
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
Inductive pickNHeaps : absState -> absState -> (list nat) -> nat -> list nat -> list (absState)-> list (nat * (absState)) -> Prop :=
    | PNHBase : forall state size fields cells,
                pickNHeaps state state nil size fields cells nil
    | PNHInductive : forall state state1 state2 base fff r root ff fields cells size heap hr e_fields,
                strip_fields fields e_fields ->
                nth fff cells AbsEmpty = ((root++++#ff) |-> base) ->
                spickElement state (TREE(base,v(heap),#size,fields)) state1 ->
                pickNHeaps state1 state2 r size e_fields cells hr ->
                pickNHeaps state state2 (fff::r) size e_fields cells ((fff,TREE(base,v(heap),#size,fields))::hr).
Hint Constructors pickNHeaps.

Ltac pickNHeaps := (eapply PNHInductive;[stripFields | (simpl;reflexivity) | solveSPickElement | pickNHeaps]) ||
                   eapply PNHBase.

Fixpoint folded_heap (v : nat) (heaps : list (nat * absState)) : option nat :=
   match heaps with
   | ((x,TREE(root,v(h),size,fields))::r) => if beq_nat h v then Some x else folded_heap v r
   | (_::r) => folded_heap v r
   | _ => None
   end.

Fixpoint noFold (e : absExp) (heaps : list (nat * absState)) : bool :=
   match e with
   | AbsConstVal v => true
   | AbsVar vv => true
   | AbsQVar v => match folded_heap v heaps with Some _ => false | None => true end
   | AbsFun i l => (fix go l := match l with
                                | nil    => true
                                | (a::b) => if noFold a heaps then go b else false
                                end) l
   end.

Fixpoint foldExp (e : absExp) (n : nat) (heaps : list (nat * absState)) : absExp :=
   match e with
   | AbsConstVal v => (AbsConstVal v)
   | AbsVar vv => (AbsVar vv)
   | AbsQVar v => match folded_heap v heaps with None => (AbsQVar v) | Some x => nth(v(n),#(x+1)) end
   | AbsFun i l => AbsFun i ((fix go l := match l with
                                | nil       => nil
                                | (a::b)    => (foldExp a n heaps)::(go b)
                                end) l)
   end.

Fixpoint addHeaps (heaps : list (nat * absState)) :=
    map (fun x => (fst x,addStateVar 0 (snd x))) heaps.

Fixpoint foldState (s : absState) (n : nat) (heaps : list (nat * absState)) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (foldState s1 n heaps) (foldState s2 n heaps))
    | AbsOrStar s1 s2 => (AbsOrStar (foldState s1 n heaps) (foldState s2 n heaps))
    | AbsExistsT s => AbsExistsT (foldState s (S n) (addHeaps heaps))
    | AbsExists e s => AbsExists (foldExp e n heaps) (foldState s (S n) (addHeaps heaps))
    | AbsAll e s => AbsAll (foldExp e n heaps) (foldState s (S n) (addHeaps heaps))
    | AbsEach e s => AbsEach (foldExp e n heaps) (foldState s (S n) (addHeaps heaps))
    | AbsEmpty => AbsEmpty
    | AbsNone => AbsNone
    | AbsAny => AbsAny
    | AbsLeaf i l => AbsLeaf i (map (fun x => foldExp x n heaps) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (foldExp e1 n heaps) (foldExp e2 n heaps) (foldExp e3 n heaps)
    | AbsMagicWand s1 s2 => AbsMagicWand (foldState s1 n heaps) (foldState s2 n heaps)
    | AbsUpdateVar s i e => AbsUpdateVar (foldState s n heaps) i (foldExp e n heaps)
    | AbsUpdateWithLoc s i e => AbsUpdateWithLoc (foldState s n heaps) i (foldExp e n heaps)
    | AbsUpdateLoc s l e => AbsUpdateLoc (foldState s n heaps) (foldExp l n heaps) (foldExp e n heaps)
    | AbsUpdState s1 s2 s3 => AbsUpdState (foldState s1 n heaps) (foldState s2 n heaps) (foldState s3 n heaps)
    | AbsClosure s l => AbsClosure s (map (fun x => foldExp x n heaps) l)
   end.

Fixpoint build_equations (heap : absExp) (cells : list absState) (fields : list nat) : absState :=
    match cells with
    | nil => AbsEmpty
    | ((l++++#o |-> val)::r) => if mem_nat o fields then
                                    ([nth(nth(heap,#(o+1)),#0)====val]) ** (build_equations heap r fields)
                                else
                                    ([nth(heap,#(o+1))====val]) ** (build_equations heap r fields)
    | (_::r) => build_equations heap r fields
    end.

Fixpoint getRootLevel (s : absState) : nat :=
    match s with
    | AbsExistsT s => S (getRootLevel s)
    | _ => 0
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
Inductive foldHeap : absState -> absState -> Prop :=
    FoldHeap : forall state state2 hvars size fields e_fields cells root r r' r'' rl,
         strip_fields e_fields fields ->
         r = getRoot state ->
         pickNCells r r' size root cells ->
         pickNHeaps r' r'' fields size fields cells hvars ->
         rl = getRootLevel state ->
         state2 = AbsExistsT (replaceRoot state ((TREE(root,v(rl),#size,e_fields) ** (build_equations (v(rl)) cells fields) ** (foldState r'' rl hvars)))) ->
         foldHeap state state2.

(*
 * This is an auxiliary definition that folds up absAll definitions corresponding to the
 * TREE that has just been folded by foldHeap.
 *
 *
 * Parameters:
 *  #1 : absState - state to be folded
 *  #2 : absState - output of folded state
 *)
Inductive foldAll : absState -> absState -> Prop :=
    FoldAll : forall state root root' root'' r roott roott' x n np cond cond' cond'' size e_fields fields var y state2,
        root = getRoot state ->
        n = getRootLevel state ->
        spickElement root (AbsAll TreeRecords(nth(v(x),#np)) cond) root' ->
        spickElement root' (TREE(r, v(x), #size, fields)) roott ->
        spickElement roott ([nth(v(x),#y)====var]) roott' ->
        strip_fields fields e_fields ->
        cond' = removeStateVar 0 (replaceStateExp (nth(find(nth(v(S x),#np),v(0)),#y)) (addExpVar 0 var) cond) ->
        cond'' = replaceStateExp nth(v(S x),#np) v(S x) cond ->
        spickElement root' cond' root'' ->
        state2 = replaceRoot state (AbsStar (AbsAll TreeRecords(v(x)) cond'') root'') ->
        foldAll state state2.

(*
 * Tactics to automate the fold operations above
 *)
Ltac foldHeap R F S :=
     eapply FoldHeap with (root := R) (fields := F) (size := S);[
                stripFields |
                (simpl; reflexivity) |
                pickNCells |
                pickNHeaps |
                (simpl; reflexivity) |
                (simpl; reflexivity)].

Ltac foldAll x :=
     eapply FoldAll;[
         (simpl; reflexivity) |
         (simpl; reflexivity) |
         solveSPickElement |
         solveSPickElement |
         (instantiate (3 := x);solveSPickElement) |
         stripFields |
         (simpl; reflexivity) |
         (simpl; reflexivity) |
         solveSPickElement |
         (simpl; reflexivity)].

Theorem foldSum : forall v e ttt t1 t2 b s e',
    realizeState (SUM(range(#0,v),e,t1)) b s ->
    realizeState (SUM(range(v++++#1,ttt),e,t2)) b s ->
    e' = replaceExpVar (length b) v e ->
    realizeState (SUM(range(#0,ttt),e,t1++++t2++++e')) b s.
Proof. admit. Admitted.













































