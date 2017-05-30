(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * Unfold.v
 * This file contains the definition of unfoldHeap which unfolds a single TREE
 * construct into cells for the root node and TREE constructs for the children.  It is
 * the reverse of fold.
 *
 * Key declarations:
 *     unfoldHeap
 *
 **********************************************************************************)

Require Export SfLib.
Require Export ImpHeap.
Require Export AbsState.
Require Export PickElement.
Require Export AbsExecute.

Fixpoint is_condition (s : absState) : bool :=
    match s with
    | AbsStar x y => if is_condition x then is_condition y else false
    | AbsOrStar x y => if is_condition x then is_condition y else false
    | [x] => true
    | _ => false
    end.

Fixpoint getUnfoldRoot (s : absState) : absState :=
    match s with
    | AbsExistsT s => getUnfoldRoot s
    | AbsUpdateVar s i v => getUnfoldRoot s
    | AbsUpdateWithLoc s i v => getUnfoldRoot s
    | AbsUpdateLoc s i v => getUnfoldRoot s
    | AbsMagicWand a b => getUnfoldRoot a
    | AbsStar x y => if is_condition x then getUnfoldRoot y else if is_condition y
                     then getUnfoldRoot x else s
    | _ => s
    end.

Fixpoint stripVar (v : id) (l : list absState) : list absState :=
    match l with
    | (a::b) => if hasVarState a v
                then (stripVar v b)
                else a::(stripVar v b)
    | nil => nil
    end.

Fixpoint joinStates (l : list absState) (s : absState) :=
    match l with
    | (a::b) => AbsStar a (joinStates b s)
    | nil => s
    end.

Fixpoint getUnfoldRootConds (s : absState) (b : list absState) : absState :=
    match s with
    | AbsExistsT s => (getUnfoldRootConds s) (map (addStateVar 0) b)
    | AbsUpdateVar s i v => getUnfoldRootConds s (stripVar i b)
    | AbsUpdateLoc s i v => getUnfoldRootConds s b
    | AbsUpdateWithLoc s i v => getUnfoldRootConds s (stripVar i b)
    | AbsMagicWand a d => getUnfoldRootConds a b
    | AbsStar x y => if is_condition x then (getUnfoldRootConds y (x::b)) else
                     if is_condition y then (getUnfoldRootConds x (y::b)) else
                     joinStates b (AbsStar x y)
    | _ => joinStates b s
    end.

Fixpoint updateRootForConds (s : absState) (e : absExp) : absExp :=
    match s with
    | AbsExistsT s => updateRootForConds s (addExpVar 0 e)
    | AbsUpdateVar s i v => updateRootForConds s e
    | AbsUpdateLoc s i v =>updateRootForConds s e
    | AbsUpdateWithLoc s i v => updateRootForConds s e
    | AbsMagicWand a b => updateRootForConds a e
    | AbsStar ([x]) y => updateRootForConds y e
    | AbsStar x ([y]) => updateRootForConds x e
    | _ => e
    end.

Fixpoint getUnfoldTrace (s : absState) : list UnfContext :=
    match s with
    | AbsExistsT s => UnfCExistsT::(getUnfoldTrace s)
    | AbsUpdateVar s i v => (UnfCUpdateVar i v)::(getUnfoldTrace s)
    | AbsUpdateWithLoc s i v => (UnfCUpdateWithLoc i v)::(getUnfoldTrace s)
    | AbsUpdateLoc s i v => (UnfCUpdateLoc i v)::(getUnfoldTrace s)
    | AbsMagicWand a b => (UnfCMagicWand b)::(getUnfoldTrace a)
    | AbsStar x y => if is_condition x then (UnfCStar x)::(getUnfoldTrace y)
                     else if is_condition y then (UnfCStar y)::(getUnfoldTrace x)
                     else nil
    | _ => nil
    end.

Fixpoint replaceTerm (s : absState) (t : absExp) (r : absExp) :=
    match t with
    | AbsQVar i => Some (replaceStateVar i t s)
    | AbsVar v => substVarState s v r
    | _ => Some s
    end.

Fixpoint replaceTermExp (e : absExp) (t : absExp) (r : absExp) :=
    match t with
    | AbsQVar i => replaceExpVar i t e
    | AbsVar v => substVar e v r
    | _ => e
    end.

Fixpoint replaceTermState (e : absState) (t : absExp) (r : absExp) :=
    match t with
    | AbsQVar i => Some (replaceStateVar i t e)
    | AbsVar v => substVarState e v r
    | _ => Some e
    end.

(*Fixpoint finishState (s : absState) (l : list (UnfContext)) :=
    match l with
    | UnfCExistsT::r => AbsExistsT (finishState s r)
    | (UnfCUpdateVar i v)::r => (AbsUpdateVar (finishState s r) i v)
    | (UnfCUpdateWithLoc i v)::r => AbsUpdateWithLoc (finishState s r) i v
    | (UnfCUpdateLoc i v)::r => AbsUpdateLoc (finishState s r) i v
    | (UnfCMagicWand d)::r => AbsMagicWand (finishState s r) d
    | (UnfCStar x)::r => AbsStar (finishState s r) ([x])
    | nil => s
    end.*)

Fixpoint rebuildState (s : absState) (l : list UnfContext) (v: absExp) (r: absExp) : option absState :=
    match l with
    (f::rr) => match f with
              | UnfCExistsT => match v with
                               | AbsQVar 0 => Some (AbsExistsT (finishState s rr))
                               | AbsQVar (S n) => match rebuildState s rr (AbsQVar n) (removeExpVar 0 r) with
                                                  | Some x => Some (AbsExistsT x)
                                                  | None => None
                                                  end
                               | x => match rebuildState s rr x (removeExpVar 0 r) with
                                      | Some x => Some (AbsExistsT x)
                                      | None => None
                                      end
                               end
              | UnfCUpdateVar i vv => if beq_absExp (AbsVar i) v then
                                          Some (AbsUpdateVar (finishState s rr) i v)
                                      else
                                          match (rebuildState s rr v r) with
                                          | Some x => Some (AbsUpdateVar x i (replaceTermExp vv v r))
                                          | None => None
                                          end
              | UnfCUpdateWithLoc i vv => if beq_absExp (AbsVar i) v then
                                              Some (AbsUpdateWithLoc (finishState s rr) i v)
                                          else
                                              match (rebuildState s rr v r) with
                                              | Some x => Some (AbsUpdateWithLoc x i (replaceTermExp vv v r))
                                              | None => None
                                              end
              | UnfCUpdateLoc i vv => match rebuildState s rr v r with
                                      | Some x => Some (AbsUpdateLoc x (replaceTermExp i v r) (replaceTermExp vv v r))
                                      | _ => None
                                      end
              | UnfCMagicWand d => match (rebuildState s rr v r),(replaceTerm d v r) with
                                   | Some x,Some y => Some (AbsMagicWand x y)
                                   | _,_ => None
                                   end
              | UnfCStar x => match (rebuildState s rr v r),(replaceTermState x v r) with
                              | Some x,Some y => Some (AbsStar x y)
                              | _,_ => None
                              end
              end
    | nil => Some s
    end.

Fixpoint existsCount (l : list UnfContext) :=
    match l with
    | UnfCExistsT::r => (S (existsCount r))
    | _::r => existsCount r
    | nil => 0
    end.

Fixpoint replaceUnfoldRoot (s : absState) (r : absState) : absState :=
    match s with
    | AbsExistsT s => AbsExistsT (replaceUnfoldRoot s r)
    | AbsUpdateVar s i v => AbsUpdateVar (replaceUnfoldRoot s r) i v
    | AbsUpdateWithLoc s i v => AbsUpdateWithLoc (replaceUnfoldRoot s r) i v
    | AbsUpdateLoc s i v => AbsUpdateLoc (replaceUnfoldRoot s r) i v
    | AbsMagicWand a b => AbsMagicWand (replaceUnfoldRoot a r) b
    | _ => r
    end.

Fixpoint pushExpVar (start : nat) (v : nat) (e : absExp) : absExp :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar vv => if ble_nat vv start then AbsQVar vv else AbsQVar (vv+v)
   | AbsFun i l => AbsFun i (map (pushExpVar start v) l)
   end.

Fixpoint pushStateVar (s : absState) (start : nat) (n : nat) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (pushStateVar s1 start n) (pushStateVar s2 start n))
    | AbsOrStar s1 s2 => (AbsOrStar (pushStateVar s1 start n) (pushStateVar s2 start n))
    | AbsExistsT s => AbsExistsT (pushStateVar s (S start) n)
    | AbsExists e s => AbsExists (pushExpVar start n e) (pushStateVar s (S start) n)
    | AbsEach e s => AbsEach (pushExpVar start n e) (pushStateVar s (S start) n)
    | AbsAll e s => AbsAll (pushExpVar start n e) (pushStateVar s (S start) n)
    | AbsEmpty => AbsEmpty
    | AbsNone => AbsNone
    | AbsAny => AbsAny
    | AbsLeaf i l => AbsLeaf i (map (pushExpVar start n) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (pushExpVar start n e1) (pushExpVar start n e2) (pushExpVar start n e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (pushStateVar s1 start n) (pushStateVar s2 start n)
    | AbsUpdateVar s i v => AbsUpdateVar (pushStateVar s start n) i (pushExpVar start n v)
    | AbsUpdateWithLoc s i v => AbsUpdateWithLoc (pushStateVar s start n) i (pushExpVar start n v)
    | AbsUpdateLoc s i v => AbsUpdateLoc (pushStateVar s start n) (pushExpVar start n i) (pushExpVar start n v)
    | AbsUpdState s1 s2 s3 => AbsUpdState (pushStateVar s1 start n) (pushStateVar s2 start n) (pushStateVar s3 start n)
    | AbsClosure s l => AbsClosure s (map (pushExpVar start n) l)
   end.

Inductive noInstanceExpVar : nat -> absExp -> Prop :=
   | NIAbsConstVal : forall vv v, noInstanceExpVar vv (AbsConstVal v)
   | NIAbsVar : forall vv v, noInstanceExpVar vv (AbsVar v)
   | NIAbsQVar : forall v vv, v <> vv -> noInstanceExpVar vv (AbsQVar v)
   | NIAbsFun : forall i l v,
                (forall x, In x l -> noInstanceExpVar v x) ->
                noInstanceExpVar v (AbsFun i l).

Inductive noInstanceStateVar : nat -> absState -> Prop :=
    | NIAbsStar : forall n s1 s2,
                     noInstanceStateVar n s1 ->
                     noInstanceStateVar n s2 ->
                     noInstanceStateVar n (AbsStar s1 s2)
    | NIAbsOrStar : forall n s1 s2,
                       noInstanceStateVar n s1 ->
                       noInstanceStateVar n s2 ->
                       noInstanceStateVar n (AbsOrStar s1 s2)
    | NIAbsExistsT : forall s n,
                     noInstanceStateVar n s ->
                     noInstanceStateVar n (AbsExistsT s)
    | NIAbsExists : forall e s n,
                    noInstanceStateVar n s ->
                    noInstanceExpVar n e ->
                    noInstanceStateVar n (AbsExists e s)
    | NIAbsAll : forall e s n,
                 noInstanceStateVar n s ->
                 noInstanceExpVar n e ->
                 noInstanceStateVar n (AbsAll e s)
    | NIAbsEach : forall e s n,
                  noInstanceStateVar n s ->
                  noInstanceExpVar n e ->
                  noInstanceStateVar n (AbsEach e s)
    | NIAbsEmpty : forall n, noInstanceStateVar n AbsEmpty
    | NIAbsR : forall i l n,
               (forall x, In x l -> noInstanceExpVar n x) ->
               noInstanceStateVar n (AbsLeaf i l)
    | NIAbsAccumulate : forall n id e1 e2 e3,
               noInstanceExpVar n e1 ->
               noInstanceExpVar n e2 ->
               noInstanceExpVar n e3 ->
               noInstanceStateVar n (AbsAccumulate id e1 e2 e3).

Fixpoint build_cells (n : nat) (ff : list nat) (root : absExp) (s : absState) (o : nat) :=
    match n return absState with
    | 0 => s
    | S n1 => AbsStar ((root++++#n1) |-> (if mem_nat n1 ff then (nth(v(n1+o),#0)) else v(n1+o))) (build_cells n1 ff root s o)
    end.

Fixpoint build_Rs (f : list nat) (size : nat) (fields : list nat) (h : absExp) (s : absState) (o : nat) :=
    match f with
    | nil => s
    | (f::r) => AbsStar (AbsLeaf (AbsTreeId) (nth(v(f+o),#0)::(nth(h,#(f+1)))::(#size)::(map AbsConstVal (map NatValue fields))))
                           (build_Rs r size fields h s o)
    end.

Fixpoint appendQuants2 (h : nat) (s : absState) :=
    match h with
    | 0 => s
    | S h1 => AbsExistsT (appendQuants2 h1 s)
    end.

Fixpoint appendQuants (n : nat) (h : nat) (s : absState) :=
    match n with
    | 0 => appendQuants2 h s
    | S n1 => AbsExistsT (appendQuants n1 h s)
    end.

Inductive constantValues : list (absExp) -> list nat -> Prop :=
    | ConstantValuesNil : constantValues nil nil
    | ConstantValuesCons : forall r r' f field,
                           constantValues r r' ->
                           NatValue f = field ->
                           constantValues ((AbsConstVal field)::r) (f::r').

Ltac solveConstantValues := solve [eapply ConstantValuesNil | (eapply ConstantValuesCons;[solveConstantValues | reflexivity]) ].

Hint Constructors constantValues.

Fixpoint createVarList start total :=
    match total with
    | 0 => nil
    | S(n) => (AbsQVar start)::(createVarList (start+1) n)
    end.

(*
 * This is the main predicate.  It takes two parameters.  The first inputs the state.
 *  The second outputs a new state in which a single RFun term has been unfolded.
 *)
(*Inductive unfoldHeap {ev} {eq} {ff} {t} {ac} : @absExp ev eq ff -> @absState ev eq ff t ac -> @absState ev eq ff t ac -> Prop :=
    UnfoldHeap : forall state rs rs' state' state'' fields root s f size h,
        rs = getRoot state ->
        spickElement rs (AbsLeaf (AbsTreeId) (root::(AbsQVar h)::(AbsConstVal s)::f)) rs' ->
        constantValues f fields ->
        NatValue size = s ->
        state' = replaceRoot state
                     (build_cells size fields root
                         (build_Rs fields size fields (list(root::(createVarList 0 size)))
                             (replaceStateVar
                                 (h+size)
                                 (list(root::(createVarList 0 size)))
                                 rs'))) ->
        state'' = (appendQuants2 size state') ->
        unfoldHeap root state state''.*)


Fixpoint replace_term (s : absState) (t : absState) (n : absState) :=
    match s with
    | AbsStar l r => match replace_term l t n with
                     | Some x => Some (AbsStar x r)
                     | None => match replace_term r t n with
                                     | Some x => Some (AbsStar l x)
                                     | None => None
                                     end
                     end
    | AbsMagicWand l r => match replace_term l t n with
                     | Some x => Some (AbsMagicWand x r)
                     | None => match replace_term r t n with
                                     | Some x => Some (AbsMagicWand l x)
                                     | None => None
                                     end
                     end
    | AbsUpdateVar s i v => match replace_term s t n with
                            | Some x => Some (AbsUpdateVar x i v)
                            | None => None
                            end
    | AbsUpdateWithLoc s i v => match replace_term s t n with
                                | Some x => Some (AbsUpdateWithLoc x i v)
                                | None => None
                                end
    | x => if beq_absState s t then Some n else None
    end.

Inductive unfoldHeap : absExp -> absState -> absState -> Prop :=
    UnfoldHeap : forall state rs rs' rt state' state'' fields root s f size h rs'' nn,
        rs = getUnfoldRoot state ->
        rt = getUnfoldTrace state ->
        nn = existsCount rt ->
        fpickElement rs (AbsLeaf (AbsTreeId) (root::(AbsQVar h)::(AbsConstVal s)::f)) rs' ->
        constantValues f fields ->
        NatValue size = s ->
        Some rs'' = replace_term (replaceStateVar h (list(root::(createVarList nn size))) rs) (replaceStateVar h (list(root::(createVarList nn size))) (AbsLeaf (AbsTreeId) (root::(AbsQVar h)::(AbsConstVal s)::f))) (build_cells size fields root
            (build_Rs fields size fields (list(root::(createVarList nn size))) AbsEmpty nn) nn) ->
        Some state' = rebuildState rs'' rt (AbsQVar h) (list(root::(createVarList nn size))) ->
        state'' = (appendQuants2 size state') ->
        unfoldHeap root state state''.

Ltac unfoldHeap root :=
    eapply UnfoldHeap;[
        (compute; reflexivity) |
        (compute; reflexivity) |
        (compute; reflexivity) |
        (instantiate (5 := root); solveFPickElement) |
        solveConstantValues |
        (compute; reflexivity) |
        (compute; reflexivity) |
        (compute; reflexivity) |
        (compute; reflexivity) ].

Theorem unfold_pre : forall P P' c Q res root Q',
    unfoldHeap root P P' ->
    {{P'}}c{{Q return res with Q'}} ->
    {{P}}c{{Q return res with Q'}}.
Proof. admit. Admitted.

Theorem unfold_rs1 : forall root P Q bindings s,
    unfoldHeap root P Q ->
    realizeState Q bindings s ->
    realizeState P bindings s.
Proof. admit. Admitted.

Theorem unfold_rs2 : forall P Q bindings root s,
    unfoldHeap root P Q ->
    realizeState P bindings s ->
    (forall s bindings, realizeState (getUnfoldRootConds P nil) bindings s -> exists v, absEval (env_p s) bindings root=NatValue (S v)) ->
    realizeState Q bindings s.
Proof. admit. Admitted.

Theorem unfold_merge1 : forall P Q r m root,
    unfoldHeap root P Q ->
    mergeStates Q r m ->
    (forall s bindings, realizeState (getUnfoldRootConds P nil) bindings s -> exists v, absEval (env_p s) bindings root=NatValue (S v)) ->
    mergeStates P r m.
Proof. admit. Admitted.

Theorem unfold_merge2 : forall P Q l m root,
    unfoldHeap root P Q ->
    mergeStates l Q m ->
    (forall s bindings, realizeState (getUnfoldRootConds P nil) bindings s -> exists v, absEval (env_p s) bindings root=NatValue (S v)) ->
    mergeStates l P m.
Proof. admit. Admitted.

Theorem unfoldSum : forall l h e sum bbb lbbb state ee v,
        lbbb = length bbb ->
        ee = replaceExpVar lbbb v e ->
        absEval (fst state) bbb (v<<<<(h++++#1))=NatValue 1 ->
        ((realizeState (SUM(range(l,h),e,sum)) bbb state) <->
                    (realizeState (AbsExistsT (AbsExistsT
                                      (SUM(range(l,v),addExpVar lbbb (addExpVar lbbb e),v(lbbb)) **
                                      (SUM(range(v++++#1,h),addExpVar lbbb (addExpVar lbbb e),v(lbbb+1))) **
                                       [sum====(v(lbbb)++++v(lbbb+1))++++ee]))) bbb state)).
Proof. admit. Admitted.










































































































