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
Opaque unitEval.

Fixpoint pushExpVar {ev} {eq} {f} (v : nat) (e : @absExp ev eq f) : @absExp ev eq f :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar vv => AbsQVar (vv+v)
   | AbsFun i l => AbsFun i (map (pushExpVar v) l)
   end.

Fixpoint pushStateVar {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) (n : nat) : @absState ev eq f t ac :=
   match s with
    | AbsStar s1 s2 => (AbsStar (pushStateVar s1 n) (pushStateVar s2 n))
    | AbsOrStar s1 s2 => (AbsOrStar (pushStateVar s1 n) (pushStateVar s2 n))
    | AbsExistsT s => AbsExistsT (pushStateVar s n)
    | AbsExists e s => AbsExists (pushExpVar n e) (pushStateVar s n)
    | AbsEach e s => AbsEach (pushExpVar n e) (pushStateVar s n)
    | AbsAll e s => AbsAll (pushExpVar n e) (pushStateVar s n)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i l => AbsLeaf i (map (pushExpVar n) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (pushExpVar n e1) (pushExpVar n e2) (pushExpVar n e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (pushStateVar s1 n) (pushStateVar s2 n)
    | AbsUpdateVar s i v => AbsUpdateVar (pushStateVar s n) i (pushExpVar n v)
    | AbsUpdState s1 s2 s3 => AbsUpdState (pushStateVar s1 n) (pushStateVar s2 n) (pushStateVar s3 n)
   end.

Inductive noInstanceExpVar {ev} {eq} {f} : nat -> @absExp ev eq f -> Prop :=
   | NIAbsConstVal : forall vv v, noInstanceExpVar vv (AbsConstVal v)
   | NIAbsVar : forall vv v, noInstanceExpVar vv (AbsVar v)
   | NIAbsQVar : forall v vv, v <> vv -> noInstanceExpVar vv (AbsQVar v)
   | NIAbsFun : forall i l v,
                (forall x, In x l -> noInstanceExpVar v x) ->
                noInstanceExpVar v (AbsFun i l).

Inductive noInstanceStateVar {ev} {eq} {f} {t} {ac} : nat -> @absState ev eq f t ac -> Prop :=
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

Fixpoint build_cells {ev} {eq} {f} {t} {ac} (n : nat) (ff : list nat) (root : @absExp ev eq f) (s : @absState ev eq f t ac) :=
    match n return @absState ev eq f t ac with
    | 0 => s
    | S n1 => AbsStar ((root++++#n1) |-> (if mem_nat n1 ff then (nth(v(n1),#0)) else v(n1))) (build_cells n1 ff root s)
    end.

Fixpoint build_Rs {ev} {eq} {ff} {t} {ac} (f : list nat) (size : nat) (fields : list nat) (h : @absExp ev eq ff) (s : @absState ev eq ff t ac) :=
    match f with
    | nil => s
    | (f::r) => AbsStar (AbsLeaf (AbsTreeId) (nth(v(f),#0)::(nth(h,#(f+1)))::(#size)::(map AbsConstVal (map NatValue fields))))
                           (build_Rs r size fields h s)
    end.

Fixpoint appendQuants2 {ev} {eq} {ff} {t} {ac} (h : nat) (s : @absState ev eq ff t ac) :=
    match h with
    | 0 => s
    | S h1 => AbsExistsT (appendQuants2 h1 s)
    end.

Fixpoint appendQuants {ev} {eq} {ff} {t} {ac} (n : nat) (h : nat) (s : @absState ev eq ff t ac) :=
    match n with
    | 0 => appendQuants2 h s
    | S n1 => AbsExistsT (appendQuants n1 h s)
    end.

Inductive constantValues {ev} {eq} {ff} : list (@absExp ev eq ff) -> list nat -> Prop :=
    | ConstantValuesNil : constantValues nil nil
    | ConstantValuesCons : forall r r' f field,
                           constantValues r r' ->
                           NatValue f = field ->
                           constantValues ((AbsConstVal field)::r) (f::r').

Hint Constructors constantValues.

Fixpoint createVarList {ev} {eq} {ff} start total :=
    match total with
    | 0 => nil
    | S(n) => (@AbsQVar ev eq ff start)::(@createVarList ev eq ff (start+1) n)
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
                                 (pushStateVar rs' size)))) ->
        state'' = (appendQuants2 size state') ->
        unfoldHeap root state state''.
*)
Inductive unfoldHeap {ev} {eq} {ff} {t} {ac} : @absExp ev eq ff -> @absState ev eq ff t ac -> @absState ev eq ff t ac -> Prop :=
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
                                 (pushStateVar rs' size)))) ->
        state'' = (appendQuants2 size state') ->
        unfoldHeap root state state''.

Ltac unfoldHeap root :=
    eapply UnfoldHeap;[
        (compute; reflexivity) |
        (instantiate (5 := root); solveSPickElement) |
        auto |
        (compute; reflexivity) |
        (compute; reflexivity) |
        (compute; reflexivity) ].

Theorem unfold_pre {ev} {eq} {ff} {t} {ac} : forall P P' c Q res root,
    @unfoldHeap ev eq ff t ac root P P' ->
    {{P'}}c{{Q,res}} ->
    {{P}}c{{Q,res}}.
Proof. admit. Qed.

Theorem unfoldSum {ev} {eq} {ff} {t} {ac} : forall l h e sum bbb lbbb state ee v,
        lbbb = length bbb ->
        ee = replaceExpVar lbbb v e ->
        @absEval ev eq ff (fst state) bbb (v<<<<(h++++#1))=NatValue 1 ->
        ((@realizeState ev eq ff t ac (SUM(range(l,h),e,sum)) bbb state) <->
                    (@realizeState ev eq ff t ac (AbsExistsT (AbsExistsT
                                      (SUM(range(l,v),addExpVar lbbb (addExpVar lbbb e),v(lbbb)) **
                                      (SUM(range(v++++#1,h),addExpVar lbbb (addExpVar lbbb e),v(lbbb+1))) **
                                       [sum====(v(lbbb)++++v(lbbb+1))++++ee]))) bbb state)).
Proof. admit. Qed.




