(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * AbsExecute.v
 * This file contains the basic hoare triple definition and many auxiliary theorems
 * and definitions related to forward propagation.
 *
 * Some key definitions:
 *     absExecute
 *     hoare_triple
 *     strengthenPost
 *     assign
 *     basic_assign
 *     load_traverse
 *     load
 *     store
 *     new_thm
 *     delete_thm
 *     if_statement
 *     while
 *     mergeStates
 *
 **********************************************************************************)

Require Import Omega.
Require Export SfLib.
Require Export ImpHeap.
Require Export AbsState.
Require Export PickElement.
Require Export AbsStateInstance.
Require Export Tactics.
Require Export Classical.
Require Export FunctionalExtensionality.

(* ***************************************************************************
 *
 * absExecute is the top level predicate that defines what execution of a
 * statement does to the abstract state.
 *
 * Parameters:
 *     ff - function specifications (see ceval in ImpHeap.v)
 *     c - command being executed (see ImpHeap.v)
 *     s - AbsState before execution
 *     s' - AbsState after execution
 *     r - result (see ceval in ImpHeap.v)
 *
 * The intuition behind this definition is that if s is true before executing
 * c, then s' will be true afterwards.  realizeState is used to relate
 * the abstract states to the concrete states and ceval is used to relate
 * the pre- and post- concrete states.
 *
 ***************************************************************************)

  Fixpoint In {A:Type} (a:A) (l:list A) : Prop :=
    match l with
      | nil => False
      | b :: m => b = a \/ In a m
    end.

Definition absExecute (ff : functions) (c : com) (s : absState) (s' : absState) (r : list absExp) (s'' : absState)  (exc : id -> (absExp * absState)) : Prop :=
    forall st st' i x, 
        realizeState s nil st ->
        ((exists st', exists r, ceval ff st c st' r) /\
         ((ceval ff st c st' NoResult -> realizeState s' nil st') \/
          (ceval ff st c st' (Return x) -> (forall rx, In rx r -> absEval (fst st') nil rx = NatValue x /\ realizeState s'' nil st')) \/
          (ceval ff st c st' (Exception i x) -> (absEval (fst st') nil (fst (exc i)) = NatValue x /\ realizeState (snd (exc i)) nil st')))).


Fixpoint evalList env el vl : Prop :=
    match (el,vl) with
    | (nil,nil) => True
    | (ef::er,vf::vr) => absEval env nil ef = vf /\ evalList env er vr
    | (_,_) => False
    end.

(*
 * mergeReturnStates specifies where states need to be merged at the end of processing an if-then-else
 *)
Definition mergeReturnStates (Q1 : absState) (Q2 : absState) (Q : absState) (R1 : list absExp) (R2 : list absExp) (R : list absExp) :=
    (forall s v, realizeState Q1 nil s -> evalList (fst s) R1 v-> (realizeState Q nil s /\ evalList (fst s) R v)) /\
    (forall s v, realizeState Q2 nil s -> evalList (fst s) R2 v-> (realizeState Q nil s /\ evalList (fst s) R v)).

(* Our Hoare triple notation is based on the absExecute definition *)
Definition hoare_triple (P : absState) c (Q : absState) r Qr exc :=
           absExecute (fun x => fun y => fun z => fun a => fun b => False) c P Q r Qr exc.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q (#0) AbsNone (fun x => (#0,AbsNone))) (at level 90).

Notation "{{ P }} c {{ Q 'return' rr 'with' QQ }}" := (hoare_triple P c Q rr QQ (fun x => (#0,AbsNone))) (at level 90).

(* **************************************************************************
 *
 * Post condition strengthening
 *
 * **************************************************************************)

Fixpoint equivEvalList env el1 el2 : Prop :=
    match (el1,el2) with
    | (nil,nil) => True
    | (ef::er,vf::vr) => absEval env nil ef = absEval env nil vf /\ equivEvalList env er vr
    | (_,_) => False
    end.

Theorem strengthenPost : forall (P : absState) c Q r Q' QQ QQ' r',
    {{ P }} c {{ Q return r with QQ }} ->
    (forall s, realizeState Q nil s -> realizeState Q' nil s) ->
    (forall s, realizeState QQ nil s -> realizeState QQ' nil s) ->
    (forall s, realizeState QQ nil s -> realizeState QQ' nil s ->
        equivEvalList (fst s) r r' ) ->
    {{ P }} c {{ Q' return r' with QQ' }}.
Proof. admit.
    (*unfold hoare_triple. unfold absExecute. intros.

    assert (forall st st' : state,
    realizeState P nil st ->
    (exists (st'0 : state) (r : result),
       ceval
         (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
          False) st c st'0 r)).
    intros.
    assert ((exists (st'0 : state) (r : result),
       ceval
         (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
          False) st0 c st'0 r) /\
    (ceval
       (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
        False) st0 c st' r -> realizeState Q nil st')).
    eapply H. apply H2. inversion H3. apply H4.

    assert (forall st st' : state,
    realizeState P nil st -> (ceval
       (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
        False) st c st' r -> realizeState Q nil st')).
    intros.
    assert ((exists (st'00 : state) (r : result),
       ceval
         (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
          False) st0 c st'00 r) /\
    (ceval
       (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
        False) st0 c st'0 r -> realizeState Q nil st'0)).
    eapply H. apply H3. inversion H5. apply H7. apply H4.

    split.

    eapply H2. apply st'. apply H1.

    intros. apply H0. eapply H3. apply H1. apply H4.*)
Admitted.

(* **************************************************************************
 *
 * Theorem for SKIP
 *
 * **************************************************************************)

Theorem skip_thm : forall (P:absState) r,
    {{ P }}SKIP{{ P return r with AbsNone }}.
Proof. admit. Admitted.

(* **************************************************************************
 *
 * Theorem for RETURN
 *
 * **************************************************************************)

Theorem return_thm : forall (P:absState) e r,
    r = convertToAbsExp e ->
    {{ P }}RETURN e{{ AbsNone return (r::nil) with P }}.
Proof. admit. Admitted.

(* **************************************************************************
 *
 * Theorems for statement composition
 *
 * **************************************************************************)
Theorem compose : forall (P:absState) c1 P' c2 Q R r1 r2 R' Q' rm,
    {{ P }} c1 {{ Q return r1 with P' }} ->
    {{ Q }} c2 {{ R return r2 with Q' }} ->
    mergeReturnStates P' Q' R' r1 r2 rm ->
    {{ P }} c1;c2 {{ R return rm with R' }}.
Proof. admit.
    (*unfold hoare_triple. unfold absExecute. intros.

    assert (forall st st' : state,
    realizeState P nil st ->
    (exists (st'0 : state) (r : result),
       ceval
         (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
          False) st c1 st'0 r)).
    intros.
    assert ((exists (st'0 : state) (r : result),
       ceval
         (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
          False) st0 c1 st'0 r) /\
    (ceval
       (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
        False) st0 c1 st' NoResult -> realizeState P' nil st')).
    eapply H. apply H3. inversion H4. apply H5.

    assert (forall st st' : state,
    realizeState P nil st -> (ceval
       (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
        False) st c1 st' NoResult -> realizeState P' nil st')).
    intros.
    assert ((exists (st'00 : state) (r : result),
       ceval
         (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
          False) st0 c1 st'00 r) /\
    (ceval
       (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
        False) st0 c1 st'0 NoResult -> realizeState P' nil st'0)).
    eapply H. apply H4. inversion H6. apply H8. apply H5.

    assert (forall st st' : state,
    realizeState P' nil st ->
    (exists (st'0 : state) (r : result),
       ceval
         (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
          False) st c2 st'0 r)).
    intros.
    assert ((exists (st'0 : state) (r : result),
       ceval
         (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
          False) st0 c2 st'0 r) /\
    (ceval
       (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
        False) st0 c2 st' r -> realizeState Q nil st')).
    eapply H1. eapply H5. inversion H6. apply H7.

    assert (forall st st' : state,
    realizeState P' nil st -> (ceval
       (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
        False) st c2 st' r -> realizeState Q nil st')).
    intros.
    assert ((exists (st'00 : state) (r : result),
       ceval
         (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
          False) st0 c2 st'00 r) /\
    (ceval
       (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
        False) st0 c2 st'0 r -> realizeState Q nil st'0)).
    eapply H1. apply H6. inversion H8. apply H10. apply H7.

    split.

    assert (realizeState P nil st). apply H2.

    eapply H3 in H2.
    inversion H2. subst. inversion H9. destruct x0. eapply H5 in H4.
    inversion H4. inversion H10.
    eapply ex_intro. eapply ex_intro. eapply CESeq1. eapply H9. eapply H11.
    eapply x.
    eapply H7. eapply H9.
    eapply ex_intro. eapply ex_intro.
    eapply CESeq2. apply H9.
    eapply ex_intro. eapply ex_intro. eapply CESeq3. apply H9. apply st.

    intros.

    (inversion H7; subst; clear H7). apply H0 in H12. eapply H6 in H12.
    apply H12. apply H15. apply H2.

    assert ((Return v)=NoResult). eapply H. apply H14. inversion H7.
    assert (Exception name val=NoResult). eapply H. apply H14. inversion H7.*)
Admitted.

(* **************************************************************************
 *
 * Theorems for assignment
 *
 ****************************************************************************)

(*
 *  The intent of the next several definitions is to build up a concept of
 *  a valid expression.  The informal idea is that if an AbsExp expression 'e'
 *  is valid with respect to an AbsState 's', then the result of evaluating
 *  the expression for any set of variable assignments which satisfy the
 *  's' will be a NatValue (and not a NoValue or anything else).
 *)

(*
 * This function identifies key variables in an expression.  If all of these
 * variables are defined in the state (meaning that they have a NatValue rather
 * than NoValue), then the result of evaluating the expression will be a
 * NatValue.  If the result 'None' is returned, then no such set of key
 * variables can be determined.
 *)
Fixpoint keyVariables (e : absExp) : option (list id) := 
    match e with
    | (AbsFun (AbsPlusId) (l::r::nil)) =>
            match (keyVariables l,keyVariables r) with
            | (Some l,Some r) => Some (l++r)
            | _ => None
            end
    | (AbsFun (AbsMinusId) (l::r::nil)) =>
            match (keyVariables l,keyVariables r) with
            | (Some l,Some r) => Some (l++r)
            | _ => None
            end
    | (AbsFun (AbsTimesId) (l::r::nil)) =>
            match (keyVariables l,keyVariables r) with
            | (Some l,Some r) => Some (l++r)
            | _ => None
            end
    | (AbsFun (AbsEqualId) (l::r::nil)) =>
            match (keyVariables l,keyVariables r) with
            | (Some l,Some r) => Some (l++r)
            | _ => None
            end
    | (AbsFun (AbsLessId) (l::r::nil)) =>
            match (keyVariables l,keyVariables r) with
            | (Some l,Some r) => Some (l++r)
            | _ => None
            end
    | (AbsFun (AbsMemberId) (l::_::nil)) => keyVariables l
    | (AbsFun (AbsIncludeId) (l::_::nil)) => keyVariables l
    | (AbsFun (AbsNotId) (l::nil)) => keyVariables l
    | (AbsVar i) => Some (i::nil)
    | (AbsConstVal (NatValue x)) => Some nil
    | _ => None
    end.

Fixpoint is_kv (x : id) (kv : list id) :=
   match kv with
   | nil    => false
   | (a::b) => if beq_id x a then true else is_kv x b
   end.

Definition is_key_variable (x : id) (kv : option (list id)) :=
   match kv with
   | None => false
   | Some y => is_kv x y
   end.

(*
 * This definition determines whether an AbsState 's' defines a constraint that
 * requires the variable 'id' to have an assigned value.  The rule used here is that
 * 's' is required to be assigned if it is a key variable in either the first expression
 * of an AbsPredicate or TREE or either the first or second predicate in an AbsCell.
 *)
Fixpoint basicVarAssigned (s : absState) id : bool :=
   match s with
   | AbsStar s1 s2 => if basicVarAssigned s1 id then true else basicVarAssigned s2 id
   | AbsExistsT s => basicVarAssigned s id
   | AbsExists l s => basicVarAssigned s id
   (*| AbsAll i l s => basicVarAssigned s id*)
   (*| AbsEach l s => basicVarAssigned s id*)
   | AbsEmpty => false
   | AbsLeaf (AbsPredicateId) (p::nil) => is_key_variable id (keyVariables p)
   | AbsLeaf (AbsCellId) (f::s::nil) => if beq_absExp f (AbsVar id) then true else beq_absExp s (AbsVar id)
   | AbsLeaf (AbsTreeId) (f::_) => beq_absExp f (AbsVar id)
   | _ => false
   end.

Fixpoint getRoot (s : absState) : absState :=
    match s with
    | AbsExistsT s => getRoot s
    | _ => s
    end.

(*
 * VarAssigned is a little more powerful rule for picking out variables that are
 * required to be assigned a value.  In contains all of the rules of
 * basicVarAssigned plus a rule stating that if there is a predicate making the
 * variable equal to some other expression and that expression is the root of a
 * TREE, then the variable must be assigned.  Note that the something else might
 * be an AbsQVar which is not covered by keyVariables.
 *)
Inductive varAssigned : absState -> id -> Prop :=
  | VarAssignedBasic : forall s v , basicVarAssigned s v = true ->
                                    varAssigned s v
  | VarAssignedPredicate1 : forall s v xx e a b c yy r,
                            r = getRoot s ->
                            spickElement r ([!!v ==== e]) xx ->
                            spickElement xx (TREE(e,a,b,c)) yy ->
                            varAssigned s v.

Hint Constructors varAssigned.

(*
 * A Valid expression is one in which the VarAssigned predicate holds for
 * each of the key variables.
 *)
Definition validExpression
                           (s : absState)
                           (e : absExp) :=
                                 forall x vars,
                                 keyVariables e <> None /\
                                 (Some vars = keyVariables e ->
                                 In x vars ->
                                 varAssigned s x).

Theorem quantifyExp :
                    forall (x : absExp) (e:env) v val ee vars,
                    val = NatValue (e v) ->
                    absEval (override e v ee) (val::vars) (quantifyAbsVar x 0 0 v) =
                    absEval e vars x.
Proof. admit.
    (*intro x. induction x using abs_ind'.

    crunch.

    crunch. remember (beq_id id v). destruct b. crunch. crunch. unfold override. crunch.
    crunch.

    assert (forall (e : env) (v : SfLibExtras.id) (val : @Value ev) (ee : nat) vars,
     (map
     (absEval (override e v ee)
        (NatValue (e v) :: vars)) (map (fun x : absExp => quantifyAbsVar x v) l)) =
     (map (absEval e vars) l)).
         induction l.
         crunch.
         crunch. rewrite H0. rewrite IHl. crunch. crunch. crunch. crunch.

     crunch.
     unfold quantifyAbsVar. fold (@quantifyAbsVar ev eq f).
     crunch. rewrite H0. crunch. crunch. apply (NatValue 0).*)
Admitted.

Theorem quantifyExpList :
                    forall (l : list absExp) (e:env) x v val vars,
                    val = NatValue (e v) ->
                    (map (absEval (override e v x) (val::vars))
                         (map (fun x0 => quantifyAbsVar x0 0 0 v) l))=
                    (map (absEval e vars) l).
Proof. admit.
    (*induction l.
        crunch.
        crunch. erewrite quantifyExp. erewrite IHl. crunch. crunch. crunch.*)
Admitted.

Theorem mapFirsts {t} :
        forall rl l v x,
        @allFirsts (@Value t) state rl l -> allFirsts rl (map (fun ss => (fst ss,(override (fst (snd ss)) v x, snd (snd ss)))) l).
Proof.
    induction rl.
    crunch. inversion H. crunch.
    crunch. inversion H. subst. clear H. crunch. apply AFCons. apply IHrl. crunch.
Qed.

Theorem mapSeconds {t} :
    forall sl l v x,
    @allSeconds state (@Value t) sl l ->
    allSeconds
        (map (fun s => (override (fst s) v x,snd s)) sl)
        (map
            (fun ss : Value * (env * heap) =>
                (fst ss, (override (fst (snd ss)) v x, snd (snd ss)))) l).
Proof.
    induction sl.
        crunch. inversion H. subst. crunch.
        intros. inversion H. subst. clear H. crunch. eapply ASCons. eapply IHsl.
        crunch.
Qed.

Theorem mapFoldCompose :
    forall states v x (st : state),
    fold_compose states st ->
    fold_compose
         (map (fun s : env * heap => (override (fst s) v x, snd s)) states)
         (override (fst st) v x, snd st).
Proof.
    induction states.
        crunch. inversion H. crunch. eapply FCNil.

        crunch. inversion H. subst. clear H. eapply FCCons.
            eapply IHstates. crunch.
            unfold concreteCompose in H4. crunch.
            unfold concreteCompose. crunch. rewrite <- H. crunch.
            rewrite H1. crunch.
Qed.

Theorem mapProp :
        forall l v x y,
                 In y (map
                      (fun ss : (@Value unit) * (env * heap) =>
                       (fst ss, (override (fst (snd ss)) v x, snd (snd ss)))) l) ->
                 (exists y', (y = (fst y',(override (fst (snd y')) v x, snd (snd y'))) /\ In y' l)).
Proof.
    induction l.
        crunch.

        crunch. inversion H. subst. clear H. crunch. destruct a. crunch. destruct p.
        crunch. apply ex_intro with (x := (v0, (e, h))). crunch.
        assert (exists y', y = (fst y', (override (fst (snd y')) v x, snd (snd y'))) /\
            (In y' l)). eapply IHl. crunch.
        crunch. apply ex_intro with (x := x0). crunch.
Qed.

Theorem envProp'' :
    forall states s e h, In s states -> fold_compose states (e,h) -> fst s = e.
Proof.
    induction states.
        crunch.

        crunch. inversion H. subst. clear H.
            inversion H0. subst. clear H0. unfold concreteCompose in H4. crunch.
            subst. clear H. inversion H0. subst. clear H0. eapply IHstates. crunch.
            instantiate (1 := (snd rstate)). unfold concreteCompose in H5. crunch.
            destruct rstate. crunch.
Qed.

Theorem envProp''' {t1} {t2} :
    forall states s l, @allSeconds t1 t2 states l -> In s l -> In (snd s) states.
Proof.
    induction states.
        crunch. inversion H. subst. crunch.

        intros. crunch. inversion H. subst. clear H. inversion H0. subst. clear H0.
        left. crunch. right. eapply IHstates. crunch. crunch.
Qed.

Theorem envProp {t} :
    forall xl l (states : list state) st,
    In xl l -> @allSeconds state (@Value t) states l -> fold_compose states st -> (fst st = fst (snd xl)).
Proof.
    intros. erewrite <- envProp'' with (e := (fst st)) (s := (snd xl)) (states := states).
    crunch.
    eapply envProp'''. crunch. crunch. instantiate (1 := snd st). destruct st.
    crunch.
Qed.

Theorem quantify1gen :
                    forall (P : absState) state v x val vars,
                    val = NatValue (fst state v) ->
                    realizeState P vars state -> realizeState (quantifyAbsVarState P 0 0 v) (val::vars)
                                            (override (fst state) v x, snd state).
Proof. admit.
    (*intro P. induction P.

    crunch. unfold quantifyAbsVarState. fold (@quantifyAbsVarState ev eq f t ac).
    inversion H0. subst. clear H0. eapply RSExists. crunch. erewrite quantifyExp.
    unfold env_p in H3. crunch. crunch.
    unfold env_p in H3. crunch.
    apply ex_intro with (x := x0).
    crunch. apply IHP. crunch. crunch.

    crunch. unfold quantifyAbsVarState. fold (@quantifyAbsVarState ev eq f t ac).
    inversion H0. subst. clear H0. eapply RSExistsU. crunch.
    apply ex_intro with (x := x0).
    crunch. apply IHP. crunch. crunch.

    crunch. unfold quantifyAbsVarState. fold (@quantifyAbsVarState ev eq f t ac).
    inversion H0. subst. clear H0. eapply RSAll. crunch. erewrite quantifyExp.
    unfold env_p in H3. crunch. crunch.
    unfold env_p in H3. crunch.
    crunch. apply IHP. crunch. apply H6. *crunch?* crunch.

    crunch. unfold quantifyAbsVarState. fold (@quantifyAbsVarState ev eq f t ac).
    inversion H0. subst. clear H0. eapply RSEach. crunch. erewrite quantifyExp.
    unfold env_p in H3. crunch. crunch.
    eapply mapFirsts. crunch.
    crunch. unfold env_p in H3.
    eapply mapSeconds. crunch.
    unfold env_p in H3. crunch.
    eapply mapProp in H. crunch.
    eapply IHP. crunch.
    erewrite envProp. crunch. crunch. crunch. crunch.
    eapply H6. destruct x1. *crunch?* crunch.
    eapply mapFoldCompose. crunch.

    crunch. inversion H0. subst. clear H0. eapply RSCompose.
    eapply IHP1.
    instantiate (1 := s1). unfold concreteCompose in H6. crunch.
    assert (fst state v = fst s1 v).
    rewrite <- H1. reflexivity.
    rewrite H4. crunch. crunch.
    eapply IHP2.
    instantiate (1 := s2). unfold concreteCompose in H6. crunch.
    assert (fst state v = fst s2 v).
    rewrite <- H. rewrite <- H1. reflexivity.
    rewrite H4. crunch.
    crunch.
    unfold concreteCompose in H6. crunch.
    unfold concreteCompose. crunch.
    instantiate (1 := x).
    instantiate (1 := x).
    assert (override (fst s1) v x = override (fst s2) v x).
    rewrite H. reflexivity. crunch.
    assert (override (fst state) v x = override (fst s1) v x).
    rewrite <- H1. reflexivity. crunch.

    crunch. inversion H0. subst. clear H0. eapply RSOrComposeL.
    eapply IHP1.
    reflexivity. apply H4.
    subst. clear H0. eapply RSOrComposeR.
    eapply IHP2.
    reflexivity. apply H4.

    crunch. inversion H0. subst. clear H0. eapply RSEmpty.
        intros. simpl. apply H.

    crunch. inversion H0. subst. clear H0. eapply RSR. simpl. rewrite quantifyExpList.
    crunch. crunch. apply H5.

    crunch. inversion H0. subst. clear H0.
    eapply RSAccumulate.
    simpl. rewrite quantifyExp. apply H6.
    crunch.
    simpl. reflexivity. unfold env_p in H8.
    apply H8.

    simpl. rewrite quantifyExp. unfold env_p in H6.
 apply H6.
    simpl in H5.
    remember (fst state v). destruct o.
        rewrite quantifyExpList.
 rewrite quantifyExpList. 2:apply H5.

 unfold quantifyAbsVarState. fold (@quantifyAbsVarState ev eq f t ac).
        unfold instantiateState. fold (@instantiateState ev eq f t ac).
    inversion H0. subst. clear H0.
    eapply RSR. crunch. rewrite quantifyExpList. crunch. crunch.

    crunch. inversion H0.*)
Admitted.

Theorem quantify1 :
                    forall (P : absState) state v x val bindings,
                    val = NatValue (fst state v) ->
                    realizeState P bindings state -> realizeState (quantifyAbsVarState P 0 0 v) (val::bindings)
                                            (override (fst state) v x, snd state).
Proof.
    crunch. eapply quantify1gen. crunch. crunch.
Qed.

Theorem absEvalSimp : forall (e : absExp) n (st : state) v x bindings,
        n = fst st v ->
        (absEval (override (fst st) v x) ((NatValue n)::bindings)
                 (quantifyAbsVar e 0 0 v)) =
        (absEval (fst st) bindings e).
Proof.
    (*induction e using abs_ind'.

    crunch.

    crunch. remember (beq_id id v). destruct b. unfold override. crunch. unfold override. crunch.

    crunch.

    assert (forall (n : nat) (st : state) (v : SfLibExtras.id) (x : nat) bindings,
        n = fst st v ->
        (map (absEval (override (fst st) v x) ((NatValue n)::bindings))
                (map (fun x0 : absExp => quantifyAbsVar x0 v) l)) =
        (map (absEval (fst st) bindings) l)).
        induction l. crunch.
        crunch.
        rewrite IHl. crunch. rewrite H0. crunch. crunch. crunch. crunch. crunch.
        rewrite H0. crunch. crunch. *) admit.
Admitted.

Theorem absEvalSimp2 : forall (e : absExp) (st : state) v x bindings,
        0 = fst st v ->
        (absEval (override (fst st) v x) ((NatValue 0)::bindings)
                 (quantifyAbsVar e 0 0 v)) =
        (absEval (fst st) bindings e).
Proof. admit.
    (*induction e using abs_ind'.

    crunch.

    crunch. remember (beq_id id v). destruct b. unfold override. crunch. unfold override. crunch.

    crunch.

    rewrite <- H. reflexivity.

    simpl. unfold override. crunch. crunch. crunch.

    assert (forall (n : nat) (st : state) (v : SfLibExtras.id) (x : nat) bindings,
        0 = fst st v ->
        (map (absEval (override (fst st) v x) ((NatValue 0)::bindings))
                (map (fun x0 : absExp => quantifyAbsVar x0 v) l)) =
        (map (absEval (fst st) bindings) l)).
        induction l. crunch.
        crunch.
        rewrite IHl. rewrite H1. crunch. crunch. crunch. apply 0. crunch. rewrite H1. crunch. 
        apply 0. crunch.*)
Admitted.

Theorem existsEvalDecompose_a :
    forall e (a : absExp) a0 i bindings,
    (i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) ->
    (exists x : nat,
        (absEval e bindings (AbsFun (Id i) (a :: a0 :: nil))) = NatValue x) ->
    (exists x : nat, (absEval e bindings a)= NatValue x).
Proof.
    (*crunch.

    unfold supportsBasicFunctionality in H. unfold supportsFunctionality in H.
    crunch.

    unfold absEval in H2. simpl in H2. fold (@absEval ev eq f) in H2.
    erewrite H1 in H2. Focus 3. reflexivity. simpl in H2.

    remember (absEval e bindings a). destruct v.
        apply ex_intro with (x := n). crunch.
        remember (absEval e bindings a0). destruct v.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
    omega. *)
Admitted.

Theorem existsEvalDecompose_b :
    forall e (a : absExp) a0 i bindings,
    (i = 2 \/ i = 3 \/ i = 4 \/ i=5 \/ i=6) ->
    (exists x : nat,
        (absEval e bindings (AbsFun (Id i) (a :: a0 :: nil))) = NatValue x) ->
    (exists x : nat, (absEval e bindings a0)= NatValue x).
Proof.
    (*crunch.

    unfold supportsBasicFunctionality in H. unfold supportsFunctionality in H.
    crunch.

    unfold absEval in H2. simpl in H2. fold (@absEval ev eq f) in H2.
    erewrite H1 in H2. Focus 3. reflexivity. simpl in H2.

    remember (absEval e bindings a0). destruct v.
        apply ex_intro with (x := n). crunch.
        remember (absEval e bindings a). destruct v.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
        remember (absEval e bindings a). destruct v.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
        remember (absEval e bindings a). destruct v.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
            caseAnalysis;inversion H2.
    omega.*)
    admit.
Admitted.

Theorem existsEvalDecompose :
    forall e (a : absExp) bindings i,
    (i = 10) ->
    (exists x : nat,
        (absEval e bindings (AbsFun (Id i) (a :: nil))) = NatValue x) ->
    (exists x : nat, (absEval e bindings a)= NatValue x).
Proof.
    (*crunch.

    unfold supportsBasicFunctionality in H. unfold supportsFunctionality in H.
    crunch.

    unfold absEval in H0. simpl in H0. fold (@absEval ev eq f) in H0.
    erewrite H1 in H0. Focus 3. reflexivity. simpl in H0.

    remember (absEval e bindings a). destruct v.
    apply ex_intro with (x := n). crunch.
    inversion H0. inversion H0. inversion H0.

    omega.*)
    admit.
Admitted.

(*Theorem defineWhenKeys {ev} {eq} {f} {t} {ac} {u} :
    forall (val : absExp) vars e v bindings,
    supportsBasicFunctionality ev eq f t ac u ->
    Some vars = keyVariables val ->
    In v vars ->
    (exists x, (absEval e bindings val)=(NatValue x)) ->
    None <> e v.
Proof.
    induction val using abs_ind'.

    crunch.

    crunch.
    destruct (e v). crunch. inversion H0. subst.

    crunch.

    crunch.

    destruct id. destruct n. crunch. destruct n. crunch. destruct n. destruct l. crunch.
    destruct l. crunch. destruct l. remember (keyVariables a). destruct o.
    remember (keyVariables a0). destruct o. crunch.
    inversion H2.
    eapply H1. crunch. crunch. crunch.
    eapply existsEvalDecompose_a. crunch. Focus 2. apply ex_intro with (x := x). crunch. crunch.
    eapply H. crunch. crunch. crunch.
    eapply existsEvalDecompose_b. crunch. Focus 2. apply ex_intro with (x := x). crunch. crunch.
    crunch. crunch. crunch.

    destruct n. destruct l. crunch. destruct l. crunch. destruct l.
    remember (keyVariables a). destruct o.
    remember (keyVariables a0). destruct o. crunch.
    inversion H2.
    eapply H1. crunch. crunch. crunch.
    eapply existsEvalDecompose_a. crunch. Focus 2. apply ex_intro with (x := x). crunch. crunch.
    eapply H. crunch. crunch. crunch.
    eapply existsEvalDecompose_b. crunch. Focus 2. apply ex_intro with (x := x). crunch. crunch.
    crunch. crunch. crunch.

    destruct n. destruct l. crunch. destruct l. crunch. destruct l.
    remember (keyVariables a). destruct o.
    remember (keyVariables a0). destruct o. crunch.
    inversion H2.
    eapply H1. crunch. crunch. crunch.
    eapply existsEvalDecompose_a. crunch. Focus 2. apply ex_intro with (x := x). crunch. right. crunch.
    eapply H. crunch. crunch. crunch.
    eapply existsEvalDecompose_b. crunch. Focus 2. apply ex_intro with (x := x). crunch. right. crunch.
    crunch. crunch. crunch.

    destruct n. destruct l. crunch. destruct l. crunch. destruct l.
    remember (keyVariables a). destruct o.
    remember (keyVariables a0). destruct o. crunch.
    inversion H2.
    eapply H1. crunch. crunch. crunch.
    eapply existsEvalDecompose_a. crunch. Focus 2. apply ex_intro with (x := x). crunch. right. right. crunch.
    eapply H. crunch. crunch. crunch.
    eapply existsEvalDecompose_b. crunch. Focus 2. apply ex_intro with (x := x). crunch. right. right. crunch.

    remember (keyVariables a). destruct o.
    remember (keyVariables a0). destruct o. crunch. inversion H. subst. clear H. inversion H5. subst. clear H5.
    eapply H3. crunch. crunch. crunch.
    eapply existsEvalDecompose_a. crunch. Focus 2. apply ex_intro with (x := x). crunch. right. right. crunch.
    crunch.

    remember (keyVariables a0). destruct o. crunch.
    eapply H. crunch. crunch. crunch.
    eapply existsEvalDecompose_b. crunch. Focus 2. apply ex_intro with (x := x). crunch. right. right. crunch.
    crunch. crunch.

    destruct n. destruct l. crunch. destruct l. crunch. destruct l.
    remember (keyVariables a). destruct o.
    remember (keyVariables a0). destruct o. crunch.
    inversion H2.
    eapply H1. crunch. crunch. crunch.
    eapply existsEvalDecompose_a. crunch. Focus 2. apply ex_intro with (x := x). crunch. right. right. right. crunch.
    eapply H. crunch. crunch. crunch.
    eapply existsEvalDecompose_b. crunch. Focus 2. apply ex_intro with (x := x). crunch. right. right. right. crunch.
    crunch. crunch. crunch.

    destruct n. destruct l. crunch. destruct l. crunch. destruct l.
    crunch.
    eapply H3. crunch. crunch. crunch.
    eapply existsEvalDecompose_a. crunch. Focus 2. apply ex_intro with (x := x). crunch. right. right. right. right. crunch.
    crunch.

    destruct n. destruct l. crunch. destruct l. crunch. destruct l.
    crunch.
    eapply H3. crunch. crunch. crunch.
    eapply existsEvalDecompose_a. crunch. Focus 2. apply ex_intro with (x := x). crunch. right. right. right. right. right. crunch.
    crunch.

    destruct n. crunch. destruct n. destruct l. crunch. destruct l. crunch.
    eapply H3. crunch. crunch. crunch.
    eapply existsEvalDecompose. crunch. Focus 2. apply ex_intro with (x := x). crunch.
    crunch.
    crunch. crunch. crunch.
Qed.

Theorem is_kv_thm : forall l v, is_kv v l = true -> In v l.
Proof.
    induction l.
    intros. inversion H.
    intros. unfold is_kv in H. remember (beq_id v a). destruct b. eapply beq_id_eq in Heqb.
    subst. simpl. left. reflexivity. simpl. right. eapply IHl. fold is_kv in H. crunch.
Qed.

Theorem validEval {ev} {eq} {f} {t} {ac} {u} :
        forall a v e x bindings,
               supportsBasicFunctionality ev eq f t ac u ->
               @absEval ev eq f e bindings a = @NatValue ev x ->
               is_key_variable v (keyVariables a)=true ->
               (None <> e v).
Proof.
    intros.

    remember (keyVariables a).  destruct o. eapply defineWhenKeys.
    crunch. eapply Heqo. inversion H1. apply is_kv_thm. crunch.
    eapply ex_intro. apply H0. inversion H1.
Qed.*)

(*Theorem validHasAssignBasic {ev} {eq} {f} {t} {ac} {u} :
        forall (P : @absState ev eq f t ac) v vars e h,
               supportsBasicFunctionality ev eq f t ac u ->
               realizeState P vars (e,h) ->
               basicVarAssigned P v = true ->
               (None <> e v).
Proof. adxxxmit.
    induction P.

    crunch. inversion H0. subst. clear H0. crunch. eapply IHP. crunch. crunch. crunch.

    crunch. inversion H0. subst. clear H0. crunch. eapply IHP. crunch. crunch. crunch.

    crunch.

    crunch.

    crunch. inversion H0. subst. clear H0. remember (basicVarAssigned P1 v).
        destruct b. inversion H8. crunch. destruct s1. destruct s2. crunch.
        eapply IHP1. crunch. crunch. crunch.
        destruct s1. destruct s2. crunch. inversion H8. crunch. eapply IHP2. crunch. crunch.
        crunch.

    crunch.

    crunch. inversion H. crunch.
    inversion H1. subst. clear H1.
    destruct i. destruct n. crunch. destruct n. crunch. destruct l. crunch. destruct l.
    inversion H0. subst. clear H0.
    eapply H5 in H13. 2:crunch. 2:crunch. inversion H13.
    remember (absEval e vars a). destruct v0.
    eapply validEval. crunch. instantiate (1 := n). rewrite Heqv0. reflexivity. crunch.
    inversion H0. inversion H0. inversion H0. inversion H9.

    destruct n. destruct l. crunch. inversion H0. subst. clear H0.
    crunch. eapply H5 in H13. 2:crunch. 2:crunch. inversion H13. subst. clear H13.
    destruct a. inversion H9. inversion H9. subst. clear H9.
    remember (beq_id i v). destruct b. eapply beq_id_eq in Heqb. subst.
    inversion H0. destruct (e v). crunch. inversion H11. crunch.
    inversion H9. inversion H9.

    destruct n. destruct l. crunch. destruct l. crunch. destruct l.

    inversion H0. subst. clear H0. eapply H5 in H13. 2:crunch. 2:crunch.
    inversion H13. subst. clear H13.

    destruct a. inversion H9. subst. clear H9.

        destruct a0. inversion H13. inversion H13. remember (beq_id i v). destruct b.
        eapply beq_id_eq in Heqb. subst. inversion H1. destruct (e v). crunch.
        inversion H14. crunch. inversion H13. inversion H13.

        crunch. remember (beq_id i v). destruct b. eapply beq_id_eq in Heqb. subst.
        destruct (e v). crunch. inversion H0.
        destruct a0. inversion H9. inversion H9. remember (beq_id i0 v). destruct b.
        eapply beq_id_eq in Heqb0. subst. inversion H1. destruct (e v). crunch.
        inversion H14. crunch. inversion H9. inversion H9.

        inversion H9.
        destruct a0. inversion H13. inversion H13. remember (beq_id i v). destruct b.
        eapply beq_id_eq in Heqb. subst. inversion H1. destruct (e v). crunch.
        inversion H15. crunch. inversion H13. inversion H13.

        inversion H9. subst. clear H9.
        destruct a0. inversion H13. inversion H13. remember (beq_id i0 v). destruct b.
        eapply beq_id_eq in Heqb. subst. inversion H1. destruct (e v). crunch.
        inversion H14. crunch. inversion H13. inversion H13.

        crunch. crunch. crunch.

    intros. inversion H0.
Qed.*)

(*Theorem validPickElement {ev} {eq} {f} {t} {ac} {u} :
    forall (s : @absState ev eq f t ac) st v val xx vars bindings,
    supportsBasicFunctionality ev eq f t ac u ->
    realizeState s bindings st ->
    spickElement s ([val]) xx ->
    Some vars = keyVariables val ->
    In v vars ->
    None <> fst st v.
Proof. admxxit.
    crunch.

    destruct st.

    assert (forall (s : @absState ev eq f t ac) xx p,
            spickElement s p xx ->
            p = ([val]) ->
            (exists h, realizeState s bindings (e, h)) ->
            In v vars ->
            None <> e v).
    intros. induction H4.

        apply IHspickElement. crunch.

        crunch. inversion H5. subst. clear H5.
        unfold concreteCompose in H13. destruct s1. destruct s2. crunch.
        apply ex_intro with (x := h0). crunch.

        apply IHspickElement. crunch.

        crunch. inversion H5. subst. clear H5.
        unfold concreteCompose in H13. destruct s1. destruct s2. crunch.
        apply ex_intro with (x := h1). crunch.

        inversion H5.

        crunch. inversion H4. subst. clear H4.

        inversion H. crunch.

        destruct i. eapply H9 in H12. Focus 2. crunch.

        crunch. inversion H5. subst. clear H5. inversion H12. subst. clear H12. crunch.

        eapply defineWhenKeys. crunch. crunch. crunch.
        apply ex_intro with (x := e0).
            remember (@absEval ev eq f e bindings val). destruct v0.
            crunch. inversion H5. subst. rewrite Heqv0. reflexivity.
            inversion H5. inversion H5. inversion H5.

        inversion H5. omega. inversion H5.

    crunch. eapply H4. crunch. crunch. eapply ex_intro. crunch. crunch.
Qed.*)

(*Theorem validHasAssign1 {ev} {eq} {f} {t} {ac} {u} :
    forall st v (P: @absState ev eq f t ac) bindings,
        supportsBasicFunctionality ev eq f t ac u ->
        realizeState P bindings st ->
        varAssigned P v ->
        None <> fst st v.
Proof.
    crunch.

    induction H1.

    destruct st.
    eapply validHasAssignBasic. crunch. crunch. crunch.
    admxxit. * Note that this is special case that is only meaningful if VarAssignedPredicate1
              is used in validating the application of the assign tactic *
Qed.*)
(*    eapply validPickElement. crunch. crunch. crunch. rewrite H2. crunch. crunch.
Qed.*)

Theorem validKeyVariablesSubterm :
    forall ff x l, keyVariables (AbsFun ff l)<>None ->
                   ff <> AbsMemberId -> ff <> AbsIncludeId ->
                   In x l -> keyVariables x<>None.
Proof. admit.
    (*crunch.

    destruct ff. destruct n. crunch. destruct n. crunch.
    destruct n. destruct l. crunch. destruct l. crunch.
    destruct l.

    remember (keyVariables a). destruct o. remember (keyVariables a0).
    destruct o. inversion H2. subst. clear H2. rewrite <- Heqo. crunch.
    inversion H3. subst. clear H3. rewrite <- Heqo0. crunch. inversion H4.

    crunch. crunch. crunch.

    destruct n. destruct l. crunch.  destruct l. crunch.
    destruct l.

    remember (keyVariables a). destruct o. remember (keyVariables a0).
    destruct o. inversion H2. subst. clear H2. rewrite <- Heqo. crunch.
    inversion H3. subst. clear H3. rewrite <- Heqo0. crunch. inversion H4.

    crunch. crunch. crunch.

    destruct n. destruct l. crunch.  destruct l. crunch.
    destruct l.

    remember (keyVariables a). destruct o. remember (keyVariables a0).
    destruct o. inversion H2. subst. clear H2. rewrite <- Heqo. crunch.
    inversion H3. subst. clear H3. rewrite <- Heqo0. crunch. inversion H4.

    crunch. crunch. crunch.

    destruct n. destruct l. crunch.  destruct l. crunch.
    destruct l.

    remember (keyVariables a). destruct o. remember (keyVariables a0).
    destruct o. inversion H2. subst. clear H2. rewrite <- Heqo. crunch.
    inversion H3. subst. clear H3. rewrite <- Heqo0. crunch. inversion H4.

    crunch. crunch. crunch.

    destruct n. destruct l. crunch.  destruct l. crunch.
    destruct l.

    remember (keyVariables a). destruct o. remember (keyVariables a0).
    destruct o. inversion H2. subst. clear H2. rewrite <- Heqo. crunch.
    inversion H3. subst. clear H3. rewrite <- Heqo0. crunch. inversion H4.

    crunch. crunch. crunch.

    destruct n. destruct l. elim H. reflexivity.  destruct l. crunch.
    destruct l.

    crunch. crunch.

    destruct n. crunch.

    destruct n. crunch. destruct n. destruct l. crunch.

    destruct l. inversion H2. subst. apply H. crunch.

    crunch. crunch. crunch.*)
Admitted.

Theorem keyVariablesSubset :
    forall ff x l v vars1 vars2, In x l ->
                                 keyVariables (AbsFun ff l) = Some vars1 ->
                                 ff <> AbsMemberId -> ff <> AbsIncludeId ->
                                 keyVariables x = Some vars2 -> In v vars2 -> In v vars1.
Proof. admit.
    (*crunch.
    destruct ff. destruct n. crunch. destruct n. crunch. destruct n.

    destruct l. crunch. destruct l. crunch. destruct l.

    remember (keyVariables a). destruct o. remember (keyVariables a0).
    destruct o. crunch. inversion H. subst. rewrite <- Heqo in H3. crunch.
    crunch. crunch. crunch. crunch.

    destruct n. destruct l. crunch. destruct l. crunch. destruct l.

    remember (keyVariables a). destruct o. remember (keyVariables a0).
    destruct o. crunch. inversion H. subst. rewrite <- Heqo in H3. crunch.
    crunch. crunch. crunch. crunch.

    destruct n. destruct l. crunch. destruct l. crunch. destruct l.

    remember (keyVariables a). destruct o. remember (keyVariables a0).
    destruct o. crunch. inversion H. subst. rewrite <- Heqo in H3. crunch.
    crunch. crunch. crunch. crunch.

    destruct n. destruct l. crunch. destruct l. crunch. destruct l.

    remember (keyVariables a). destruct o. remember (keyVariables a0).
    destruct o. crunch. inversion H. subst. rewrite <- Heqo in H3. crunch.
    crunch. crunch. crunch. crunch.

    destruct n. destruct l. crunch. destruct l. crunch. destruct l.

    remember (keyVariables a). destruct o. remember (keyVariables a0).
    destruct o. crunch. inversion H. subst. rewrite <- Heqo in H3. crunch.
    crunch. crunch. crunch. crunch.

    destruct n. destruct l. crunch. destruct l. crunch. destruct l.

    remember (keyVariables a). destruct o. remember (keyVariables a0).
    destruct o. crunch. inversion H. subst. rewrite <- Heqo in H3. crunch.
    crunch. crunch. crunch. crunch.

    destruct n. destruct l. crunch. destruct l. crunch. destruct l.

    crunch. crunch.

    destruct n.

    crunch.

    destruct n. crunch. destruct l. crunch. destruct l.
    inversion H. subst. clear H. rewrite H3 in H0. crunch. crunch. crunch.
    crunch. crunch.*)
Admitted.

Theorem validExpressionProp :
    forall (P : absState) i l x,
        In x l ->
        i<>AbsMemberId -> i<>AbsIncludeId ->
        validExpression P (AbsFun i l) ->
        validExpression P x.
Proof.
    (*crunch. unfold validExpression in H2.
    unfold validExpression. intros. split.
    eapply validKeyVariablesSubterm.
        apply H2. apply (Id 0). crunch apply nil. crunch?
    crunch. crunch. crunch.

    remember (keyVariables (AbsFun i l)). destruct o. 
    intros. eapply H2. reflexivity.
    eapply keyVariablesSubset. crunch. rewrite Heqo. reflexivity.
    crunch. crunch. rewrite <- H3. reflexivity. crunch.
    assert (@None (list id) <> None). eapply H2. apply x0. apply vars. crunch
    elim H3. reflexivity.*) admit.
Admitted. (* Crunch problems *)

(*Theorem validHasAssign {ev} {eq} {f} {t} {ac} {u} :
    forall st v (P: @absState ev eq f t ac) bindings,
        supportsBasicFunctionality ev eq f t ac u ->
        realizeState P bindings st ->
        validExpression P (!!v) ->
        None <> fst st v.
Proof.
    unfold validExpression. intros. eapply validHasAssign1.
    crunch. crunch. eapply H1.
    unfold keyVariables. crunch. crunch.
Qed.*)

Fixpoint noMemberExpression (e : absExp) :=
    match e with
    | AbsFun x l => (x <> AbsMemberId /\ x <> AbsIncludeId /\
                     (fold_right (fun x y => x /\ y) True (map noMemberExpression l)))
    | _ => True
    end.

(*Theorem noMemberPropagate {ev} {eq} {f} :
        forall ff l x, noMemberExpression (@AbsFun ev eq f ff l) -> In x l ->
                       noMemberExpression x.
Proof.
    induction l.

    crunch.

    crunch.
        inversion H0. crunch.

        eapply IHl. crunch. crunch.
Qed.*)

(*Theorem absEvalSimp2 {ev} {eq} {f} {t} {ac} {u} :
                     forall y (st : state) v x (e : absExp)
                            (P : @absState ev eq f t ac) bindings,
        supportsBasicFunctionality ev eq f t ac u ->
        None = fst st v ->
        realizeState P bindings st ->
        validExpression P e ->
        noMemberExpression e ->
        (absEval (override (fst st) v x) (y::bindings)
                 (quantifyAbsVar e v)) =
        (absEval (fst st) bindings e).
Proof.
    induction e using abs_ind'.

    crunch.

    crunch.
    remember (beq_id id v). destruct b. apply beq_id_eq in Heqb. subst. crunch.
        crunch.
        assert (None <> fst st v). eapply validHasAssign.
        crunch. crunch. crunch. rewrite H0 in H4. *crunch* crunch.
        intros.
        crunch. unfold override. rewrite beq_id_comm. rewrite <- Heqb. crunch.

    crunch.

    intros. unfold quantifyAbsVar. fold (@quantifyAbsVar ev eq f).
    unfold instantiateExp. fold (@instantiateExp ev eq f).

    simpl.

    assert (forall (l : list absExp), (map (absEval (override (fst st) v x) (y::bindings))
        (map (fun x0 : absExp => quantifyAbsVar x0 v) l))=
         (map (fun x0 => absEval (override (fst st) v x) (y::bindings) (quantifyAbsVar x0 v)) l)).
        crunch.
        induction l0.
            crunch.

            crunch. rewrite IHl0. crunch.

    rewrite H5.

    assert (forall x, In x l -> noMemberExpression x).
        intros. eapply noMemberPropagate. crunch. crunch. 
    assert (forall (e : absExp), In e l ->
        (absEval (override (fst st) v x) (y::bindings)
                 (quantifyAbsVar e v)) =
        (absEval (fst st) bindings e)). crunch.
        eapply reduceAll in H. Focus 2. crunch.
        erewrite H with (P := P) (bindings := bindings). crunch. crunch. crunch. crunch.
        eapply validExpressionProp. crunch. crunch. crunch. crunch. apply H6. crunch.

    assert (forall ll, subset ll l -> (map
     (fun x0 : absExp =>
      absEval (override (fst st) v x) (y::bindings)
        (quantifyAbsVar x0 v)) ll) =
     (map (absEval (fst st) bindings) ll)).

        induction ll. crunch.

        unfold subset. fold (@subset absExp). crunch.
        rewrite H7. rewrite IHll. crunch. crunch. crunch.

    rewrite H8. reflexivity.

    assert (forall t (x : list t), x = (nil++x)).
        crunch.
    rewrite H9. apply subsetAppend.
Qed.*)

(*Theorem absEvalHasNatValue {ev} {eq} {f} {t} {ac} {u} :
                        forall e (st : state) bindings
                               (P : @absState ev eq f t ac),
        supportsBasicFunctionality ev eq f t ac u ->
        validExpression P e ->
        realizeState P bindings st ->
        (exists x, NatValue x = (absEval (fst st) bindings e)).
Proof.
    adxmit.
Qed.*)

Theorem absEvalAeval :
                        forall e (st : state) bindings,
        (NatValue (aeval st e)) =
        (absEval (fst st) bindings (convertToAbsExp e)).
Proof.
    admit.
    (*induction e.

    crunch. intros. simpl. reflexivity.

    crunch.
    inversion H.
    crunch. erewrite H0. 3:reflexivity.
    erewrite <- IHe1. erewrite <- IHe2. crunch. crunch. crunch. crunch.

    crunch.
    inversion H.
    crunch. erewrite H0. 3:reflexivity.
    erewrite <- IHe1. erewrite <- IHe2. crunch. crunch. crunch. crunch.

    crunch.
    inversion H.
    crunch. erewrite H0. 3:reflexivity.
    erewrite <- IHe1. erewrite <- IHe2. crunch. crunch. crunch. crunch.

    crunch.
    inversion H.
    crunch. erewrite H0. 3:reflexivity.
    erewrite <- IHe1. erewrite <- IHe2.
    crunch. crunch.
    unfold basicEval. destruct (beq_nat (aeval st e1) (aeval st e2)). crunch. crunch.
    crunch. crunch. crunch.

    crunch.
    inversion H.
    crunch. erewrite H0. 3:reflexivity.
    erewrite H0. 3:reflexivity.
    erewrite <- IHe1. erewrite <- IHe2. unfold basicEval. simpl.
       destruct (ble_nat (aeval st e1) (aeval st e2)). crunch. crunch. crunch. crunch. crunch.
       crunch.

    crunch.
    inversion H.
    crunch. erewrite H0. 3:reflexivity.
    erewrite <- IHe1. erewrite <- IHe2. crunch.
    unfold basicEval. destruct (beq_nat (aeval st e1) 0). crunch. crunch.
    crunch. crunch. crunch.

    crunch.
    inversion H.
    crunch. erewrite H0. 3:reflexivity.
    erewrite <- IHe1. erewrite <- IHe2. crunch.
    unfold basicEval. destruct (beq_nat (aeval st e1) 0). crunch. crunch. crunch. crunch.
        crunch.

    crunch.
    inversion H.
    crunch. erewrite H0. 3:reflexivity.
    erewrite <- IHe. crunch.
    unfold basicEval. destruct (beq_nat (aeval st e) 0). crunch. crunch.
    crunch. crunch.*)
Admitted.

Theorem absPredicateCompose :
    forall P p state bindings,
    realizeState P bindings state ->
    realizeState (AbsLeaf AbsPredicateId (p::nil)) bindings (fst state,empty_heap) ->
    realizeState (AbsStar ([p]) P) bindings state.
Proof.
    (*crunch. inversion H. crunch. inversion H1. subst. eapply H5 in H13.
    2:crunch. crunch. inversion H13. subst. clear H13. crunch.
    eapply RSCompose. crunch. crunch. unfold concreteCompose. crunch.
    left. unfold empty_heap. crunch. crunch.*) admit.
Admitted.

(*Theorem validExpressionValue {ev} {eq} {f} {t : id -> list (@Value ev) -> heap -> Prop} {ac} {u} :
        forall e (P : @absState ev eq f t ac) st bindings,
        supportsBasicFunctionality ev eq f t ac u ->
        validExpression P e ->
        realizeState P bindings st ->
        (exists x, absEval (fst st) bindings e=NatValue x).
Proof.
    induction e using abs_ind'.

    crunch. unfold validExpression in H0. crunch. destruct c. eapply ex_intro. crunch.
        crunch. assert (@None (list id) <> None). apply H0. apply (Id 0). apply nil. crunch.
        crunch. assert (@None (list id) <> None). apply H0. apply (Id 0). apply nil. crunch.
        crunch. assert (@None (list id) <> None). apply H0. apply (Id 0). apply nil. crunch.

    crunch. unfold validExpression in H0. crunch.
    assert (None <> fst st id). eapply validHasAssign1.
        crunch. crunch. eapply H0. crunch. crunch.
    remember (fst st id). destruct o. apply ex_intro with (x := n). crunch.
    elim H2. crunch.

    crunch. unfold validExpression in H0. unfold keyVariables in H0.
    assert (@None (list id) <> None).
    apply H0. apply (Id 0). apply nil. crunch.

    crunch. remember H1. clear Heqv.
    unfold validExpression in H1. unfold keyVariables in H1. fold (@keyVariables ev eq f) in H1.

    destruct id. destruct n.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct n.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct n. destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.

    crunch. inversion H0. crunch. erewrite H4. 3:crunch.
    assert (exists x, absEval (fst st) bindings a = NatValue x).
        eapply H3. crunch. crunch. crunch. eapply validExpressionProp. 4:apply v.
        crunch. intro X. inversion X. *crunch* intro X. inversion X. crunch.
    assert (exists x, absEval (fst st) bindings a0 = NatValue x).
        eapply H. crunch. crunch. crunch. eapply validExpressionProp. 4:apply v.
        crunch. intro X. inversion X. *crunch* intro X. inversion X. crunch.
    crunch. rewrite H13. rewrite H12.
    crunch. eapply ex_intro. crunch. crunch.

    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct n. destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.

    crunch. inversion H0. crunch. erewrite H4. 3:crunch.
    assert (exists x, absEval (fst st) bindings a = NatValue x).
        eapply H3. crunch. crunch. crunch. eapply validExpressionProp. 4:apply v.
        crunch. intro X. inversion X. *crunch* intro X. inversion X. crunch.
    assert (exists x, absEval (fst st) bindings a0 = NatValue x).
        eapply H. crunch. crunch. crunch. eapply validExpressionProp. 4:apply v.
        crunch. intro X. inversion X. *crunch* intro X. inversion X. crunch.
    crunch. rewrite H13. rewrite H12.
    crunch. eapply ex_intro. crunch. crunch.

    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct n. destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.

    crunch. inversion H0. crunch. erewrite H4. 3:crunch.
    assert (exists x, absEval (fst st) bindings a = NatValue x).
        eapply H3. crunch. crunch. crunch. eapply validExpressionProp. 4:apply v.
        crunch. intro X. inversion X. *crunch* intro X. inversion X. crunch.
    assert (exists x, absEval (fst st) bindings a0 = NatValue x).
        eapply H. crunch. crunch. crunch. eapply validExpressionProp. 4:apply v.
        crunch. intro X. inversion X. *crunch* intro X. inversion X. crunch.
    crunch. rewrite H13. rewrite H12.
    crunch. eapply ex_intro. crunch. crunch.

    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct n. destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.

    crunch. inversion H0. crunch. erewrite H4. 3:crunch.
    assert (exists x, absEval (fst st) bindings a = NatValue x).
        eapply H3. crunch. crunch. crunch. eapply validExpressionProp. 4:apply v.
        crunch. intro X. inversion X. *crunch* intro X. inversion X. crunch.
    assert (exists x, absEval (fst st) bindings a0 = NatValue x).
        eapply H. crunch. crunch. crunch. eapply validExpressionProp. 4:apply v.
        crunch. intro X. inversion X. *crunch* intro X. inversion X. crunch.
    crunch. rewrite H13. rewrite H12.
    crunch. unfold basicEval. destruct (beq_nat x0 x). eapply ex_intro. crunch. eapply ex_intro. crunch. crunch.

    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct n. destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.

    crunch. inversion H0. crunch. erewrite H4. 3:crunch.
    assert (exists x, absEval (fst st) bindings a = NatValue x).
        eapply H3. crunch. crunch. crunch. eapply validExpressionProp. 4:apply v.
        crunch. intro X. inversion X. *crunch* intro X. inversion X. crunch.
    assert (exists x, absEval (fst st) bindings a0 = NatValue x).
        eapply H. crunch. crunch. crunch. eapply validExpressionProp. 4:apply v.
        crunch. intro X. inversion X. *crunch* intro X. inversion X. crunch.
    crunch. rewrite H13. rewrite H12.
    crunch. unfold basicEval. destruct (ble_nat x x0). eapply ex_intro. crunch. eapply ex_intro. crunch. crunch.

    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct n. destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.

    crunch. inversion H0. crunch. erewrite H4. 3:crunch.
    assert (exists x, absEval (fst st) bindings a = NatValue x).
        eapply H3. crunch. crunch. crunch.
    crunch. rewrite H12. crunch. unfold basicEval.
    destruct (Rmember x
          (convertAbsValue (fun _ : ev => tt) (absEval (fst st) bindings a0))).
    eapply ex_intro. crunch. eapply ex_intro. crunch. crunch.

    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct n. destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.

    crunch. inversion H0. crunch. erewrite H4. 3:crunch.
    assert (exists x, absEval (fst st) bindings a = NatValue x).
        eapply H3. crunch. crunch. crunch.
    crunch. rewrite H12. crunch. unfold basicEval.
    destruct (Rinclude x
          (convertAbsValue (fun _ : ev => tt) (absEval (fst st) bindings a0))).
    eapply ex_intro. crunch. eapply ex_intro. crunch. crunch.

    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct n.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct n. destruct l.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    destruct l.

    crunch. inversion H0. crunch. erewrite H. 3:crunch.
    assert (exists x, absEval (fst st) bindings a = NatValue x).
        eapply H3. crunch. crunch. crunch.
    crunch. rewrite H11. crunch. unfold basicEval.
    destruct (beq_nat x 0).
    eapply ex_intro. crunch. eapply ex_intro. crunch. crunch.

    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
    assert (@None (list id) <> None). apply H1. apply (Id 0). apply nil. crunch.
Qed.*)

Theorem noMemberTheorem : forall e, noMemberExpression (convertToAbsExp e).
Proof.
    induction e.

    crunch. crunch. crunch. intro X. inversion X. (*crunch*) intro X. inversion X.
    crunch. intro X. inversion X. intro X. inversion X.
    crunch. intro X. inversion X. intro X. inversion X.
    crunch. intro X. inversion X. intro X. inversion X.
    crunch. intro X. inversion X. intro X. inversion X.
    crunch. intro X. inversion X. intro X. inversion X.
    crunch. intro X. inversion X. intro X. inversion X.
    crunch. intro X. inversion X. intro X. inversion X.
    crunch. intro X. inversion X. intro X. inversion X.
Qed.

Theorem validExpressionValue :
    forall e env b, exists x, absEval env b (convertToAbsExp e)=NatValue x.
Proof.
    (*induction e.

    intros. eapply ex_intro. simpl. reflexivity.

    intros. simpl. destruct (env i). eapply ex_intro. reflexivity. eapply ex_intro. reflexivity.

    intros. simpl. inversion x. erewrite H. 3:reflexivity. 2:omega.
    assert (exists x : nat, absEval env b (convertToAbsExp e1) = NatValue x).
    eapply IHe1. 
    assert (exists x : nat, absEval env b (convertToAbsExp e2) = NatValue x).
    eapply IHe2.
    inversion H1. subst. clear H1. inversion H2. subst. clear H2. rewrite H1. rewrite H3.
        simpl. eapply ex_intro. reflexivity.

    intros. simpl. inversion x. erewrite H. 3:reflexivity. 2:omega.
    assert (exists x : nat, absEval env b (convertToAbsExp e1) = NatValue x).
    eapply IHe1. 
    assert (exists x : nat, absEval env b (convertToAbsExp e2) = NatValue x).
    eapply IHe2.
    inversion H1. subst. clear H1. inversion H2. subst. clear H2. rewrite H1. rewrite H3.
        simpl. eapply ex_intro. reflexivity.

    intros. simpl. inversion x. erewrite H. 3:reflexivity. 2:omega.
    assert (exists x : nat, absEval env b (convertToAbsExp e1) = NatValue x).
    eapply IHe1. 
    assert (exists x : nat, absEval env b (convertToAbsExp e2) = NatValue x).
    eapply IHe2.
    inversion H1. subst. clear H1. inversion H2. subst. clear H2. rewrite H1. rewrite H3.
        simpl. eapply ex_intro. reflexivity.

    intros. simpl. inversion x. erewrite H. 3:reflexivity. 2:omega.
    assert (exists x : nat, absEval env b (convertToAbsExp e1) = NatValue x).
    eapply IHe1. 
    assert (exists x : nat, absEval env b (convertToAbsExp e2) = NatValue x).
    eapply IHe2.
    inversion H1. subst. clear H1. inversion H2. subst. clear H2. rewrite H1. rewrite H3.
        simpl. unfold basicEval. remember (beq_nat x0 x1). destruct b0.
        eapply ex_intro. reflexivity. eapply ex_intro. reflexivity.

    intros. simpl. inversion x. erewrite H. 3:reflexivity. 2:omega. erewrite H. 3:reflexivity. 2:omega.
    assert (exists x : nat, absEval env b (convertToAbsExp e1) = NatValue x).
    eapply IHe1. 
    assert (exists x : nat, absEval env b (convertToAbsExp e2) = NatValue x).
    eapply IHe2.
    inversion H1. subst. clear H1. inversion H2. subst. clear H2. rewrite H1. rewrite H3.
        simpl. unfold basicEval. remember (ble_nat x0 x1). destruct b0.
        simpl. eapply ex_intro. reflexivity. simpl. eapply ex_intro. reflexivity.

    intros. simpl. inversion x. erewrite H. 3:reflexivity. 2:omega.
    assert (exists x : nat, absEval env b (convertToAbsExp e1) = NatValue x).
    eapply IHe1. 
    assert (exists x : nat, absEval env b (convertToAbsExp e2) = NatValue x).
    eapply IHe2.
    inversion H1. subst. clear H1. inversion H2. subst. clear H2. rewrite H1. rewrite H3.
        simpl. unfold basicEval. remember (beq_nat x0 0). destruct b0.
        simpl. eapply ex_intro. reflexivity. simpl. eapply ex_intro. reflexivity.

    intros. simpl. inversion x. erewrite H. 3:reflexivity. 2:omega.
    assert (exists x : nat, absEval env b (convertToAbsExp e1) = NatValue x).
    eapply IHe1. 
    assert (exists x : nat, absEval env b (convertToAbsExp e2) = NatValue x).
    eapply IHe2.
    inversion H1. subst. clear H1. inversion H2. subst. clear H2. rewrite H1. rewrite H3.
        simpl. unfold basicEval. remember (beq_nat x0 0). destruct b0.
        simpl. eapply ex_intro. reflexivity. simpl. eapply ex_intro. reflexivity.

    intros. simpl. inversion x. erewrite H. 3:reflexivity. 2:omega.
    assert (exists x : nat, absEval env b (convertToAbsExp e) = NatValue x).
    eapply IHe. 
    inversion H1. subst. clear H1. rewrite H2.
        simpl. unfold basicEval. remember (beq_nat x0 0). destruct b0.
        simpl. eapply ex_intro. reflexivity. simpl. eapply ex_intro. reflexivity.*)
    admit.
Admitted.

Theorem assign  :
    forall P v e Q,
        Q = (AbsUpdateVar P v (convertToAbsExp e)) ->
        {{ P }} v ::= e {{ Q return (#0::nil) with AbsNone }}.
Proof. admit.
    (*crunch. unfold hoare_triple. unfold absExecute. crunch.
    eapply ex_intro. eapply ex_intro.
    eapply CEAss.
    crunch.
    inversion H0. subst. clear H0.

    eapply RSExistsU. eapply ex_intro. crunch.
    eapply absPredicateCompose. crunch.
    eapply quantify1. crunch. crunch.
    eapply RSR. crunch.

    inversion x. crunch. eapply H1. instantiate (1 := ((NatValue 1)::nil)).
    Focus 2.
    assert (forall s x y, override s x y x = y).
    unfold override. crunch. rewrite <- beq_id_refl. crunch.
    rewrite H5.

    erewrite H0. Focus 3. crunch.
    erewrite absEvalSimp.
    assert (exists x, (absEval (fst st) nil (@convertToAbsExp ev eq f e)=@NatValue ev x)).
    eapply validExpressionValue. inversion H7. subst. clear H7.
    simpl. unfold basicEval.
    remember (absEval (fst st) nil (convertToAbsExp e)).
    destruct v0. simpl.
    remember (beq_nat (aeval st e) n). destruct b. reflexivity.
    inversion H8. subst. clear H8.
        crunch. erewrite <- absEvalAeval in Heqv0. inversion Heqv0.  subst.
        rewrite <- beq_nat_refl in Heqb. inversion Heqb.

    apply x.
    inversion H8. inversion H8. inversion H8.
    reflexivity. omega.
    apply Heqo.

    simpl.
    assert (exists x, (absEval (fst st) nil (@convertToAbsExp ev eq f e)=@NatValue ev x)).
    eapply validExpressionValue. inversion H7. subst. clear H7.

    unfold basicEval.
    erewrite absEvalSimp2.
    remember (absEval (fst st) nil (convertToAbsExp e)).
    destruct v0. simpl. inversion H8. subst. clear H8.
    remember (beq_nat (aeval st e) x0). destruct b. reflexivity.
    erewrite <- absEvalAeval in Heqv0. inversion Heqv0. subst. clear Heqv0.
    rewrite <- beq_nat_refl in Heqb. inversion Heqb.
    apply x.

    inversion H8. inversion H8. inversion H8.
    crunch. crunch.
    eapply BTStatePredicate.
        intro X. inversion X.
        crunch. crunch.
Grab Existential Variables.
    apply x. *)
Admitted.

Definition id_fun {e} := fun (x:e) => x.


(*Theorem sbasic1 :
    forall x, convertAbsValue (fun _ : unit => tt) x=x.
Proof. intros. induction x using value_ind'. simpl. reflexivity. simpl.
 reflexivity. simpl. destruct v. reflexivity.
    simpl.   assert ((map (convertAbsValue (fun _ : unit => tt)) l) = l).
        induction l. simpl. reflexivity. simpl. simpl in H. inversion H. rewrite H0.
        rewrite IHl. reflexivity. apply H1.
    rewrite H0. reflexivity.
Qed.

Theorem sbasic2 :
    forall l, (map (convertAbsValue (fun _ : unit => tt)) l) = l.
Proof. induction l. simpl. reflexivity.
    simpl. rewrite sbasic1. rewrite IHl. reflexivity.
Qed. 

Theorem sbasic3 :
    forall c (e:absExp), (convertAbsExp e)=e.
Proof.
    intros. induction e using abs_ind'.
    unfold convertAbsExp. rewrite sbasic1. reflexivity.
    unfold convertAbsExp. reflexivity.
    unfold convertAbsExp. reflexivity.
    simpl. assert ((map (convertAbsExp (fun _ : unit => tt)) l)=l).
           induction l. simpl. reflexivity.
           simpl. simpl in H. inversion H. rewrite H0. rewrite IHl. reflexivity. apply H1.
    rewrite H0. reflexivity.
Qed.*)

(*Theorem sbasic : supportsBasicFunctionality unit eq_unit unitEval basicState (@basicAccumulate unit eq_unit unitEval) tt.
Proof.
    unfold supportsBasicFunctionality. unfold supportsFunctionality.
    split. intros. unfold unitEval. rewrite sbasic2 in H0. subst. rewrite sbasic1. reflexivity.
    split. intros. rewrite sbasic2 in H0. subst. rewrite sbasic1. reflexivity.
    split. intros. rewrite sbasic2 in H0. subst. apply H.
    split. intros. rewrite sbasic2 in H0. subst. apply H.
    split. intros. rewrite sbasic2. rewrite sbasic2. rewrite sbasic1. rewrite sbasic3. apply H.
    intros. rewrite sbasic2. rewrite sbasic2. rewrite sbasic1. rewrite sbasic3. apply H. admit.
Admitted.*)

(*Hint Resolve sbasic.*)

(*Definition basicAssign := @assign unit eq_unit unitEval basicState basicAccumulate tt.*)

(* **************************************************************************
 *
 * Theorems and definitions for new
 *
 ****************************************************************************)

Fixpoint add_cells (n : nat) (base : absState) : absState :=
    match n with
    | 0 => base
    | (S n1) => (AbsStar (v(0)++++#n1 |-> v(n)) (add_cells n1 base))
    end.

Fixpoint n_quant (n : nat) (s : absState) : absState :=
    match n with
    | 0 => s
    | (S n1) => n_quant n1 (AbsExistsT s)
    end.

Fixpoint pushNState (s : absState) (n : nat) :=
    match n with
    | 0 => s
    | S n1 => pushNState (addStateVar 0 s) n1
    end.

Theorem new_thm : forall P v size Q,
    Q = n_quant (S size) (AbsExistsT (add_cells size
                                         (AbsStar ([!!v====v(0)])
                                          (quantifyAbsVarState (pushNState P (S size)) 1 0 v)))) ->
    {{ P }} (NEW v,(ANum size)) {{ Q return (#0::nil) with AbsNone }}.
Proof.
    admit.
Admitted.

Ltac new_thm :=
    eapply new_thm;simpl;reflexivity.

Theorem del_thm : forall P v size Q vv,
    vv = convertToAbsExp v ->
    Q = AbsMagicWand P (n_quant (S size) (add_cells size ([vv====v(0)]))) ->
    ((exists s, realizeState P nil s) -> (exists s, realizeState Q nil s)) ->
    {{ P }} (DELETE v,(ANum size)) {{ Q return (#0::nil) with AbsNone }}.
Proof. admit. Admitted.

Ltac del_thm :=
    eapply del_thm;simpl;reflexivity.


(* **************************************************************************
 *
 * Theorems and definitions for store
 *
 ****************************************************************************)

Fixpoint replaceRoot (s : absState) (r : absState) : absState :=
    match s with
    | AbsExistsT s => AbsExistsT (replaceRoot s r)
    | _ => r
    end.

Fixpoint rootCount (s : absState) : nat :=
    match s with
    | AbsExistsT s => S(rootCount s)
    | _ => 0
    end.

Theorem store : forall P ll l v vv,
    ll = (convertToAbsExp l) ->
    vv = convertToAbsExp v ->
    (forall s n, realizeState P nil s -> ((NatValue n)=(absEval (env_p s) nil ll) -> (heap_p s) n<>None)) ->
    {{ P }} CStore l v {{ (AbsUpdateLoc P ll vv) return (#0::nil) with AbsNone }}.
Proof. admit. Admitted.

Ltac store := eapply store;
              [(simpl;reflexivity)|(simpl;reflexivity)|solveSPickElement|
               (simpl;reflexivity)].

Theorem store_array : forall P r r' (bb : absExp) base ll l v vv var Q size c bb,
    r = getRoot P ->
    c = rootCount P ->
    ll = convertToAbsExp l ->
    bb = convertToAbsExp base ->
    vv = convertToAbsExp v ->
    spickElement r (ARRAY(bb, size, (AbsQVar var))) r' ->
    (forall ss, realizeState P nil ss -> absEval (fst ss) nil (ll <<<< size)=NatValue 1) ->
    Q = (AbsExistsT (replaceRoot P (AbsLeaf (Id 4) ((addExpVar 0 bb)::(addExpVar 0 size)::(AbsQVar (var+1))::nil) ** (AbsLeaf (Id 1) ((vv====(nth(AbsQVar (var+1),(addExpVar 0 ll))))::nil)) ** (replaceStateExp (AbsQVar (var+1)) (replacenth(AbsQVar (var+1),(addExpVar 0 ll),(AbsQVar 0))) (addStateVar 0 r'))))) ->
    {{ P }} CStore (base+++l) v {{ Q return (#0::nil) with AbsNone }}.
Proof. admit. Admitted.

(* **************************************************************************
 *
 * Theorems and definitions for load
 *
 ****************************************************************************)

Inductive UnfContext :=
    | UnfCExistsT : UnfContext
    | UnfCUpdateVar : id -> absExp -> UnfContext
    | UnfCUpdateWithLoc : id -> absExp -> UnfContext
    | UnfCUpdateLoc : absExp -> absExp -> UnfContext
    | UnfCMagicWand : absState -> UnfContext
    | UnfCStar : absState -> UnfContext
    .

Fixpoint getRootTraceLoadTraverse (e:absExp) (s : absState) : option (absState * list UnfContext) :=
    match s with
    | AbsExistsT s => match getRootTraceLoadTraverse e s with
                      | Some (s,l) => Some (s,(UnfCExistsT::l))
                      | None => None
                      end
    | AbsUpdateVar s i v => if hasVarExp e i then None
                            else match getRootTraceLoadTraverse e s with
                                 | Some (s,l) => Some (s,((UnfCUpdateVar i v)::l))
                                 | None => None
                                 end
    | AbsUpdateWithLoc s i v => if hasVarExp e i then None
                                else match getRootTraceLoadTraverse e s with
                                     | Some (s,l) => Some (s,((UnfCUpdateWithLoc i v)::l))
                                     | None => None
                                     end
    | AbsStar x y => match x,y with
                     | ([a]),b => match getRootTraceLoadTraverse e b with
                                  | Some (s,l) => Some (s,(UnfCStar ([a]))::l)
                                  | None => None
                                  end
                     | b,([a]) => match getRootTraceLoadTraverse e b with
                                  | Some (s,l) => Some (s,(UnfCStar ([a]))::l)
                                  | None => None
                                  end
                     | _,_ => Some (s,nil)
                     end
    | AbsUpdateLoc s i v => None
    (*| AbsMagicWand a b => (UnfCMagicWand b)::(getUnfoldTrace a)*)
    | _ => Some (s,nil)
    end.

Fixpoint finishState (s : absState) (l : list (UnfContext)) :=
    match l with
    | UnfCExistsT::r => AbsExistsT (finishState s r)
    | (UnfCUpdateVar i v)::r => (AbsUpdateVar (finishState s r) i v)
    | (UnfCUpdateWithLoc i v)::r => AbsUpdateWithLoc (finishState s r) i v
    | (UnfCUpdateLoc i v)::r => AbsUpdateLoc (finishState s r) i v
    | (UnfCMagicWand d)::r => AbsMagicWand (finishState s r) d
    | (UnfCStar x)::r => AbsStar (finishState s r) (x)
    | nil => s
    end.
(*
 * This theorem creates a tactic that allows one to retain an inTree relationship after
 * an operation that causes one to traverse a pointer to a child node in a TREE type
 * data structure.  See the proof of loopInvariant for an example of this rule's use.
 *)
Theorem load_traverse : forall v (r:absState) r' r'' ff vve vv (PPP:absState) Q t root heap size fields,
    vv = convertToAbsExp vve ->
    Some (r,t) = getRootTraceLoadTraverse (AbsVar v) PPP ->
    spickElement r ([vv inTree heap]) r' ->
    spickElement r' (TREE(root,heap,size,fields)) r'' ->
    Q = AbsExistsT
    (finishState
                             (AbsStar
                                 ([(!!v)====#0 \\//
                                   (!!v) inTree (quantifyAbsVar (addExpVar 0 heap) 0 0 v)])
                                 (AbsStar
                                     ([nth(nth(quantifyAbsVar (find((addExpVar 0 heap),vv)) 0 0 v,#(ff+1)),#0)====(AbsVar v)])
                                     (quantifyAbsVarState r 0 0 v))) t) ->
    {{ PPP }} CLoad v (APlus vve (ANum ff)) {{ Q return (#0::nil) with AbsNone }}.
Proof. admit. Admitted.

Ltac load_traverse := eapply load_traverse;[
        (simpl; reflexivity) |
        (simpl; reflexivity) |
        solveSPickElement |
        solveSPickElement |
        (simpl; reflexivity)].

Fixpoint findCell (state : absState) (loc : absExp) :=
   match state with
   | AbsLeaf i (l::val::nil) => if beq_id i AbsCellId && beq_absExp l loc then Some val else None
   | AbsStar l r => match findCell l loc with
                       | Some v => Some v
                       | None => findCell r loc
                       end
   | _ => None
   end.

(*
 * load theorem.  This theorem allows one to propagate over a statement that loads a heap
 * cell value into a variable.  See the loopInvariant proof in TreeTraversal.v for an
 * example of this rule's use.
 *)
Theorem load : forall (P:absState) v loc ll,
    ll = (convertToAbsExp loc) ->
    {{ P }} CLoad v loc {{ (AbsUpdateWithLoc P v ll) return (#0::nil) with AbsNone }}.
Proof. admit. Admitted.

Theorem loadUpdateProp : forall (P:absState) v loc (Q:absState)  vv val,
    v<>vv ->
    {{ P }} CLoad v loc {{ Q return (#0::nil) with AbsNone }} ->
    {{ (AbsUpdateVar P vv val) }} CLoad v loc {{ (AbsUpdateVar Q vv val) return (#0::nil) with AbsNone }}.
Proof.
    admit.
Admitted.

Theorem load_array : forall P r r' (bb : absExp) base ll l v var Q size c bb,
    r = getRoot P ->
    c = rootCount P ->
    ll = convertToAbsExp l ->
    bb = convertToAbsExp base ->
    spickElement r (AbsLeaf (Id 4) (bb::size::(AbsQVar var)::nil)) r' ->
    (forall ss, realizeState P nil ss -> absEval (fst ss) nil (ll <<<< size)=@NatValue unit 1) ->
    Q = (AbsExistsT (replaceRoot P (AbsStar
                           ([(!!v)====(quantifyAbsVar (nth((AbsQVar var),ll)) 0 0 v)])
                           (quantifyAbsVarState r 0 0 v)))) ->
    {{ P }} CLoad v (base+++l) {{ Q return (#0::nil) with AbsNone }}.
Proof. admit. Admitted.

(* **************************************************************************
 *
 * Theorems for delete
 *
 ****************************************************************************)

Fixpoint removeCell (state : absState) (loc : absExp) :=
   match state with
   | AbsLeaf i (l::val::nil) => if beq_id AbsCellId i && beq_absExp l loc then Some AbsEmpty else None
   | AbsExistsT s => match removeCell s loc with
                         | Some x => Some (AbsExistsT x)
                         | None => None
                         end
   | AbsStar l r => match removeCell l loc with
                       | Some x => Some (AbsStar x r)
                       | None => match removeCell r loc with
                                 | Some x => Some (AbsStar l x)
                                 | None => None
                                 end
                       end
   | _ => None
   end.

Fixpoint removeCells (state : absState) (loc : absExp) (n : nat) :=
    match n with
    | 0 => Some state
    | S 0 => match removeCell state loc with
             | None => None
             | Some s => Some s
             end
    | S n1 => match (removeCell state (loc++++#n1)) with
                  | None => None
                  | Some s => removeCells s loc n1
                  end
    end.

(*
 * This is the rule for forward propagating over a DELETE statement.  See loopInvariant
 * in TreeTraversal.v for an example of this rule's use.
 *)
Theorem delete_thm :
    forall (P:absState) v (loc:absExp) (Q:absState) n exp nn,
    
    loc = convertAbsExp (convertToAbsExp v) ->
    AbsConstVal n = convertAbsExp (convertToAbsExp exp) ->
    Some Q = removeCells P loc nn ->
    n = NatValue nn ->
    {{ P }} DELETE v,exp {{ Q return (#0::nil) with AbsNone }}.
Proof. admit. Admitted.

(*Definition delete_thm_basic := @delete_thm unit eq_unit
                                           (@basicEval unit)
                                           (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)) tt.*)

(* **************************************************************************
 *
 * Theorems for if
 *
 ****************************************************************************)

Theorem cevalFalse : forall f r st st' b1 c1 c2,
      aeval st b1 = 0 ->
      ceval f st (CIf b1 c1 c2) st' r ->
      ceval f st c2 st' r.
Proof.
    admit.
    (*intros.  inversion H0. subst. rewrite H in H8. elim H8. reflexivity. subst. apply H9.*)
Admitted.

Theorem cevalTrue : forall f r st st' b1 c1 c2,
      aeval st b1 <> 0 ->
      ceval f st (CIf b1 c1 c2) st' r ->
      ceval f st c1 st' r.
Proof.
    intros. inversion H0. subst. apply H9. subst. rewrite H8 in H. elim H. reflexivity.
Qed.

(*
 * mergeStates specifies where states need to be merged at the end of processing an if-then-else
 *)
Definition mergeStates(Q1 : absState) (Q2 : absState) (Q : absState) :=
    (forall s, realizeState Q1 nil s -> realizeState Q nil s) /\
    (forall s, realizeState Q2 nil s -> realizeState Q nil s).

(*
 * Rule for propagating over an if-then-else
 *)
Theorem if_statement: forall (P:absState) Q1 Q2 Q Q1' Q2' Qm r1 r2 rm b l r,
    {{(AbsStar ([convertToAbsExp b]) P)}}l{{Q1 return r1 with Q1' }} ->
    {{(AbsStar ([~~(convertToAbsExp b)]) P)}}r{{Q2 return r2 with Q2' }} ->
    mergeReturnStates  Q1' Q2' Qm r1 r2 rm ->
    mergeStates Q1 Q2 Q ->
    {{P}}CIf b l r{{Q return rm with Qm}}.
Proof. admit.
    (*unfold hoare_triple. unfold mergeStates. unfold absExecute. intros. inversion H2. subst. clear H2.

    assert (forall (st st' : state), realizeState ([convertToAbsExp b] ** P) nil st ->
               (exists (st'0:state) (r:result),
                   ceval
                       (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
                            False) st l st'0 r)).
    intros.
    assert ((exists (st'0 : state) (r : result),
       ceval
         (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
          False) st0 l st'0 r) /\
    (ceval
       (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
        False) st0 l st' res -> realizeState Q1 nil st')).
    eapply H0. apply H2.

    inversion H6. subst. clear H6. apply H7.

    assert (forall st st' : state,
    realizeState ([convertToAbsExp b] ** P) nil st ->
    (ceval
       (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
        False) st l st' res -> realizeState Q1 nil st')).
    intros.
    assert ((exists (st'0 : state) (r : result),
       ceval
         (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
          False) st0 l st'0 r) /\
    (ceval
       (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
        False) st0 l st'0 res -> realizeState Q1 nil st'0)).
    eapply H0. apply H6.
    inversion H8. subst. clear H8. apply H10. apply H7.

    assert (forall st st' : state,
     realizeState ([~~ (convertToAbsExp b)] ** P) nil st ->
     (exists (st'0 : state) (r0 : result),
        ceval
          (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
           False) st r st'0 r0)).
    intros.
    assert ((exists (st'0 : state) (r0 : result),
        ceval
          (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
           False) st0 r st'0 r0) /\
     (ceval
        (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
         False) st0 r st'0 res -> realizeState Q2 nil st'0)).
    eapply H1. apply H7.

    inversion H8. subst. clear H8. apply H9.

    assert (forall st st' : state,
     realizeState ([~~ (convertToAbsExp b)] ** P) nil st ->
     (ceval
        (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
         False) st r st' res -> realizeState Q2 nil st')).
    intros.
    assert ((exists (st'0 : state) (r0 : result),
        ceval
          (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
           False) st0 r st'0 r0) /\
     (ceval
        (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
         False) st0 r st'0 res -> realizeState Q2 nil st'0)).
    eapply H1. apply H8.
    inversion H10. subst. clear H10. apply H12. apply H9.

    split.

    clear H6. clear H8.

    remember (aeval st b). destruct n.

    assert (
        (exists (st'0 : state) (r0 : result),
  ceval
    (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
     False) st r st'0 r0) ->
        (exists (st'0 : state) (r0 : result),
  ceval
    (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
     False) st (CIf b l r) st'0 r0)
    ).
    intros. inversion H6. subst. clear H6. inversion H8. subst. clear H8.
    eapply ex_intro. eapply ex_intro. apply CEIfFalse. rewrite Heqn. reflexivity. apply H6.

    eapply H6. eapply H7. apply st. eapply RSCompose. eapply RSR. unfold map. reflexivity.
    inversion H. subst. inversion H9. subst. clear H9. inversion H11. subst. clear H11.
    eapply H9. 3:omega. eapply BTStatePredicate.
    instantiate (1 := aeval st (ALnot b)). simpl. rewrite <- Heqn. unfold beq_nat. intro X. inversion X.

    instantiate (1:=(fst st,empty_heap)). simpl. unfold empty_heap. reflexivity.

    simpl.

    erewrite H8. rewrite <- Heqn. simpl. 2:omega. 2:simpl. 2:reflexivity.
    erewrite <- absEvalAeval. rewrite <- Heqn. simpl. reflexivity.
    apply H.

    apply H3. unfold concreteCompose. simpl.
    split. reflexivity. split. reflexivity. split. intros. left. unfold empty_heap. reflexivity.
    unfold compose_heaps. unfold empty_heap.

    eapply functional_extensionality. reflexivity.

    assert (
        (exists (st'0 : state) (r0 : result),
  ceval
    (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
     False) st l st'0 r0) ->
        (exists (st'0 : state) (r0 : result),
  ceval
    (fun (_ : id) (_ : state) (_ : list nat) (_ : state) (_ : result) =>
     False) st (CIf b l r) st'0 r0)
    ).
    intros. inversion H6. subst. clear H6. inversion H8. subst. clear H8.
    eapply ex_intro. eapply ex_intro. apply CEIfTrue. rewrite <- Heqn. intro X. inversion X. apply H6.

    eapply H6. eapply H2. apply st. eapply RSCompose. eapply RSR. unfold map. reflexivity.
    inversion H. subst. inversion H9. subst. clear H9. inversion H11. subst. clear H11.
    eapply H9. 3:omega. eapply BTStatePredicate.
    instantiate (1 := aeval st b). simpl. rewrite <- Heqn. intro X. inversion X.

    instantiate (1:=(fst st,empty_heap)). simpl. unfold empty_heap. reflexivity.

    simpl.

    rewrite <- Heqn. simpl.
    erewrite <- absEvalAeval. rewrite <- Heqn. simpl. reflexivity.
    apply H.

    apply H3. unfold concreteCompose. simpl.
    split. reflexivity. split. reflexivity. split. intros. left. unfold empty_heap. reflexivity.
    unfold compose_heaps. unfold empty_heap.

    eapply functional_extensionality. reflexivity.

    intros.

    remember (aeval st b). destruct n.

    apply H5. eapply H8.

    eapply RSCompose. eapply RSR. unfold map. reflexivity.

    inversion H. subst. inversion H11. subst. clear H11. inversion H13. subst. clear H13.
    eapply H11. 3:omega. eapply BTStatePredicate. instantiate (1:= aeval st (ALnot b)).
    simpl. rewrite <- Heqn. simpl. intro X. inversion X.

    instantiate (1 := (fst st,empty_heap)). simpl. unfold empty_heap. reflexivity.

    simpl.

    rewrite <- Heqn. simpl.

    erewrite <- absEvalAeval. rewrite <- Heqn. erewrite H10. 2:omega. 2:simpl. 2:reflexivity.
    simpl. reflexivity. apply H.
    apply H3. unfold concreteCompose. simpl.
    split. reflexivity. split. reflexivity. split. intros. left. unfold empty_heap. reflexivity.
    unfold compose_heaps. unfold empty_heap.

    eapply functional_extensionality. reflexivity.

    eapply cevalFalse. instantiate (1 := b). erewrite <- Heqn. reflexivity.
    eapply H9.

    apply H4. eapply H6.

    eapply RSCompose. eapply RSR. unfold map. reflexivity.

    inversion H. subst. inversion H11. subst. clear H11. inversion H13. subst. clear H13.
    eapply H11. 3:omega. eapply BTStatePredicate. instantiate (1:= aeval st b).
    simpl. rewrite <- Heqn. simpl. intro X. inversion X.

    instantiate (1 := (fst st,empty_heap)). simpl. unfold empty_heap. reflexivity.

    simpl.

    rewrite <- Heqn. simpl.

    erewrite <- absEvalAeval. rewrite <- Heqn. reflexivity.
    apply H.
    apply H3. unfold concreteCompose. simpl.
    split. reflexivity. split. reflexivity. split. intros. left. unfold empty_heap. reflexivity.
    unfold compose_heaps. unfold empty_heap.

    eapply functional_extensionality. reflexivity.

    eapply cevalTrue. instantiate (1 := b). erewrite <- Heqn. intro X. inversion X.
    eapply H9.*)
Admitted.

(* **************************************************************************
 *
 * Theorems for while
 *
 ****************************************************************************)


Theorem while_aux : forall c b ff (invariant: absState) res c1 st1 st1',
   (forall st st' res, realizeState (AbsStar ([convertToAbsExp b]) invariant) nil st ->
                       ceval ff st c st' res ->
                       realizeState invariant nil st') ->
    realizeState invariant nil st1 ->
    c1 = (WHILE b DO c LOOP) ->
    ceval ff st1 c1 st1' res ->
    realizeState (AbsStar (match res with | NoResult => [~~(convertToAbsExp b)] | _ => AbsEmpty end) invariant) nil st1'.
Proof.
    admit. (*intros. induction H3.

    inversion H2. inversion H2. inversion H2. inversion H2. inversion H2. inversion H2. inversion H2.
    inversion H2. inversion H2. inversion H2. inversion H2. inversion H2. subst. clear H2.

    eapply RSCompose. instantiate (1 := (fst st,empty_heap)).
    eapply RSR. simpl. inversion H. erewrite H2. reflexivity. omega. simpl. reflexivity.
    inversion H. inversion H4. inversion H6. eapply H7.
    eapply BTStatePredicate.
    Focus 3. simpl. unfold basicEval. erewrite <- absEvalAeval. simpl.
    remember (beq_nat (aeval st b) 0). destruct b0. simpl. reflexivity.
    apply beq_nat_neq in Heqb0. rewrite H3 in Heqb0. elim Heqb0. reflexivity.
    apply H.
    omega.
    intros. simpl. unfold empty_heap. reflexivity. omega. apply H1.
    unfold concreteCompose.
    split. simpl. reflexivity.
    split. simpl. reflexivity.
    split. intros. left. simpl. unfold empty_heap. reflexivity.
    unfold compose_heaps. simpl. apply functional_extensionality. intros. reflexivity.

    inversion H2. subst. clear H2.

    assert (realizeState ([convertToAbsExp b] ** invariant) nil st).
    eapply RSCompose. instantiate (1 := (fst st, empty_heap)).
    eapply RSR. simpl. unfold env_p. erewrite <- absEvalAeval. reflexivity. apply H.
    inversion H. inversion H4. inversion H6. eapply H7. 2:instantiate (1:=(NatValue _::nil)).
    2:simpl. 2:reflexivity.
    apply BTStatePredicate. apply H3.
    intros. simpl. unfold empty_heap. reflexivity. omega. apply H1.
    unfold concreteCompose.
    split. simpl. reflexivity.
    split. simpl. reflexivity.
    split. intros. left. simpl. unfold empty_heap. reflexivity.
    unfold compose_heaps. simpl. apply functional_extensionality. intros. reflexivity.
    eapply H0 in H2. Focus 2. eapply H3_.
    eapply IHceval2. apply H0. apply H2. reflexivity.

    inversion H2. subst. clear H2.
    eapply RSCompose. instantiate (1 := (fst st', empty_heap)).
    eapply RSEmpty. simpl. intros. unfold empty_heap. reflexivity. eapply H0.
    eapply RSCompose. instantiate (1 := (fst st,empty_heap)).
    eapply RSR. simpl. reflexivity. inversion H.  inversion H5. inversion H7.
    eapply H8.
    eapply BTStatePredicate.
    Focus 3. simpl. unfold basicEval. erewrite <- absEvalAeval. simpl. reflexivity.
    apply H.
    apply H3.
    intros. simpl. unfold empty_heap. reflexivity. omega. apply H1.
    unfold concreteCompose.
    split. simpl. reflexivity.
    split. simpl. reflexivity.
    split. intros. left. simpl. unfold empty_heap. reflexivity.
    unfold compose_heaps. simpl. apply functional_extensionality. intros. reflexivity.
    apply H4.
    unfold concreteCompose.
    split. simpl. reflexivity.
    split. simpl. reflexivity.
    split. intros. left. simpl. unfold empty_heap. reflexivity.
    unfold compose_heaps. simpl. apply functional_extensionality. intros. reflexivity.

    inversion H2. subst. clear H2.
    eapply RSCompose. instantiate (1 := (fst st', empty_heap)).
    eapply RSEmpty. simpl. intros. unfold empty_heap. reflexivity. eapply H0.
    eapply RSCompose. instantiate (1 := (fst st,empty_heap)).
    eapply RSR. simpl. reflexivity. inversion H.  inversion H5. inversion H7.
    eapply H8.
    eapply BTStatePredicate.
    Focus 3. simpl. unfold basicEval. erewrite <- absEvalAeval. simpl. reflexivity.
    apply H.
    apply H3.
    intros. simpl. unfold empty_heap. reflexivity. omega. apply H1.
    unfold concreteCompose.
    split. simpl. reflexivity.
    split. simpl. reflexivity.
    split. intros. left. simpl. unfold empty_heap. reflexivity.
    unfold compose_heaps. simpl. apply functional_extensionality. intros. reflexivity.
    apply H4.
    unfold concreteCompose.
    split. simpl. reflexivity.
    split. simpl. reflexivity.
    split. intros. left. simpl. unfold empty_heap. reflexivity.
    unfold compose_heaps. simpl. apply functional_extensionality. intros. reflexivity.

    inversion H2. inversion H2. inversion H2. inversion H2. inversion H2. inversion H2.
    inversion H2.*)
Admitted.

Theorem while_aux2 : forall c b ff (invariant: absState) c1 st1,
   (forall st, exists st', exists res, realizeState (AbsStar ([convertToAbsExp b]) invariant) nil st ->
                                       ceval ff st c st' res ->
                                       realizeState invariant nil st') ->
    realizeState invariant nil st1 ->
    c1 = (WHILE b DO c LOOP) ->
    (exists st'', exists res', ceval ff st1 c1 st'' res').
Proof. admit. Admitted.
(*    intros. eapply ex_intro. eapply ex_intro.
    induction H1.
    inversion H2. inversion H2. inversion H2. inversion H2. inversion H2. inversion H2. inversion H2.
    inversion H2. inversion H2. inversion H2. inversion H2.
    inversion H2. subst.
    apply H1.*)



(*
 * Rule for propagating over a while.  When creating a proof, one will usually have to
 * fill in the expression 'invariant'.
 *)
Theorem whileThm : forall (state: absState) c b invariant res Q,
   {{AbsStar ([convertToAbsExp b]) invariant}} c {{invariant return res with Q}} ->
   (forall x, realizeState state nil x -> realizeState invariant nil x) ->
   {{state}} (WHILE b DO c LOOP) {{ (AbsStar ([~~(convertToAbsExp b)]) invariant) return res with Q}}.
Proof. admit.
    (*unfold hoare_triple. unfold absExecute. intros.

    split.

    eapply while_aux2.
        apply H. intros. eapply ex_intro. eapply ex_intro. intros.
        assert (forall st st' : ImpHeap.state,
        realizeState ([convertToAbsExp b] ** invariant) nil st ->
            (exists (st'0 : ImpHeap.state) (r : result),
               ceval
                 (fun (_ : id) (_ : ImpHeap.state) (_ : list nat)
                    (_ : ImpHeap.state) (_ : result) => False) st c st'0 r)).
        intros.
        assert((exists (st'0 : ImpHeap.state) (r : result),
          ceval
            (fun (_ : id) (_ : ImpHeap.state) (_ : list nat)
               (_ : ImpHeap.state) (_ : result) => False) st1 c st'0 r) /\
       (ceval
          (fun (_ : id) (_ : ImpHeap.state) (_ : list nat)
             (_ : ImpHeap.state) (_ : result) => False) st1 c st' res ->
        realizeState invariant nil st')).
        apply H0. eapply H5.
        inversion H6. subst. clear H6.
        apply H7.
        apply H2. apply H2. reflexivity.

    eapply while_aux.
        apply H. intros.
        assert(forall st' st0 res, realizeState ([convertToAbsExp b] ** invariant) nil st0 ->
            (ceval
          (fun (_ : id) (_ : ImpHeap.state) (_ : list nat)
             (_ : ImpHeap.state) (_ : result) => False) st0 c st' res) ->
          realizeState invariant nil st').
        intros.
        assert((exists (st'0 : ImpHeap.state) (r : result),
          ceval
            (fun (_ : id) (_ : ImpHeap.state) (_ : list nat)
               (_ : ImpHeap.state) (_ : result) => False) st1 c st'0 r) /\
       (ceval
          (fun (_ : id) (_ : ImpHeap.state) (_ : list nat)
             (_ : ImpHeap.state) (_ : result) => False) st1 c st'1 res1 ->
        realizeState invariant nil st'1)).
        apply H0. apply H5.

        inversion H7. subst. clear H7. apply H9. apply H6.

        eapply H5. apply H3. apply H4.
        apply H1. apply H2. reflexivity.

Grab Existential Variables. apply NoResult.*)
Admitted.
































































































