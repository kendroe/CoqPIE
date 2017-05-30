(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * MagicWandExistsHelper.v
 *
 **********************************************************************************)

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

Fixpoint localizeExists (s : absState) (n : nat) :=
    match s with
    | AbsStar s1 s2 => AbsStar (localizeExists s1 n) (localizeExists s2 n)
    | AbsOrStar s1 s2 => AbsOrStar (localizeExists s1 n) (localizeExists s2 n)
    | AbsMagicWand s1 s2 => AbsMagicWand (localizeExists s1 n) (localizeExists s2 n)
    | AbsUpdateVar s vv vall => AbsUpdateVar (localizeExists s n) vv vall
    | AbsUpdateWithLoc s vv vall => AbsUpdateWithLoc (localizeExists s n) vv vall
    | AbsUpdateLoc s vv vall => AbsUpdateLoc (localizeExists s n) vv vall
    | AbsUpdState s1 s2 s3 => AbsUpdState (localizeExists s1 n) (localizeExists s2 n) (localizeExists s3 n)
    | AbsAll e s => AbsAll e (localizeExists s (S n))
    | AbsEach e s => AbsEach e (localizeExists s (S n))

    | AbsExistsT (AbsStar s1 s2) => if hasVnState s1 0 then
                                        if hasVnState s2 0 then
                                            AbsExistsT (AbsStar (localizeExists s1 (S n)) (localizeExists s2 (S n) ))
                                        else
                                            (AbsStar (AbsExistsT (localizeExists s1 (S n))) (removeStateVar 0 s2))
                                    else
                                        (AbsStar (removeStateVar 0 s1) (AbsExistsT (localizeExists s2 (S n))))
    | AbsExists e (AbsStar s1 s2) => if hasVnState s1 0 then
                                         if hasVnState s2 0 then
                                             AbsExists e (AbsStar (localizeExists s1 (S n)) (localizeExists s2 (S n)))
                                         else
                                             (AbsStar (AbsExists e (localizeExists s1 (S n))) (removeStateVar 0 s2))
                                     else
                                         (AbsStar (removeStateVar 0 s1) (AbsExists e (localizeExists s2 (S n))))
    | AbsExistsT s => AbsExistsT (localizeExists s (S n))
    | AbsExists e s => AbsExists e (localizeExists s (S n))
    | x => x
    end.

Theorem localizeExistsThm1 : forall bindings s state1 state2,
    state1 = localizeExists state2 0 ->
    (realizeState state1 bindings s -> realizeState state2 bindings s).
Proof.
    admit.
Admitted.

Theorem localizeExistsThm2 : forall bindings s state1 state2,
    state1 =localizeExists state2 0 ->
    (realizeState state2 bindings s -> realizeState state1 bindings s).
Proof.
    admit.
Admitted.

Theorem localizeExistsLeft : forall right res state1 state2,
    state1 = localizeExists state2 0 ->
    (mergeStates state1 right res -> mergeStates state2 right res).
Proof.
    admit.
Admitted.

Fixpoint hasVarExpList (e : absExp) (l : list id) :=
    match l with
    | nil => false
    | (a::b) => if hasVarExp e a then true else hasVarExpList e b
    end.

Fixpoint findVal vlist v (e : absState) :=
    match e with
    | AbsStar l r => match findVal vlist v l with
                     | Some x => Some x
                     | None => findVal vlist v r
                     end
    | AbsUpdateVar s vv r => if hasVarExp v vv then None else findVal (vv::vlist) v s
    | AbsUpdateWithLoc s vv r => if hasVarExp v vv then None else findVal (vv::vlist) v s
    | ( l |-> vv) => if hasVarExpList vv vlist then None else if beq_absExp l v then Some vv
                    else None
    | _ => None
    end.

Fixpoint clearUpdateWithLoc (s : absState) :=
    match s with
    | AbsUpdateWithLoc ss v e => match clearUpdateWithLoc ss with
                                 | sss => match findVal nil e sss with
                                          | None => AbsUpdateWithLoc sss v e
                                          | Some x => AbsUpdateVar sss v x
                                          end
                                 end
    | AbsUpdateVar ss v e => AbsUpdateVar (clearUpdateWithLoc ss) v e
    | x => x
    end.

Fixpoint clearMagicWandUpdateWithLoc (s : absState) :=
    match s with
    | AbsExistsT e => AbsExistsT (clearMagicWandUpdateWithLoc e)
    | AbsExists e s => AbsExists e (clearMagicWandUpdateWithLoc s)
    | AbsUpdateVar s v e => AbsUpdateVar (clearMagicWandUpdateWithLoc s) v e
    | AbsUpdateWithLoc s v e => AbsUpdateWithLoc (clearMagicWandUpdateWithLoc s) v e
    | AbsMagicWand l r => AbsMagicWand (clearUpdateWithLoc l) r
    | x => x
    end.

Theorem clearMagicWandUpdateWithLocThm : forall s s' bindings ss,
    s' = clearMagicWandUpdateWithLoc s ->
    (realizeState s bindings ss -> realizeState s' bindings ss).
Proof.
    admit.
Admitted.

Fixpoint pair_apply1 {t} {r} (f : r -> t -> t -> option r) (b :r) (l1 : list t) (l2 : list t) : option r :=
    match l1,l2 with
    | nil,nil => Some b
    | f1::r1,f2::r2 => match f b f1 f2 with
                         | Some bb => pair_apply1 f bb r1 r2
                         | None => None
                         end
    | _, _ => None
    end.

Definition funFix1 (x : option (list (nat * absExp))) :=
    match x with
    | Some b => Some b
    | None => None
    end.

Fixpoint matchBinding (v : nat) (e : absExp) (bindings : list (nat * absExp)) :=
    match bindings with
    | nil => Some ((v,e)::nil)
    | ((vv,f)::r) => if beq_nat v vv then
                         (if beq_absExp e f then Some bindings else None)
                     else
                         matchBinding v e r
    end.

Fixpoint is_instance (limit : nat) (bindings: list (nat * absExp)) (e1 : absExp) (e2 : absExp) :=
    match (e1,e2) with
    | (AbsConstVal v1,AbsConstVal v2) => if beq_val v1 v2 then Some bindings else None
    | (AbsVar v1,AbsVar v2) => if beq_id v1 v2 then (Some bindings) else None
    | (AbsQVar v1,AbsQVar v2) => if ble_nat limit v1 then
                                   (if beq_nat v1 (v2+limit) then Some bindings else None)
                                 else matchBinding v1 (AbsQVar v2) bindings
    | (AbsQVar v1,t) => if ble_nat limit v1 then
                            None
                        else matchBinding v1 t bindings
    | (AbsFun i1 el1,AbsFun i2 el2) => if beq_id i1 i2 then
                                         (fix go b l1 l2 :=
                                           match l1,l2 with
                                           | (f1::r1),(f2::r2) => match is_instance limit b f1 f2 with
                                                                  | Some b => go b r1 r2
                                                                  | None => None
                                                                  end
                                           | nil,nil => Some b
                                           | _,_ => None
                                           end) bindings el1 el2
                                       else None
    | (l,r) => None
    end.

Fixpoint is_instance_state (limit : nat) (bindings: list (nat * absExp)) (p : absState) (e : absState) :=
   match (p,e) with
    | (AbsStar l1 l2,AbsStar r1 r2) => match is_instance_state limit bindings l1 r1 with
                                             | Some b => is_instance_state limit bindings l2 r2
                                             | None => None
                                       end
    | (AbsOrStar l1 l2,AbsOrStar r1 r2) => match is_instance_state limit bindings l1 r1 with
                                             | Some b => is_instance_state limit bindings l2 r2
                                             | None => None
                                       end
    | (AbsEmpty,AbsEmpty) => Some bindings
    | (AbsLeaf i1 el1,AbsLeaf i2 el2) => if beq_id i1 i2 then 
                                       pair_apply1 (is_instance limit) bindings el1 el2
                                   else None
    | (AbsAccumulate i1 e1a e1b e1c,AbsAccumulate i2 e2a e2b e2c) =>
          if beq_id i1 i2 then
              match is_instance limit bindings e1a e2a with
              | Some b2 => match is_instance limit b2 e1b e2b with
                                      | Some b3 => is_instance limit b3 e1c e2c
                                      | None => None
                                      end
              | None => None
              end
          else None
    | (_,_) => None
    end.

Fixpoint matchExistential (v : nat) (p : absState) (e: absState) :=
    match p with
    | AbsExistsT s => matchExistential (v+1) s e
    | _ => is_instance_state v nil p e
    end.

Fixpoint removeSubterm (p : absState) (e: absState) :=
    match e with
    | AbsStar l r => match removeSubterm p l with
                     | Some ll => Some (AbsStar ll r)
                     | None => match removeSubterm p r with
                               | Some rr => Some (AbsStar l rr)
                               | None => None
                               end
                     end
    | AbsExistsT e => match removeSubterm (addStateVar 0 p) e with
                      | Some l => Some (AbsExistsT l)
                      | None => None
                      end
    | AbsExists ee e => match removeSubterm (addStateVar 0 p) e with
                        | Some l => Some (AbsExists ee l)
                        | None => None
                        end
    | AbsUpdateVar s v e => if hasVarState p v then None else
                            match removeSubterm p s with
                            | Some x => Some (AbsUpdateVar x v e)
                            | None => None
                            end
    | AbsUpdateWithLoc s v e => if hasVarState p v then None else
                                match removeSubterm p s with
                                | Some x => Some (AbsUpdateWithLoc x v e)
                                | None => None
                                end
    | _ => match matchExistential 0 p e with
           | Some x => Some AbsEmpty
           | None => None
           end
    end.

Fixpoint removeSubterms (p : absState) (e : absState) :=
    match p with
    | AbsStar l r => match removeSubterms l e with
                     | Some x => removeSubterms r x
                     | None => None
                     end
    | x => removeSubterm x e
    end.

Fixpoint removeMagicWand (s : absState) :=
    match s with
    | AbsExistsT e => match removeMagicWand e with
                      | Some x => Some (AbsExistsT x)
                      | None => None
                      end
    | AbsExists e s => match removeMagicWand s with
                       | Some x => Some (AbsExists e x)
                       | None => None
                       end
    | AbsStar l r => match removeMagicWand l with
                       | Some x => Some (AbsStar x r)
                       | None => match removeMagicWand r with
                                 | Some x => Some (AbsStar l x)
                                 | None => None
                                 end
                       end
    | AbsUpdateVar s v e => match removeMagicWand s with
                            | Some x => Some (AbsUpdateVar x v e)
                            | None => None
                            end
    | AbsUpdateWithLoc s v e => match removeMagicWand s with
                                | Some x => Some (AbsUpdateWithLoc x v e)
                                | None => None
                                end
    | AbsUpdateLoc s v e => match removeMagicWand s with
                            | Some x => Some (AbsUpdateLoc x v e)
                            | None => None
                            end
    | AbsMagicWand l r => removeSubterms r l
    | x => None
    end.

Theorem removeMagicWandThm : forall s s' bindings ss,
    Some s' = removeMagicWand s ->
    (realizeState s bindings ss -> realizeState s' bindings ss).
Proof.
    admit.
Admitted.

Theorem removeMagicWandLeft : forall s s' r m,
    Some s' = removeMagicWand s ->
    (mergeStates s' r m -> mergeStates s r m).
Proof.
    admit.
Admitted.

Theorem removeMagicWandRight : forall s s' l m,
    Some s' = removeMagicWand s ->
    (mergeStates l s' m -> mergeStates l s m).
Proof.
    admit.
Admitted.

Fixpoint clearSubterm (p : absState) (e: absState) :=
    match e with
    | AbsStar l r => match clearSubterm p l with
                     | Some b => Some b
                     | None => clearSubterm p r
                     end
    | AbsUpdateWithLoc s v e => if hasVarState p v then None else clearSubterm p s
    | AbsUpdateVar s v e => if hasVarState p v then None else clearSubterm p s
    | _ => matchExistential 0 p e
    end.

Fixpoint clearAllSubterms (p : absState) (e: absState) :=
    match p with
    | AbsStar l r => match clearAllSubterms l e with
                     | Some x => clearAllSubterms r e
                     | None => None
                     end
    | _ => clearSubterm p e
    end.

Inductive propagateInExists : nat -> absState -> absState -> Prop :=
    | propagateInExistsId: forall x y n, x=y -> propagateInExists n x y
    | propagateInExistsSimp: forall x y z n,
          y = localizeExists x n ->
          propagateInExists n y z ->
          propagateInExists n x z.
          

Fixpoint subn n (s : absState) :=
    match n with
    | 0 => s
    | S n' => subn n' (removeStateVar 0 s)
    end.

Theorem magicWandStateExists : forall core st state sub q sub' sub'' n,
    getRoot state = AbsMagicWand core sub ->
    (exists s, realizeState st nil s) ->
    getRoot st = core ->
    getRootLevel st = n ->
    sub' = subn n sub ->
    propagateInExists 0 sub' sub'' ->
    clearAllSubterms sub'' core=Some q ->
    (exists s, realizeState state nil s).
Proof.
    admit.
Admitted.

Theorem simplifyExists : forall st st',
    st' = simplifyState nil st ->
    (exists s, realizeState st' nil s) ->
    (exists s, realizeState st nil s).
Proof.
    admit.
Admitted.

Theorem existsWithLoc : forall st a b,
    (exists s, realizeState st nil s) ->
    (exists s, realizeState (AbsUpdateWithLoc st a b) nil s).
Proof.
    admit.
Admitted.

Theorem existsVar : forall st a b,
    (exists s, realizeState st nil s) ->
    (exists s, realizeState (AbsUpdateVar st a b) nil s).
Proof.
    admit.
Admitted.


Theorem localizeExistsRightp
    : forall P1 P2 P,
      mergeStates P1 (localizeExists P2 0) P -> mergeStates P1 P2 P.
Proof.
    admit.
Admitted.

Theorem localizeExistsLeftp
    : forall P1 P2 P,
      mergeStates (localizeExists P1 0) P2 P -> mergeStates P1 P2 P.
Proof.
    admit.
Admitted.

Theorem existsRealizeState :
     forall st st' b s,
     (realizeState st b s -> realizeState st' b s) ->
     (exists s, realizeState st b s) ->
     (exists s, realizeState st' b s).
Proof.
    admit.
Admitted.


















































