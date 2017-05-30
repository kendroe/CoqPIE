 Inductive var : list Type -> Type -> Type :=
  | VO : forall T Ts, var (T :: Ts) T
  | VS : forall T Ts T', var Ts T -> var (T' :: Ts) T.

  Implicit Arguments VO [T Ts].
  Implicit Arguments VS [T Ts T'].

  Inductive propX (G : list Type) : Type :=
  | Inj : Prop -> propX G
  | Cptr : nat -> (nat -> propX G) -> propX G
  | And : propX G -> propX G -> propX G
  | Or : propX G -> propX G -> propX G
  | Imply : propX G -> propX G -> propX G
  | Forall : forall A, (A -> propX G) -> propX G
  | Exists : forall A, (A -> propX G) -> propX G

  | Var : forall A, var G A -> A -> propX G
  | ForallX : forall A, propX (A :: G) -> propX G
  | ExistsX : forall A, propX (A :: G) -> propX G.

  Implicit Arguments Inj [G].

  Definition PropX := propX nil.

Fixpoint liftV G T (v : var G T) G' : var (G ++ G') T :=
    match v with
      | VO _ _ => VO
      | VS _ _ _ v' => VS (liftV _ _ v' _)
    end.

  Fixpoint liftV G T (v : var G T) G' : var (G ++ G') T :=
    match v with
      | VO _ _ => VO
      | VS _ _ _ v' => VS (liftV v' _)
    end.