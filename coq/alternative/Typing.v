Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.
Require Import Coq.Sets.Ensembles.
Require Import SMEDL.Types.
Require Import SMEDL.AST.

Arguments exist {_ _} _ _.
Arguments existT {_ _} _ _.
Arguments In {_} _ _.
Arguments Add {_} _ _ _.

(** Variable environments *)
Record VarEnv : Type := mkVarEnv
  { VarEnv_vars : Ensemble string;
    VarEnv_lookup : {v : string | In VarEnv_vars v} -> Ty;
  }.

Notation "v ∈ Γ" := (In (VarEnv_vars Γ) v) (at level 40).

Coercion VarEnv_var (Γ : VarEnv) : Set :=
  {n : string | In (VarEnv_vars Γ) n}.

Coercion VarEnv_var_name {Γ : VarEnv} (v : Γ) : string :=
  proj1_sig v.

Notation "Γ [ v ]" := (VarEnv_lookup Γ v) (at level 40).

Program Definition VarEnv_extend (Γ : VarEnv) (n : string) (x : Ty) : VarEnv :=
  mkVarEnv (Add (VarEnv_vars Γ) n)
           (fun v => if string_dec (proj1_sig v) n
                     then x
                     else (Γ[v])).
Obligation 1.
inversion H0; subst.
- assumption.
- inversion H1.
  congruence.
Qed.

(** Typing judgements *)
(* Expressions *)
Inductive ArithTy : Ty -> Prop :=
| ArithTy_SInt : ArithTy SInt
| Arithty_SFloat : ArithTy SFloat.

Hint Constructors ArithTy.

Inductive ArithBinOp : BinOp -> Prop :=
| ArithBinOp_Plus : ArithBinOp Plus
| ArithBinOp_Times : ArithBinOp Times.

Hint Constructors ArithBinOp.

Inductive BoolBinOp : BinOp -> Prop :=
| BoolBinOp_Or : BoolBinOp Or 
| BoolBinOp_And : BoolBinOp And.

Hint Constructors BoolBinOp.

Inductive HasTy_BinOp : BinOp -> Ty -> Ty -> Ty -> Prop :=
| HasTy_Eq : forall ty, HasTy_BinOp Eq ty ty SBool
| HasTy_Or : forall op,
    BoolBinOp op ->
    HasTy_BinOp op SBool SBool SBool
| HasTy_Plus : forall ty op,
    ArithTy ty ->
    ArithBinOp op ->
    HasTy_BinOp op ty ty ty.

Hint Constructors HasTy_BinOp.

Inductive HasTy_UnOp : UnOp -> Ty -> Ty -> Prop :=
| HasTy_Neg : forall ty,
    ArithTy ty ->
    HasTy_UnOp Neg ty ty
| HasTy_Not : HasTy_UnOp Not SBool SBool.

Hint Constructors HasTy_UnOp.

Inductive HasTy_Expr : VarEnv -> Expr -> Ty -> Prop :=
| HasTy_Var : forall (Γ : VarEnv),
    forall (v : Γ), HasTy_Expr Γ (Var v) (Γ[v])
| HasTy_LitNat : forall (Γ : VarEnv),
    forall n, HasTy_Expr Γ (LitInt n) SInt
| HasTy_LitFloat : forall (Γ : VarEnv),
    forall q, HasTy_Expr Γ (LitFloat q) SFloat
| HasTy_LitBool : forall (Γ : VarEnv),
    forall b, HasTy_Expr Γ (LitBool b) SBool
| HasTy_UnOpExpr : forall (Γ : VarEnv),
    forall op body body_ty ty,
    HasTy_UnOp op body_ty ty ->
    HasTy_Expr Γ (UnOpExpr op body) ty
| HasTy_BinOpExpr : forall (Γ : VarEnv),
    forall op lhs_ty rhs_ty ty lhs rhs,
      HasTy_BinOp op lhs_ty rhs_ty ty ->
      HasTy_Expr Γ lhs lhs_ty ->
      HasTy_Expr Γ rhs rhs_ty ->
      HasTy_Expr Γ (BinOpExpr And lhs rhs) ty.

Hint Constructors HasTy_Expr.

Notation "Γ |- e :: τ" := (HasTy_Expr Γ e τ) (at level 70).

(* Commands *)

(** Event environments *)
Record EventEnv := mkEventEnv
  { EventEnv_events : Ensemble string;
    EventEnv_event_airity : {name : string | In EventEnv_events name} -> nat;
    EventEnv_lookup :
      forall (ev : {n : string | In EventEnv_events n})
             (n : Fin.t (EventEnv_event_airity ev)),
        Ty;
    EventEnv_param_name :
      forall (ev : {n : string | In EventEnv_events n})
             (n : Fin.t (EventEnv_event_airity ev)),
        string;
    EventEnv_param_names_unique :
      forall (ev : {n : string | In EventEnv_events n})
             (n1 n2 : Fin.t (EventEnv_event_airity ev)),
        EventEnv_param_name ev n1 = EventEnv_param_name ev n2 ->
        n1 = n2;
  }.

Notation "ev ∈ Δ" := (In (EventEnv_events Δ) ev) (at level 40).

Coercion EventEnv_event (Δ : EventEnv) : Type :=
  { ev : string | ev ∈ Δ }.

Notation "Δ ![ ev , p ]" := (EventEnv_lookup Δ ev p) (at level 50).

Notation "Δ ?[ ev , p ]" := (EventEnv_param_name Δ ev p) (at level 50).

Notation "Δ #[ ev ]" := (EventEnv_event_airity Δ ev) (at level 50).

Inductive HasTy_Cmd (Δ : EventEnv) (Γ : VarEnv) : Cmd -> Prop :=
| HasTy_Assign : forall (v : Γ) e,
    HasTy_Expr Γ e (Γ[v]) ->
    HasTy_Cmd Δ Γ (Assign v e)
| HasTy_Raise : forall ev args,
    (* Right number of args *)
    List.length args = Δ#[ev] ->
    (* Right types of args *)
    (forall p (Hlt : p < Δ#[ev]) arg,
        List.nth_error args p = Some arg ->
        HasTy_Expr Γ arg (Δ![ev,Fin.of_nat_lt Hlt])) ->
    HasTy_Cmd Δ Γ (Raise (proj1_sig ev) args)
| HasTy_Seq : forall c1 c2,
    HasTy_Cmd Δ Γ c1 ->
    HasTy_Cmd Δ Γ c2 ->
    HasTy_Cmd Δ Γ (Seq c1 c2)
| HasTy_If : forall cond c_then c_else,
    HasTy_Expr Γ cond SBool ->
    HasTy_Cmd Δ Γ c_then ->
    HasTy_Cmd Δ Γ c_else ->
    HasTy_Cmd Δ Γ (If cond c_then c_else).

Hint Constructors HasTy_Cmd.

Notation "Δ , Γ |- c" := (HasTy_Cmd Δ Γ c) (at level 70).

Definition VarEnv_extend_with_event_param
           (Δ : EventEnv)
           (ev : Δ)
           (Γ : VarEnv)
           (p : Fin.t (Δ#[ev])) : VarEnv :=
  VarEnv_extend Γ
                (EventEnv_param_name Δ ev p)
                (EventEnv_lookup Δ ev p).

Program Fixpoint VarEnv_extend_with_event'
        (Δ : EventEnv)
        (ev : Δ)
        (Γ : VarEnv)
        (p : nat)
        (Hp : p <= Δ#[ev]) : VarEnv :=
  match p with
  | 0 => Γ
  | S n =>
    VarEnv_extend_with_event'
      Δ
      ev
      (VarEnv_extend_with_event_param Δ ev Γ (Fin.of_nat_lt Hp))
      n
      (Le.le_Sn_le _ _ Hp)
  end.

Program Definition VarEnv_extend_with_event
        (Δ : EventEnv)
        (ev : Δ)
        (Γ : VarEnv) : VarEnv :=
  VarEnv_extend_with_event' Δ ev Γ (Δ#[ev]) _.

Inductive HasTy_Transition (Δ : EventEnv) (Γ : VarEnv) : Transition -> Prop :=
| HasTy_Transition_intro : forall src dst ev guard act,
    HasTy_Expr (VarEnv_extend_with_event Δ ev Γ) guard SBool ->
    HasTy_Cmd Δ (VarEnv_extend_with_event Δ ev Γ) act ->
    HasTy_Transition Δ Γ (mkTransition src (proj1_sig ev) guard act dst).