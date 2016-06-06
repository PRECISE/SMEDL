Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.
Require Import Coq.Sets.Ensembles.
Require Import SMEDL.Types.
Require Import SMEDL.AST.
Require SMEDL.VarEnv.
Import SMEDL.VarEnv.Notations.
Import SMEDL.VarEnv.Coercions.
Require SMEDL.EventEnv.
Import SMEDL.EventEnv.Notations.
Import SMEDL.EventEnv.Coercions.

Arguments exist {_ _} _ _.
Arguments existT {_ _} _ _.

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

Inductive HasTy_Expr : VarEnv.t -> Expr -> Ty -> Prop :=
| HasTy_Var : forall (Γ : VarEnv.t),
    forall (v : Γ), HasTy_Expr Γ (Var v) (Γ[v])
| HasTy_LitNat : forall (Γ : VarEnv.t),
    forall n, HasTy_Expr Γ (LitInt n) SInt
| HasTy_LitFloat : forall (Γ : VarEnv.t),
    forall q, HasTy_Expr Γ (LitFloat q) SFloat
| HasTy_LitBool : forall (Γ : VarEnv.t),
    forall b, HasTy_Expr Γ (LitBool b) SBool
| HasTy_UnOpExpr : forall (Γ : VarEnv.t),
    forall op body body_ty ty,
    HasTy_UnOp op body_ty ty ->
    HasTy_Expr Γ (UnOpExpr op body) ty
| HasTy_BinOpExpr : forall (Γ : VarEnv.t),
    forall op lhs_ty rhs_ty ty lhs rhs,
      HasTy_BinOp op lhs_ty rhs_ty ty ->
      HasTy_Expr Γ lhs lhs_ty ->
      HasTy_Expr Γ rhs rhs_ty ->
      HasTy_Expr Γ (BinOpExpr And lhs rhs) ty.

Hint Constructors HasTy_Expr.

(** Commands *)
Inductive HasTy_Cmd (Δ : EventEnv.t) (Γ : VarEnv.t) : Cmd -> Prop :=
| HasTy_Assign : forall (v : Γ) e,
    HasTy_Expr Γ e (Γ[v]) ->
    HasTy_Cmd Δ Γ (Assign v e)
| HasTy_Raise : forall ev args,
    (* Right number of args *)
    List.length args = Δ#[ev] ->
    (* Right types of args *)
    (forall p (Hlt : p < Δ#[ev]) arg,
        List.nth_error args p = Some arg ->
        HasTy_Expr Γ arg (Δ![ev;Fin.of_nat_lt Hlt])) ->
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

Inductive HasTy_Transition (Δ : EventEnv.t) (Γ : VarEnv.t)
  : Transition -> Prop :=
| HasTy_Transition_intro : forall src dst ev actions,
    (* All of the guards and actions typecheck. *)
    List.Forall
      (fun action : Expr * Cmd =>
         let (guard, act) := action in
         HasTy_Expr (Γ +![Δ;ev]) guard SBool /\
         HasTy_Cmd Δ (Γ +![Δ;ev]) act)
      actions ->
    HasTy_Transition Δ Γ (mkTransition src (proj1_sig ev) actions dst).

Hint Constructors HasTy_Transition.

Inductive HasTy_Scenario (Δ : EventEnv.t) (Γ : VarEnv.t) :
  Scenario -> Prop :=
| HasTy_Scenario_intro : forall ts,
    (* Each transition is independently OK. *)
    List.Forall (HasTy_Transition Δ Γ) ts ->
    (* No source-state/trigger duplication. *)
    List.NoDup (List.map (fun t => (Transition_source t, Transition_trigger t)) ts) ->
    HasTy_Scenario Δ Γ ts.

Inductive HasTy_EventEnv (es : list EventDecl) (Δ : EventEnv.t) : Prop :=
| HasTy_EventEnv_intro :
    (* Events have the same names *)
    (forall e, ((exists ps, List.In (e, ps) es) <-> e ∈ Δ)) ->
    (* No duplicate event names *)
    (List.NoDup (List.map fst es)) ->
    (* No duplicate parameter names *)
    (forall e ps, List.In (e, ps) es ->
                  List.NoDup (List.map fst ps)) ->
    (* Events have the same number of parameters *)
    (forall e ps, List.In (proj1_sig e, ps) es ->
                  List.length ps = EventEnv.arity Δ e) ->
    (* Events parameters have the same names *)
    (forall e ps,
        List.In (proj1_sig e, ps) es ->
        forall pi,
          (List.nth_error (List.map fst ps)
                          (proj1_sig (Fin.to_nat pi))) =
          Some (nth (EventEnv.param_name Δ e) pi)) ->
    (* Event parameters have the same types *)
    (forall e ps,
        List.In (proj1_sig e, ps) es ->
        forall pi,
          (List.nth_error (List.map snd ps)
                          (proj1_sig (Fin.to_nat pi))) =
          Some (nth (EventEnv.lookup Δ e) pi)) ->
    HasTy_EventEnv es Δ.

Hint Constructors HasTy_EventEnv.

Inductive HasTy_VarEnv (gs : list GlobalDecl) (Γ : VarEnv.t) : Prop :=
| HasTy_VarEnv_intro :
    (* Unique variable names *)
    List.NoDup (List.map fst gs) ->
    (* Same variable names *)
    (forall n, In (VarEnv.vars Γ) n <-> exists ty, List.In (n, ty) gs) ->
    (* Same types for same names *)
    (forall v ty, Γ[v] = ty <-> List.In ((proj1_sig v), ty) gs) ->
    HasTy_VarEnv gs Γ.

Hint Constructors HasTy_VarEnv.

Inductive HasTy_LM : LocalMonitor -> Prop :=
| HasTy_LM_intro : forall es Δ gs Γ ss,
    (* Events typecheck *)
    HasTy_EventEnv es Δ ->
    HasTy_VarEnv gs Γ ->
    (* Scenarios typecheck independently *)
    List.Forall (fun s => HasTy_Scenario Δ Γ s) ss ->
    (* TODO: Scenarios are compatible *)
    (* Events  *)
    HasTy_LM (mkLocalMonitor es gs ss).

Hint Constructors HasTy_LM.