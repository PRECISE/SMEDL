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

Notation "Γ |- e :: τ" := (HasTy_Expr Γ e τ) (at level 70).


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

Notation "Δ ,, Γ |- c" := (HasTy_Cmd Δ Γ c) (at level 70).

Inductive HasTy_Transition (Δ : EventEnv.t) (Γ : VarEnv.t) : Transition -> Prop :=
| HasTy_Transition_intro : forall src dst ev actions,
    List.Forall (fun action : Expr * Cmd =>
                   let (guard, act) := action in
                   HasTy_Expr (Γ +![Δ;ev]) guard SBool /\
                   HasTy_Cmd Δ (Γ +![Δ;ev]) act)
                actions ->
    HasTy_Transition Δ Γ (mkTransition src (proj1_sig ev) actions dst).

Inductive HasTy_Scenario (Δ : EventEnv.t) (Γ : VarEnv.t) :
  Scenario -> Prop :=
| HasTy_Scenario_intro : forall ts,
    (* Each transition is independently OK. *)
    List.Forall (HasTy_Transition Δ Γ) ts ->
    (* No source-state/trigger duplication. *)
    List.NoDup (List.map (fun t => (Transition_source t, Transition_trigger t)) ts) ->
    HasTy_Scenario Δ Γ ts.

Inductive HasTy_EventEnv (es : list EventDecl) (ee : EventEnv.t) : Prop :=
| HasTy_EventEnv_intro :
    (* Events have the same names *)
    (forall e, ((exists ps, List.In (e, ps) es) <-> e ∈ ee)) ->
    (* No duplicate event names *)
    (List.NoDup (List.map fst es)) ->
    (* No duplicate parameter names *)
    (forall e ps, List.In (e, ps) es ->
                  List.NoDup (List.map fst ps)) ->
    (* Events have the same number of parameters *)
    (forall e ps, List.In (proj1_sig e, ps) es ->
                  List.length ps = EventEnv.arity ee e) ->
    (* Events parameters have the same names *)
    (forall e ps,
        List.In (proj1_sig e, ps) es ->
        forall pi,
          (List.nth_error (List.map fst ps)
                          (proj1_sig (Fin.to_nat pi))) =
          Some (nth (EventEnv.param_name ee e) pi)) ->
    (* Event parameters have the same types *)
    (forall e ps,
        List.In (proj1_sig e, ps) es ->
        forall pi,
          (List.nth_error (List.map snd ps)
                          (proj1_sig (Fin.to_nat pi))) =
          Some (nth (EventEnv.lookup ee e) pi)) ->
    HasTy_EventEnv es ee.

(* Equivalence of event environments relies on Ensemble extensionality and
 Functional Extensionality. Is that OK?*)

Require Import Coq.Logic.FunctionalExtensionality.

Lemma HasEventEnv_unique : forall es ee1 ee2,
    HasTy_EventEnv es ee1 ->
    HasTy_EventEnv es ee2 ->
    ee1 = ee2.                  (* TODO: = or some other equivalence? *)
Proof.
  intros.
  inversion H; inversion H0.
  destruct ee1, ee2.
  simpl in *.

  assert (Heq : events0 = events)
    by (apply Extensionality_Ensembles;
        unfold Same_set, Included;
        firstorder).
  subst.

  assert (Heq : arity0 = arity).
  { extensionality x.
    specialize (H10 x).
    specialize (H4 x).
    destruct x.
    specialize (H7 x).
    inversion H7.
    specialize (H14 i).
    inversion H14.
    specialize (H10 x0).
    specialize (H4 x0).
    rewrite <- H10, <- H4;
      simpl; auto.
  }
  subst.

  assert (Heq : param_name0 = param_name).
  { extensionality x.
    apply Vector.eq_nth_iff; intros; subst.
    specialize (H5 x).
    specialize (H11 x).
    destruct x.
    specialize (H7 x).
    inversion H7.
    specialize (H14 i).
    inversion H14.
    specialize (H5 x0).
    specialize (H11 x0).
    simpl in *.
    specialize (H5 H15 p2).
    specialize (H11 H15 p2).
    rewrite H5 in H11.
    inversion H11.
    rewrite H17.
    auto.
  }
  subst.

  assert (Heq : lookup0 = lookup).
  { extensionality x.
    apply Vector.eq_nth_iff; intros; subst.
    specialize (H6 x).
    specialize (H12 x).
    destruct x.
    specialize (H7 x).
    inversion H7.
    specialize (H14 i).
    inversion H14.
    specialize (H6 x0).
    specialize (H12 x0).
    simpl in *.
    specialize (H6 H15 p2).
    specialize (H12 H15 p2).
    rewrite H6 in H12.
    inversion H12.
    rewrite H17.
    auto.
  }
  subst.

  assert (Heq : param_names_unique0 = param_names_unique).
  { extensionality x.
    extensionality n1.
    extensionality n2.
    extensionality Hn1n2.
    Require Import Eqdep_dec.
    apply eq_proofs_unicity.
    clear.
    intros.
    destruct (Fin.eq_dec x0 y); intuition.
  }
  subst.

  reflexivity.
Qed.

(* Inductive HasTy_LM : LocalMonitor -> Prop := *)
(* | HasTy_LM_intro : forall es gs ts, *)
(*     (* Events  *) *)
(*     HasTy_LM (mkLocalMonitor es gs ts). *)