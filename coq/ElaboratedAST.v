Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.Strings.String.
Require Import Types.

Open Scope type. 

Section ElaboratedAST.
  (* The type environment for the AST *)
  Variable vars : list string.
  Definition var := { e : string | In e vars }.
  Variable var_env : var -> Ty.

  Variable events : list string.
  Definition event := { e : string | In e events }.
  Variable event_params : event -> list string.
  Definition event_param (e : event) :=
    { p : string | In p (event_params e) }.
  Variable event_env : forall (e : event), event_param e -> Ty.

  Variable states : list string.
  Definition state := { s : string | In s states }.

  (* Expressions *)
  Inductive BinOp : Ty -> Set :=
  | And : BinOp SBool
  | Or : BinOp SBool
  | IPlus : BinOp SInt
  | ITimes : BinOp SInt
  | FPlus : BinOp SFloat
  | FTimes : BinOp SFloat.

  (* Is there a way to deal with a little bit of ad hoc polymorphism without
    needing all of typeclasses? *)
  Inductive UnOp : Ty -> Set :=
  | Not : UnOp SBool 
  | INeg : UnOp SInt
  | FNeg : UnOp SFloat.

  Inductive Expr : Ty -> Set :=
  | Var : forall (x : var), Expr (var_env x)
  | LitBool : bool -> Expr SBool
  | LitInt : nat -> Expr SInt 
  | LitFloat : Q -> Expr SFloat
  (* Need to enhance BinOp instead of special-casing EqExpr. *)
  | EqExpr : forall {ty}, Expr ty -> Expr ty -> Expr SBool
  | BinOpExpr : forall {ty}, BinOp ty -> Expr ty -> Expr ty -> Expr ty
  | UnOpExpr : forall {ty}, UnOp ty -> Expr ty -> Expr ty.

  (* Commands *)
  Inductive Cmd : Set := 
  | Assign : forall (x : var), Expr (var_env x) -> Cmd
  | Raise : forall (e : event),
      (forall (p : event_param e), Expr (event_env e p)) -> Cmd.

  (* Transitions *)
  Record Transition := mkTransition
    { transSrc : state;
      transTrigger : event;
      transGuard : Expr SBool;
      transAction : Cmd;
      transDest : state;
    }.

  Definition Scenario := list Transition.

  Definition Monitor := list Scenario.
End ElaboratedAST.

Global Arguments Expr {vars} _ _.
Global Arguments Cmd {vars} _ {events} {event_params} _.
Global Arguments BinOpExpr {_} {_} {_} _ _ _.
Global Arguments UnOpExpr {_} {_} {_} _ _.
Global Arguments Var {_} {_} _.
Global Arguments LitInt {_} {_} _.
Global Arguments LitFloat {_} {_} _.
Global Arguments LitBool {_} {_} _.
Global Arguments Assign {_} {_} {_} {_} _ _ _.
Global Arguments Raise {_} {_} {_} _ _ _ _.


Module Example.
  Ltac invert_false :=
    match goal with
    | [H : _ |- _ ] => progress inversion H
    end.

  Open Scope string.
  Open Scope list.
  Definition vars_ex : list string := "x1"::"x2"::nil.
  Definition events_ex : list string := "e1"::"e2"::nil.
  Definition var_ex := { e : string | In e vars_ex }.
  Program Definition var_env_ex (x : var_ex) : Ty :=
    match proj1_sig x with
    | "x1" => SInt
    | "x2" => SBool
    | _ => _
    end.
  Obligation 1.
  exfalso.
  destruct x.
  simpl in *.
  intuition.
  Defined.
  Solve Obligations with (simpl; intuition; invert_false).

  Program Definition x1 : Expr var_env_ex SInt :=
    BinOpExpr IPlus (Var "x1") (LitInt 1).

  Program Definition x2 : Expr var_env_ex SBool :=
    UnOpExpr Not (BinOpExpr And (LitBool true) (Var "x2")).
End Example.