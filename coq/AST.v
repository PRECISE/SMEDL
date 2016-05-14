Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.Strings.String.
Require Import Types.

Open Scope type.

Definition EventParamDecl := list (string * Ty).
Definition EventDecl := list (string * EventParamDecl).
Definition EvenDeclBlock := list EventDecl.

Definition GlobalDecl := string * Ty.
Definition GlobalDeclBlock := list EventDecl.

Inductive UnOp :=
| Not : UnOp
| Neg : UnOp.
           
Inductive BinOp :=
| And : BinOp
| Or : BinOp
| Plus : BinOp
| Times : BinOp.

Inductive Expr :=
| Var : string -> Expr
| LitInt : nat -> Expr
| LitFloat : Q -> Expr                   
| LitBool : bool -> Expr
| UnOpExpr : UnOp -> Expr -> Expr
| BinOpExpr : BinOp -> Expr -> Expr -> Expr.

Inductive Cmd :=
| Assign : string -> Expr -> Cmd
| Raise : string -> list Expr -> Cmd.

Record Transition := mkTransition
  { transitionSourceState : string;
    transitionGuard : Expr;
    transitionAction : Cmd;
    transitionDestState : string
  }.

Definition Scenario := list Transition.

Definition Monitor := list Scenario.