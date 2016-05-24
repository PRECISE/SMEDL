Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.Strings.String.
Require Import SMEDL.Types.

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
| Eq : BinOp
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
| Raise : string -> list Expr -> Cmd
| If : Expr -> Cmd -> Cmd -> Cmd
| Seq : Cmd -> Cmd -> Cmd.

Record Transition := mkTransition
  { Transition_source : string;
    Transition_trigger : string;
    Transition_guard : Expr;
    Transition_action : Cmd;
    Transition_dest : string
  }.

Definition Scenario := list Transition.

Definition Monitor := list Scenario.

Definition show_UnOp (op : UnOp) : string :=
  match op with
  | Not => "~"
  | Neg => "-"
  end.

Definition show_BinOp (op : BinOp) : string :=
  match op with
  | Eq => "="
  | And => "&"
  | Or => "|"
  | Plus => "+"
  | Times => "*"
  end.

Fixpoint show_Expr (e : Expr) : string :=
  match e with
  | Var v => v                  (* TODO *)
  | LitInt n => "0"             (* TODO *)
  | LitFloat q => "0.0"         (* TODO *)
  | LitBool b => "#t"           (* TODO *)
  | UnOpExpr op body =>
    show_UnOp op ++ show_Expr body
  | BinOpExpr op lhs rhs =>
    "(" ++ show_Expr lhs ++ show_BinOp op ++ show_Expr rhs ++ ")"
  end.

Fixpoint show_Cmd (c : Cmd) : string :=
  match c with
  | Assign v e => v ++ ":=" ++ show_Expr e
  | Raise e args => "raise " ++ e ++ "args" (* TODO *)
  | If cond ctrue cfalse =>
    "if (" ++ show_Expr cond ++ ") then {\n"
           ++ show_Cmd ctrue ++ "} else {\n"
           ++ show_Cmd cfalse ++ "}"
  | Seq c1 c2 => show_Cmd c1 ++ ";\n" ++ show_Cmd c2
  end.