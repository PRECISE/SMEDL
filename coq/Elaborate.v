Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.Strings.String.
Require Import Types.
Require Import AST.
Require Import ElaboratedAST.

Open Scope type.

Definition bind {a b : Type} (f : a -> option b) (x : option a) : option b :=
  match x with
  | None => None
  | Some x' => f x'
  end.

Definition bind2 {a b c : Type} (f : a -> b -> option c) (x : option a) (y : option b) : option c :=
  match (x, y) with
  | (None, _) => None
  | (_, None) => None
  | (Some x', Some y') => f x' y'
  end.

Arguments existT {_} {_} _ _.
Arguments exist {_} {_} _ _.

Definition check_UnOpExpr {free_vars : list string}
           (env : var free_vars -> Ty)
           (op : AST.UnOp)
           (e : { ty : Ty & ElaboratedAST.Expr env ty}) :
  option { ty : Ty & ElaboratedAST.Expr env ty } :=
  match (op, e) with
  | (AST.Not, existT SBool e') =>
    Some (existT SBool (UnOpExpr Not e'))
  | (AST.Neg, existT SInt e') =>
    Some (existT SInt (UnOpExpr INeg e'))
  | (AST.Neg, existT SFloat e') =>
    Some (existT SFloat (UnOpExpr FNeg e'))
  | _ => None
  end.

Definition check_BinOpExpr {free_vars : list string}
                (env : var free_vars -> Ty)
                (op : AST.BinOp)
                (lhs : { ty : Ty & ElaboratedAST.Expr env ty})
                (rhs : { ty : Ty & ElaboratedAST.Expr env ty }) :
  option { ty : Ty & ElaboratedAST.Expr env ty } :=
  match (op, lhs, rhs) with
  | (AST.And, existT SBool lhs', existT SBool rhs') =>
    Some (existT SBool (BinOpExpr And lhs' rhs'))
  | (AST.Or, existT SBool lhs', existT SBool rhs') =>
    Some (existT SBool (BinOpExpr Or lhs' rhs'))
  | (AST.Plus , existT SInt lhs', existT SInt rhs') =>
    Some (existT SInt (BinOpExpr IPlus lhs' rhs'))
  | (AST.Times , existT SInt lhs', existT SInt rhs') =>
    Some (existT SInt (BinOpExpr ITimes lhs' rhs'))
  | (AST.Plus , existT SFloat lhs', existT SFloat rhs') =>
    Some (existT SFloat (BinOpExpr FPlus lhs' rhs'))
  | (AST.Times , existT SFloat lhs', existT SFloat rhs') =>
    Some (existT SFloat (BinOpExpr FTimes lhs' rhs'))
  | _ => None
  end.

Fixpoint check_Expr {free_vars : list string}
         (env : var free_vars -> Ty)
         (e : AST.Expr) :
  option { ty : Ty & ElaboratedAST.Expr env ty } :=
  match e with
  | AST.Var v => match in_dec string_dec v free_vars with
                 | left pf => Some (existT (env (exist v pf))
                                           (Var (exist v pf)))
                 | right _ => None
                 end
  | AST.LitInt n =>
    Some (existT SInt (ElaboratedAST.LitInt n))
  | AST.LitFloat q =>
    Some (existT SFloat (ElaboratedAST.LitFloat q))
  | AST.LitBool b =>
    Some (existT SBool (ElaboratedAST.LitBool b))
  | AST.UnOpExpr op e' =>
    bind (check_UnOpExpr env op) (check_Expr env e')
  | AST.BinOpExpr op lhs rhs =>
    bind2 (check_BinOpExpr env op) (check_Expr env lhs) (check_Expr env rhs)
  end.

Fixpoint check_Cmd
         {globals : list string}
         (global_env : var globals -> Ty)
         {events : list string}
         {event_params : event events -> list string}
         (event_env : forall (e : event events), event_param events event_params e -> Ty)
         (e : AST.Cmd) :
  option (ElaboratedAST.Cmd global_env event_env) :=
  match e with
  | AST.Assign v e =>
    match in_dec string_dec v globals with
    | right _ => None
    | left pf => match check_Expr global_env e with
                 | None => None
                 | Some (existT actual e') =>
                   let expected := global_env (exist v pf) in
                   match ty_dec expected actual with
                   | right _ => None
                   | left refl =>
                     Some (Assign event_env
                                  (exist v pf)
                                  (eq_rec_r _ e' refl))
                   end
                 end
    end
  | AST.Raise f e =>
    match in_dec string_dec f events with
    | right _ => None
    | left pf => None           (* TODO *)
    end
  end.