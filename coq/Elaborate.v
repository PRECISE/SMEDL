Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.Strings.String.
Require Import Coq.Program.Program.

Require Import SMEDL.Types.
Require SMEDL.AST.
Require Import SMEDL.ElaboratedAST.
Require Import SMEDL.These.

Open Scope type.
Open Scope string.
Open Scope program_scope.

Definition TypeError := string.
Definition TC a := Chronicle TypeError a.

Arguments existT {_} {_} _ _.
Arguments exist {_} {_} _ _.

Program Definition check_UnOpExpr
        {ty : Ty}
        {free_vars : list string}
        (env : var free_vars -> Ty)
        (op : AST.UnOp)
        (e : Expr env ty) :
  TC { ty : Ty & Expr env ty } :=
  match (op, ty) with
  | (AST.Not, SBool) =>
    ret (existT SBool (UnOpExpr Not e))
  | (AST.Neg, SInt) =>
    ret (existT SInt (UnOpExpr INeg e))
  | (AST.Neg, SFloat) =>
    ret (existT SFloat (UnOpExpr FNeg e))
  | (op, _) =>
    confess ("Unary operation "
               ++ AST.show_UnOp op
               ++ " cannot apply to expression of type "
               ++ show_Ty ty ++ ".")
  end.
Solve Obligations with (simpl; intuition; congruence).

Program Definition check_BinOpExpr
        {free_vars : list string}
        {ty_lhs : Ty}
        {ty_rhs : Ty}
        (env : var free_vars -> Ty)
        (op : AST.BinOp)
        (lhs : Expr env ty_lhs)
        (rhs : Expr env ty_rhs) :
  TC { ty : Ty & Expr env ty } :=
  match (op, ty_lhs, ty_rhs) with
  | (AST.And, SBool, SBool) =>
    ret (existT SBool (BinOpExpr And lhs rhs))
  | (AST.Or, SBool, SBool) =>
    ret (existT SBool (BinOpExpr Or lhs rhs))
  | (AST.Plus, SInt, SInt) =>
    ret (existT SInt (BinOpExpr IPlus lhs rhs))
  | (AST.Times, SInt, SInt) =>
    ret (existT SInt (BinOpExpr ITimes lhs rhs))
  | (AST.Plus, SFloat, SFloat) =>
    ret (existT SFloat (BinOpExpr FPlus lhs rhs))
  | (AST.Times,SFloat, SFloat) =>
    ret (existT SFloat (BinOpExpr FTimes lhs rhs))
  | (op, _, _) =>
    confess ("Binary operation "
               ++ AST.show_BinOp op
               ++ " cannot apply to expressions of type "
               ++ show_Ty ty_lhs ++ " and "
               ++ show_Ty ty_rhs ++ ".")
  end.
Solve Obligations with (simpl; intuition congruence).

Fixpoint check_Expr {free_vars : list string}
         (env : var free_vars -> Ty)
         (e : AST.Expr) :
  TC { ty : Ty & Expr env ty } :=
  match e with
  | AST.Var v => match in_dec string_dec v free_vars with
                 | left pf =>
                   ret (existT (env (exist v pf))
                               (Var (exist v pf)))
                 | right _ =>
                   confess ("Variable "
                              ++ v ++ " not in scope")
                 end
  | AST.LitInt n =>
    ret (existT SInt (LitInt n))
  | AST.LitFloat q =>
    ret (existT SFloat (LitFloat q))
  | AST.LitBool b =>
    ret (existT SBool (LitBool b))
  | AST.UnOpExpr op body =>
    do (ty, body') <- check_Expr env body;
       check_UnOpExpr env op body'
  | AST.BinOpExpr op lhs rhs =>
    do (lhs_ty, lhs') <- check_Expr env lhs;
    do (rhs_ty, rhs') <- check_Expr env rhs;
       check_BinOpExpr env op lhs' rhs'
  end.

Program Fixpoint check_Cmd
         {globals : list string}
         {events : list string}
         {event_params : event events -> list string}
         (global_env : var globals -> Ty)
         (event_env : forall (e : event events), event_param events event_params e -> Ty)
         (c : AST.Cmd) :
  TC (Cmd global_env event_env) :=
  match c with
  | AST.Assign v e =>
    match in_dec string_dec v globals with
    | right _ =>
      confess ("Variable " ++ v ++ " not in scope")
    | left pf =>
      do (e_ty, e') <- check_Expr _ e;
      let expected := global_env (exist v pf) in
      match ty_dec expected e_ty with
      | right _ =>
        confess ("Assignment to variable "
                   ++ v ++ " expects type "
                   ++ show_Ty expected ++ ", but "
                   ++ show_Ty e_ty ++ " provided.")
      | left refl =>
        ret (Assign (exist v pf)
                    (eq_rec_r _ e' refl))
      end
    end
  | AST.Raise e args =>
    match in_dec string_dec e events with
    | right _ =>
      confess ("Event " ++ e ++ " not in scope.")
    | left pf =>
      match tt with
      | _ =>
        ret (Raise e (fun p => _))
      end
    end
  | AST.If cond c1 c2 =>
    do (cond_ty, cond') <- check_Expr _ cond ;
       match cond_ty with
       | SBool =>
         do c1' <- check_Cmd _ _ c1 ;
         do c2' <- check_Cmd _ _ c2 ;
            ret (If cond' c1' c2')
       | _ =>
         confess ("Condition expression has type "
                    ++ show_Ty cond_ty
                    ++ ", but type SBool expected.")
       end
  | AST.Seq c1 c2 =>
    do c1' <- check_Cmd _ _ c1 ;
    do c2' <- check_Cmd _ _ c2 ;
       ret (Seq c1' c2')
  end.
Obligation 2.
compare (List.length args)
        (List.length (event_params (exist e pf)));
  intros.
apply (map (check_Expr global_env)) in args as args'.
Check nth.
Check In_nth.
assert (Hin := In_nth (event_params (exist e pf)) p "").
inversion Hin.

nth_in_or_default:
  forall (A : Type) (n : nat) (l : list A) (d : A),
  {In (nth n l d) l} + {nth n l d = d}


nth_In:
  forall (A : Type) (n : nat) (l : list A) (d : A),
  (n < Datatypes.length l)%nat -> In (nth n l d) l

assert (event_env' := event_env (exist e pf)).
assert (p_ty := event_env' p).

SearchAbout In.