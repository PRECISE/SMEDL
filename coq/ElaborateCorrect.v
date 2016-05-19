
Definition forget_elab_BinOp {ty : Ty} (op : BinOp ty) : AST.BinOp :=
  match op with
  | And => AST.And
  | Or => AST.Or
  | IPlus => AST.Plus
  | ITimes => AST.Times
  | FPlus => AST.Plus
  | FTimes => AST.Times
  end.

Definition forget_elab_UnOp {ty : Ty} (op : UnOp ty) : AST.UnOp :=
  match op with
  | Not => AST.Not
  | INeg => AST.Neg
  | FNeg => AST.Neg
  end.

Definition forget_elab_var
           {vars : list string}
           (v : var vars) : string :=
  let (x, H) := v in
  (fun _ : In x vars => x) H.

Fixpoint forget_elab_Expr
         {vars : list string}
         {env : var vars -> Ty}
         {ty : Ty}
         (e : Expr env ty) :
  AST.Expr :=
  match e with
  | Var v => AST.Var (forget_elab_var v)
  | LitBool b => AST.LitBool b
  | LitInt n => AST.LitInt n
  | LitFloat q => AST.LitFloat q
  | EqExpr lhs rhs =>
    AST.BinOpExpr AST.Eq
      (forget_elab_Expr lhs)
      (forget_elab_Expr rhs)
  | BinOpExpr op lhs rhs =>
    AST.BinOpExpr (forget_elab_BinOp op)
                  (forget_elab_Expr lhs)
                  (forget_elab_Expr rhs)
  | UnOpExpr op e' =>
    AST.UnOpExpr (forget_elab_UnOp op)
                 (forget_elab_Expr e')
  end.

Ltac invert_false :=
  match goal with
  | [ H : _ |- _ ] => solve [inversion H]
  end.

Ltac invert_unop :=
  match goal with
  | [ H : bind (check_Expr ?env ?e) (check_UnOpExpr ?env ?u) = These_that _ |- _ ] =>
    unfold bind in H;
    let s := fresh "s" in
    destruct (check_Expr env e) as [?|s|? s];
    try invert_false;
    let x := fresh "x" in
    let e := fresh "e" in
    destruct u; destruct s as [x e]; destruct x;
    simpl in H;
    try invert_false
  end.

Ltac invert_binop :=
  match goal with
  | [ H : bind2 (check_Expr ?env ?e1) (check_Expr ?env ?e2) (check_BinOpExpr ?env ?op)
          = These_that _
      |- _ ] =>
    let s1 := fresh "s" in
    let s2 := fresh "s" in
    destruct (check_Expr env e1) as [?|s1|? s1];
    destruct (check_Expr env e2) as [?|s2|? s2];
    try invert_false;
    destruct op;
    let x1 := fresh "x" in
    let x2 := fresh "x" in
    destruct s1 as [x1 ?];
    destruct s2 as [x2 ?];
    destruct x1, x2;
    simpl in H;
    try invert_false
  end.

(* Ltac foo H env e := *)

Lemma foo : forall {vars : list string}
                   {env : var vars -> Ty}
                   (ty : Ty)
                   (e : AST.Expr)
                   (e' : Expr env ty),
    check_Expr env e = These_that (existT ty e') -> forget_elab_Expr e' = e.
Proof.
  induction e; destruct e'; simpl; intros; eauto;
    try invert_false;
    try (solve [ destruct (in_dec string_dec s vars); try invert_false
               | inversion H; trivial
               | invert_unop
               | invert_binop ]).
  - destruct (in_dec string_dec s vars); try invert_false.
    destruct x; simpl in *.
    inversion H.
    trivial.
  - rewrite IHe;
      destruct u0;
      invert_unop;
      simpl in H;
      inversion H;
      solve [trivial | congruence ].
  - rewrite IHe1;
    [rewrite IHe2 | ];
    destruct b0;
      invert_binop;
      simpl in H;
      inversion H;
      solve [trivial | congruence ].
Qed.


Definition forget_elab_event {events : list string} (e : event events) : string :=
  let (name, _) := e in name.

Print event_param.
  
Fixpoint forget_elab_Cmd
           {globals : list string}
           {global_env : var globals -> Ty}
           {events : list string}
           {event_params : event events -> list string}
           {event_env : forall (e : event events), event_param events event_params e -> Ty}
           (c : Cmd global_env event_env) :=
  match c with
  | Assign v e =>
    AST.Assign (forget_elab_var v) (forget_elab_Expr e)
  | Raise ev args =>
    AST.Raise (forget_elab_event ev) (map forget_elab_Expr (map args (event_params ev)))
  | If e c1 c2 =>
    AST.If (forget_elab_Expr e) (forget_elab_Cmd c1) (forget_elab_Cmd c2)
  | Seq c1 c2 =>
    AST.Seq (forget_elab_Cmd c1) (forget_elab_Cmd c2)
  end.


Lemma check_Cmd_faithful :
  forall {globals : list string}
         {global_env : var globals -> Ty}
         {events : list string}
         {event_params : event events -> list string}
         {event_env : forall (e : event events), event_param events event_params e -> Ty}
         (c : AST.Cmd)
         (c' : Cmd global_env event_env),
    check_Cmd c = These_that (existT c') -> forget_elab_Cmd c' = c.
Proof.