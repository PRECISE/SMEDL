(* SMEDL Abstract Syntax with type elaborations. *)
Inductive Ty : Set :=
| SBool : Ty
| SInt : Ty
| SFloat : Ty
| SProduct : Ty -> Ty -> Ty.

Lemma ty_dec (t1 : Ty) : forall t2, { t1 = t2 } + { t1 <> t2 }.
Proof.
  induction t1;
    destruct t2;
    try intuition congruence.

  specialize (IHt1_1 t2_1).
  specialize (IHt1_2 t2_2).

  intuition congruence.
Qed.

Require Import Coq.Strings.String.

Fixpoint show_Ty (ty : Ty) : string :=
  match ty with
  | SBool => "bool"
  | SInt => "int"
  | SFloat => "float"
  | SProduct lhs rhs =>
    "(" ++ show_Ty lhs ++ "*" ++ show_Ty rhs ++ ")"
  end.