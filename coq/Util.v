Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Coq.Sets.Ensembles.

Arguments In {_} _ _.
Arguments Add {_} _ _ _.

Program Definition extend
        {A : Type}
        {B : Type}
        {A_dec : forall (x y : A), {x = y} + {x <> y}}
        {ps : Ensemble A}
        (f : {x : A | In ps x} -> B)
        (a : A)
        (b : B)
        (x : { x : A | In (Add ps a) x }) : B :=
  if A_dec a x
  then b
  else f x.
Obligation 1.
inversion H0; subst; auto.
inversion H1.
contradiction.
Qed.

Fixpoint lookup_option
        {A B : Type}
        (A_dec : forall (x y : A), { x = y } + { x <> y })
        (x : A)
        (xys : list (A * B)) : option B :=
  match xys with
  | nil => None
  | (x',y)::xys' =>
    if A_dec x x'
    then Some y
    else lookup_option A_dec x xys'
  end.

Program Definition lookup
        {A B : Type}
        (A_dec : forall (x y : A), { x = y } + { x <> y })
        (x : A)
        (xys : list (A * B))
        (Hin : List.In x (List.map fst xys)) : B :=
  match lookup_option A_dec x xys with
  | Some x' => x'
  | None => _
  end.
Obligation 1.
exfalso.
induction xys.
inversion Hin.
destruct a; simpl in *.
destruct (A_dec x a); subst; simpl in *.
inversion Heq_anonymous.
apply IHxys.
inversion Hin; subst; try congruence.
auto.
Qed.