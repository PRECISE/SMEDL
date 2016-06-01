Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.
Require Import Coq.Sets.Ensembles.
Require Import SMEDL.Notation.
Require Import SMEDL.Types.
Require SMEDL.VarEnv.
Import SMEDL.VarEnv.Notations.
Import SMEDL.VarEnv.Coercions.

(** Event environments *)
Record t := make
  { events : Ensemble string;
    arity : {name : string | In events name} -> nat;
    lookup :
      forall (ev : {n : string | In events n}),
        Vector.t Ty (arity ev);
    param_name :
      forall (ev : {n : string | In events n}),
        Vector.t string (arity ev);
    param_names_unique :
      forall (ev : {n : string | In events n})
             (n1 n2 : Fin.t (arity ev)),
        nth (param_name ev) n1 = nth (param_name ev) n2 ->
        n1 = n2;
  }.

Module Coercions.
  Coercion EventEnv_event (Δ : t) : Type :=
    { ev : string | In (events Δ) ev }.
End Coercions.
Export Coercions.

Program Fixpoint Fin_fold {B : Type} {max : nat}
        (f : B -> Fin.t max -> B)
        (b : B)
        (p : nat)
        (Hp : p <= max) : B :=
  match p with
  | 0 => b
  | S p' =>
    Fin_fold f (f b (Fin.of_nat_lt Hp)) p' (Le.le_Sn_le _ _ Hp)
  end.

Program Definition extend_with_event
        (Γ : VarEnv.t)
        (Δ : t)
        (ev : Δ) : VarEnv.t :=
  Fin_fold
    (fun Γ p => Γ +[(nth (param_name Δ ev) p);
                     (nth (lookup Δ ev) p)])
    Γ
    (arity Δ ev)
    _.

Module Notations.
  Notation "ev ∈ Δ" := (In (events Δ) ev)
                         (at level 40).

  Notation "Δ ![ ev ; p ]" := (nth (lookup Δ ev) p)
                                (at level 50).

  Notation "Δ ?[ ev ; p ]" := (nth (param_name Δ ev) p)
                                (at level 50).

  Notation "Δ #[ ev ]" := (arity Δ ev)
                            (at level 50).

  Notation "Γ +![ Δ ; ev ]" := (extend_with_event Γ Δ ev)
                                 (at level 50).
End Notations.
Export Notations.