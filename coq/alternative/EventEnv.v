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
    event_airity : {name : string | In events name} -> nat;
    lookup :
      forall (ev : {n : string | In events n}),
        Vector.t Ty (event_airity ev);
    param_name :
      forall (ev : {n : string | In events n}),
        Vector.t string (event_airity ev);
    param_names_unique :
      forall (ev : {n : string | In events n})
             (n1 n2 : Fin.t (event_airity ev)),
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
    (event_airity Δ ev)
    _.

Module Notations.
  Notation "ev ∈ Δ" := (In (events Δ) ev)
                         (at level 40).

  Notation "Δ ![ ev ; p ]" := (nth (lookup Δ ev) p)
                                (at level 50).

  Notation "Δ ?[ ev ; p ]" := (nth (param_name Δ ev) p)
                                (at level 50).

  Notation "Δ #[ ev ]" := (event_airity Δ ev)
                            (at level 50).

  Notation "Γ +![ Δ ; ev ]" := (extend_with_event Γ Δ ev)
                                 (at level 50).
End Notations.
Export Notations.

(* Lemma EventEnv_equiv : forall events event_airity lookup param_name param_names_unique events' event_airity' lookup' param_name' param_names_unique', *)
(*     Same_set _ events events' -> *)
(*     (forall ev ev', *)
(*         proj1_sig ev = proj1_sig ev' -> *)
(*         (event_airity ev = event_airity' ev') /\ *)
(*         (forall p p', *)
(*             Fin.to_nat p = Fin.to_nat p' -> *)
(*             (nth (lookup ev) p = nth (lookup' ev' p')) /\ *)
(*             (nth (param_name ev) p = nth (param_name' ev') p')) /\ *)
(*         (param_names_unique ev = param_names_unique' ev)) -> *)
(*     make events event_airity lookup param_name param_names_unique *)
(*     =  *)
(*     make events' event_airity' lookup' param_name' param_names_unique'. *)