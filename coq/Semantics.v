Require Import Coq.Program.Program.
Require Import Coq.Strings.String.
Require Import Coq.QArith.QArith.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import SMEDL.Util.
Require Import SMEDL.Types.
Require Import SMEDL.AST.
Require SMEDL.VarEnv.
Import SMEDL.VarEnv.Coercions.
Require SMEDL.EventEnv.

Require Import SMEDL.Typing.
Require Import SMEDL.TypingFacts.

Require Import SMEDL.Machine.

Arguments exist {_ _} _ _.
Arguments existT {_ _} _ _.
Arguments Empty_set {_ _}.

Fixpoint compile_type (ty : Ty) : Set :=
  match ty with
  | SInt => nat
  | SBool => bool
  | SFloat => Q
  | SProduct lhs rhs => compile_type lhs * compile_type rhs
  end.

Fixpoint initial_value (ty : Ty) : (compile_type ty) :=
  match ty with
  | SInt => 0%nat
  | SBool => false
  | SFloat => 0%Q
  | SProduct lhs rhs => (initial_value lhs, initial_value rhs)
  end.

Program Definition GlobalDecls_global_state (gs : list GlobalDecl) : Type :=
  forall (v : { n : string | List.In n (List.map fst gs) }),
    compile_type (lookup string_dec v gs _).

Program Fixpoint SM_states (sm : Scenario) : Ensemble string :=
  fun x => List.In x (app (List.map Transition_source sm)
                          (List.map Transition_dest sm)).

Definition SM_state (gs : list GlobalDecl) (sm : Scenario) : Type :=
  { n : string | In (SM_states sm) n } * GlobalDecls_global_state gs.

(* e is the tag that tells you which event. It is paired with a function from
   parameter names to values of the correct types for the parameters. *)
Program Definition EventDecls_events (es : list EventDecl) : Type :=
  { e : { n : string | List.In n (List.map fst es) } &
        let ps := lookup string_dec e es _ in
        forall p : { n : string | List.In n (List.map fst ps) },
          compile_type (lookup string_dec p ps _) }.

Program Definition GlobalDecls_initial_state
        (gs : list GlobalDecl) : GlobalDecls_global_state gs :=
  fun p => initial_value (lookup string_dec p gs _).

Program Definition transition_starts_with (src : string) (t : Transition) : bool :=
  Sumbool.bool_of_sumbool (string_dec src (Transition_source t)).

(*
Program Fixpoint eval_expr
        {ty : Ty}
        {gs : list GlobalDecl}
        {es : list EventDecl}
        (s : GlobalDecls_global_state gs)
        (σ : EventDecls_events es)
         (Γ : VarEnv.t)
        (HΓ : HasTy_VarEnv gs Γ)
        (expr : Expr)
        (Hsm : HasTy_Expr Γ expr ty) : compile_type ty :=
  match ty with
  | SInt => match expr with
            | LitInt n => n
            | Var v => _
            | UnOpExpr op body => eval_expr s σ _ HΓ body _
            | BinOpExpr op lhs rhs => _
            | _ => _
            end
  | SFloat => match expr with
              | LitFloat q => q
              | _ => _
              end
  | SBool => match expr with
             | LitBool b => b
             | _ => _
             end
  | _ => _
  end.
(* there has to be a better way to do this... in particular, I want to be able
to specify (s v) up front, and only use Ltac to prove the type conversion. *)
Obligation 1.
unfold GlobalDecls_global_state in s.
assert (List.In v (map fst gs)) as Hin.
{ inversion Hsm; subst.
  destruct v0.
  simpl.
  inversion HΓ as [_ Hdom _].
  specialize (Hdom x).
  inversion Hdom as [Hdom' _].
  specialize (Hdom' i).
  inversion Hdom'.
  apply (List.in_map fst) in H.
  simpl in H.
  exact H.
}
specialize (s (exist v Hin)).
simpl in s.
assert (compile_type (lookup string_dec v gs Hin) = nat).
{
  inversion Hsm; subst.
  destruct v0.
  inversion HΓ as [? Hdom Hlookup].
  specialize (Hdom x).
  inversion Hdom as [Hin_maps Hmaps_in].
  specialize (Hin_maps i).
  inversion_clear Hin_maps as [ty Hdom_in].
  admit.
}
rewrite H in s.
exact s.
Admitted.

Program Definition SM_transition
        {gs : list GlobalDecl}
        {es : list EventDecl}
        (sm : Scenario)
        (s : SM_state gs sm)
        (σ : EventDecls_events es)
        (Δ : EventEnv.t)
        (HΔ : HasTy_EventEnv es Δ)
        (Γ : VarEnv.t)
        (HΓ : HasTy_VarEnv gs Γ)
        (Hsm : HasTy_Scenario Δ Γ sm) : option (SM_state gs sm) :=
  let (src,_) := s in
  let ts := filter (transition_starts_with src) sm in
  let t := find (guard_passes s) ts in
  (Transition_dest t, (eval_command t) s).

Program Definition LM_output
        (lm : LocalMonitor)
        (Hlm : HasTy_LM lm)
        (s : LM_state lm)
        (σ : LM_input_events lm) : LM_input_events lm :=
  _.

Definition LM_machine
        (lm : LocalMonitor)
        (Hlm : HasTy_LM lm)
  : Machine (LM_input_events lm) (LM_output_events lm) :=
  mkMachine
    (LM_state lm)
    (LM_initial_state lm)
    (LM_transition lm Hlm)
    (LM_output lm Hlm).
*)