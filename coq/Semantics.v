Require Import Coq.Strings.String.
Require Import Coq.QArith.QArith.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
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

Fixpoint compile_type (ty : Ty) : Set :=
  match ty with
  | SInt => nat
  | SBool => bool
  | SFloat => Q
  | SProduct lhs rhs => compile_type lhs * compile_type rhs
  end.

Program Fixpoint LM_state'
         (gs : list GlobalDecl)
         (Γ : VarEnv.t)
         (Hty : HasTy_VarEnv gs Γ) : Type :=
  match gs with
  | List.nil => unit
  | (n,ty)::gs' => compile_type ty
                   * LM_state' gs'
                               (VarEnv.remove Γ n)
                               (VarEnv_shrink n Hty)
  end.
Obligation 1.
inversion Hty as [_ Hdom _].
specialize (Hdom n).
inversion Hdom.
eauto using in_eq.
Qed.

(* Program Definition LM_state (lm : LocalMonitor) (Hty : HasTy_LM lm) : Type := *)
(*   LM_state' (globals lm) _ _. *)

(* Definition LM_input (lm : LocalMonitor) : Type := *)
(*   lm . *)

(* Definition LM_output (lm : LocalMonitor) : Type := *)
(*   lm . *)