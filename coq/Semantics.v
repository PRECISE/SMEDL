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

Program Definition VarEnv_remove (Γ : VarEnv.t) (v : Γ) : VarEnv.t :=
  VarEnv.make (Subtract _ (VarEnv.vars Γ) (proj1_sig v))
              (fun v' => VarEnv.lookup Γ v').
Obligation 1.
destruct H.
exact H.
Defined.

Program Definition weaken_var {Γ : VarEnv.t} {v : Γ} (v' : VarEnv_remove Γ v) : Γ :=
   v'.
Obligation 1.
apply (VarEnv_remove_obligation_1 Γ v).
Defined.

Lemma shrink_env : forall {Γ ty gs} v,
  HasTy_VarEnv (((proj1_sig v), ty) :: gs) Γ ->
  HasTy_VarEnv gs (VarEnv_remove Γ v).
Proof.
  intros.
  eapply HasTy_VarEnv_intro; inversion H.
  - inversion H0; eauto.
  - intros.
    split; intros;
      specialize (H1 n);
      inversion H1; clear H1.
    + clear H5.
      inversion H3.
      specialize (H4 H1).
      inversion H4.
      exists x.
      inversion H6.
      * inversion H7.
        subst.
        clear H7.
        unfold not in H5.
        exfalso.
        apply H5.
        apply In_singleton.
      * exact H7.
    + clear H4.
      unfold VarEnv_remove; simpl.
      unfold Subtract, Setminus, In in *.
      split.
      * inversion H3.
        eauto using List.in_cons.
      * unfold not.
        intros.
        inversion H1.
        destruct v.
        simpl in *.
        subst.
        clear H2 H5 H1.
        inversion H3.
        clear H3.
        inversion H0.
        subst.
        apply (in_map fst) in H1.
        simpl in *.
        contradiction.
  - intros.
    split; intros;
      specialize (H2 (weaken_var v0) ty0);
      destruct v0 as [n0 Hn0];
      inversion H2; clear H2.
    + clear H5.
      assert (VarEnv.lookup Γ (weaken_var (exist n0 Hn0))
              = VarEnv.lookup (VarEnv_remove Γ v) (exist n0 Hn0))
        by (unfold VarEnv_remove, weaken_var; auto);
      subst.
      specialize (H4 H2).
      inversion H4.
      * inversion H3.
        destruct v, Hn0.
        subst; simpl in *.
        unfold not in n.
        contradiction n.
        apply In_singleton.
      * assumption.
    + clear H4.
      apply H5.
      apply in_cons.
      unfold weaken_var.
      unfold weaken_var_obligation_1.
      unfold VarEnv_remove_obligation_1.
      destruct Hn0.
      simpl in *.
      assumption.
Qed.

Program Fixpoint LM_state'
         (gs : list GlobalDecl)
         (Γ : VarEnv.t)
         (Hty : HasTy_VarEnv gs Γ) : Type :=
  match gs with
  | List.nil => unit
  | (n,ty)::gs' => compile_type ty
                   * LM_state' gs'
                               (VarEnv_remove Γ n)
                               (shrink_env n Hty)
  end.
Obligation 1.
inversion Hty.
specialize (H0 n).
inversion H0; clear H0.
clear H2.
apply H3; clear H3.
exists ty.
apply in_eq.
Qed.

(* Program Definition LM_state (lm : LocalMonitor) (Hty : HasTy_LM lm) : Type := *)
(*   LM_state' (globals lm) _ _. *)

(* Definition LM_input (lm : LocalMonitor) : Type := *)
(*   lm . *)

(* Definition LM_output (lm : LocalMonitor) : Type := *)
(*   lm . *)