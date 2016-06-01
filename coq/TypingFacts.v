Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.
Require Import Coq.Sets.Ensembles.
Require Import SMEDL.Types.
Require Import SMEDL.AST.
Require SMEDL.VarEnv.
Import SMEDL.VarEnv.Notations.
Import SMEDL.VarEnv.Coercions.
Require SMEDL.EventEnv.
Import SMEDL.EventEnv.Notations.
Import SMEDL.EventEnv.Coercions.

Require Import SMEDL.Typing.

Arguments exist {_ _} _ _.
Arguments existT {_ _} _ _.

(* Equivalence of event environments relies on Ensemble extensionality and
 Functional Extensionality. Is that OK?*)

Require Import Coq.Logic.FunctionalExtensionality.

(* The event declarations completely determine the event type environment, when
one exists. *)
Lemma HasTy_EventEnv_unique : forall es Δ1 Δ2,
    HasTy_EventEnv es Δ1 ->
    HasTy_EventEnv es Δ2 ->
    Δ1 = Δ2.                  (* TODO: = or some other equivalence? *)
Proof.
  intros.
  inversion H; inversion H0.
  destruct Δ1, Δ2.
  simpl in *.

  assert (Heq : events0 = events)
    by (apply Extensionality_Ensembles;
        unfold Same_set, Included;
        firstorder).
  subst.

  assert (Heq : arity0 = arity).
  { extensionality x.
    specialize (H10 x).
    specialize (H4 x).
    destruct x.
    specialize (H7 x).
    inversion H7.
    specialize (H14 i).
    inversion H14.
    specialize (H10 x0).
    specialize (H4 x0).
    rewrite <- H10, <- H4;
      simpl; auto.
  }
  subst.

  assert (Heq : param_name0 = param_name).
  { extensionality x.
    apply Vector.eq_nth_iff; intros; subst.
    specialize (H5 x).
    specialize (H11 x).
    destruct x.
    specialize (H7 x).
    inversion H7.
    specialize (H14 i).
    inversion H14.
    specialize (H5 x0).
    specialize (H11 x0).
    simpl in *.
    specialize (H5 H15 p2).
    specialize (H11 H15 p2).
    rewrite H5 in H11.
    inversion H11.
    rewrite H17.
    auto.
  }
  subst.

  assert (Heq : lookup0 = lookup).
  { extensionality x.
    apply Vector.eq_nth_iff; intros; subst.
    specialize (H6 x).
    specialize (H12 x).
    destruct x.
    specialize (H7 x).
    inversion H7.
    specialize (H14 i).
    inversion H14.
    specialize (H6 x0).
    specialize (H12 x0).
    simpl in *.
    specialize (H6 H15 p2).
    specialize (H12 H15 p2).
    rewrite H6 in H12.
    inversion H12.
    rewrite H17.
    auto.
  }
  subst.

  assert (Heq : param_names_unique0 = param_names_unique).
  { extensionality x.
    extensionality n1.
    extensionality n2.
    extensionality Hn1n2.
    Require Import Eqdep_dec.
    apply eq_proofs_unicity.
    clear.
    intros.
    destruct (Fin.eq_dec x0 y); intuition.
  }
  subst.

  reflexivity.
Qed.

(* The global variable declarations completely determine the global variable
environment, when one exist. *)
Lemma HasTy_Var_unique : forall gs Γ1 Γ2,
    HasTy_VarEnv gs Γ1 ->
    HasTy_VarEnv gs Γ2 ->
    Γ1 = Γ2.                  (* TODO: = or some other equivalence? *)
Proof.
  intros.
  inversion H; inversion H0.
  destruct Γ1, Γ2; simpl in *.

  assert (vars0 = vars)
    by (apply Extensionality_Ensembles;
        unfold Same_set, Included;
        firstorder).
  subst.

  assert (lookup = lookup0).
  { extensionality v.
    specialize (H3 v).
    specialize (H6 v).
    destruct v.
    specialize (H2 x).
    inversion H2.
    specialize (H7 i).
    inversion H7 as [ty Hty].
    specialize (H3 ty).
    specialize (H6 ty).
    inversion H3.
    inversion H6.
    specialize (H10 Hty).
    specialize (H12 Hty).
    rewrite H10.
    rewrite H12.
    reflexivity.
  }
  subst.
  reflexivity.
Qed.