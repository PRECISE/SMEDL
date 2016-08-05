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

Ltac inversion_VarEnv :=
  match goal with
  | [ H : HasTy_VarEnv _ _ |- _ ] =>
    let Hunique := fresh "Hunique" in
    let Hdom := fresh "Hdom" in
    let Hlookup := fresh "Hlookup" in
    inversion_clear H as [Hunique Hdom Hlookup]
  end.

Ltac inversion_EventEnv :=
  match goal with
  | [ H : HasTy_EventEnv _ _ |- _ ] =>
    let Hdom := fresh "Hdom" in
    let Hunique := fresh "Hunique" in
    let Hparam_unique := fresh "Hparam_unique" in
    let Harity := fresh "Harity" in
    let Hlookup := fresh "Hlookup" in
    let Hparam_name := fresh "Hparam_name" in
    inversion_clear H as
        [Hdom Hunique Hparam_unique Harity Hparam_name Hlookup]
  end.

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
  intros; repeat inversion_EventEnv.
  destruct Δ1, Δ2.
  simpl in *.

  assert (Heq : events0 = events)
    by (apply Extensionality_Ensembles;
        unfold Same_set, Included;
        firstorder).
  subst.

  assert (Heq : arity0 = arity).
  { extensionality e.
    specialize (Harity e).
    specialize (Harity0 e).
    destruct e as [n Hn].
    specialize (Hdom n).
    inversion Hdom as [_ Hin_in].
    specialize (Hin_in Hn).
    inversion Hin_in as [ps Hin].
    specialize (Harity ps Hin).
    specialize (Harity0 ps Hin).
    rewrite <- Harity, <- Harity0;
      simpl; auto.
  }
  subst.

  assert (Heq : param_name0 = param_name).
  { extensionality e.
    apply Vector.eq_nth_iff; intros; subst.
    specialize (Hparam_name e).
    specialize (Hparam_name0 e).
    destruct e as [n Hn].
    specialize (Hdom n).
    inversion Hdom as [_ Hin_in].
    specialize (Hin_in Hn).
    inversion Hin_in as [ps Hin].
    specialize (Hparam_name ps Hin p2).
    specialize (Hparam_name0 ps Hin p2).
    rewrite Hparam_name0 in Hparam_name.
    inversion Hparam_name.
    auto.
  }
  subst.

  assert (Heq : lookup0 = lookup).
  { extensionality e.
    apply Vector.eq_nth_iff; intros; subst.
    specialize (Hlookup e).
    specialize (Hlookup0 e).
    destruct e as [n Hn].
    specialize (Hdom n).
    inversion Hdom as [_ Hin_in].
    specialize (Hin_in Hn).
    inversion Hin_in as [ps Hin].
    specialize (Hlookup ps Hin p2).
    specialize (Hlookup0 ps Hin p2).
    rewrite Hlookup0 in Hlookup.
    inversion Hlookup.
    auto.
  }
  subst.

  assert (Heq : param_names_unique0 = param_names_unique).
  { extensionality e.
    extensionality n1.
    extensionality n2.
    extensionality Hn1n2.
    Require Import Eqdep_dec.
    apply eq_proofs_unicity.
    intros x y.
    destruct (Fin.eq_dec x y); intuition.
  }
  subst.

  trivial.
Qed.

(* The global variable declarations completely determine the global variable
environment, when one exist. *)
Lemma HasTy_Var_unique : forall gs Γ1 Γ2,
    HasTy_VarEnv gs Γ1 ->
    HasTy_VarEnv gs Γ2 ->
    Γ1 = Γ2.                  (* TODO: = or some other equivalence? *)
Proof.
  intros; repeat inversion_VarEnv.
  destruct Γ1, Γ2; simpl in *.

  assert (vars0 = vars)
    by (apply Extensionality_Ensembles;
        unfold Same_set, Included;
        firstorder).
  subst.

  assert (lookup = lookup0).
  { extensionality v.
    destruct v as [n Hn].
    specialize (Hlookup n Hn).
    specialize (Hlookup0 n Hn).
    specialize (Hdom n).
    inversion Hdom as [Hin_maps Hmaps_in].
    specialize (Hin_maps Hn).
    inversion Hin_maps as [ty Hty].
    specialize (Hlookup ty).
    specialize (Hlookup0 ty).
    inversion Hlookup as [Hlookup_maps Hmaps_lookup].
    inversion Hlookup0 as [Hlookup_maps0 Hmaps_lookup0].
    specialize (Hmaps_lookup Hty).
    specialize (Hmaps_lookup0 Hty).
    rewrite Hmaps_lookup.
    rewrite Hmaps_lookup0.
    trivial.
  }
  subst.
  trivial.
Qed.

Lemma VarEnv_shrink : forall {Γ ty gs} n Hn,
  HasTy_VarEnv ((n, ty) :: gs) Γ ->
  HasTy_VarEnv gs (VarEnv.remove Γ (exist n Hn)).
Proof.
  intros; inversion_VarEnv.
  econstructor.

  - inversion Hunique; auto.
  - intro n'; specialize (Hdom n');
      inversion Hdom as [Hdom_ty Hty_dom].
    split.
    + inversion 1 as [Hin Hsingle].
      apply Hdom_ty in Hin as Hex.
      inversion Hex as [? Hmaps].
      inversion Hmaps as [Hhd | ?];
        [inversion Hhd; subst|];
        firstorder.
    + inversion 1 as [ty' Hin].
      unfold VarEnv.remove, Subtract, Setminus, In in *.
      simpl in *.
      split; eauto using List.in_cons.
      inversion 1; subst.
      inversion Hunique; subst.
      apply (List.in_map fst) in Hin.
      auto.
  - intros n' Hn' ty'.
    destruct Hn' as [Hin' Hneq].
    specialize (Hlookup n' Hin' ty').
    inversion_clear Hlookup as [Hlookup_maps Hmaps_lookup].
    split; [intro Hlookup | intro Hmaps].
    + apply Hlookup_maps in Hlookup.
      inversion Hlookup as [Heq | ?]; auto.
      (* The case that auto doesn't handle is the one where the variable being
      looked up is the one that was removed.
      *)
      exfalso.
      inversion Heq; subst.
      intuition.
    + apply Hmaps_lookup.
      eauto using List.in_cons.
Qed.

Hint Resolve VarEnv_shrink.

Lemma VarEnv_maps_lookup : forall n gs Γ,
    In (VarEnv.vars Γ) n ->
    HasTy_VarEnv gs Γ ->
    List.In n (List.map fst gs).
Proof.
  intros.
  inversion_VarEnv.
  specialize (Hdom n).
  specialize (Hlookup n H).
  inversion Hdom as [Hin_maps Hmaps_in].
  specialize (Hin_maps H).
  inversion Hin_maps as [ty Hmaps].
  apply (List.in_map fst) in Hmaps.
  auto.
Qed.