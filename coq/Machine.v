(** Basic state machine and trace definitions. Needs to be extended with
run-to-completion semantics, operations for synchronous products of machines,
and a mechanism for asynchronous machine communication via channels. *)
Require Import Coq.Lists.List.

Import ListNotations.

Section Machines.
  Variable Σ : Type.
  Variable Λ : Type.

  Record Machine (Σ Λ : Type) :=
    mkMachine {
        S : Type;
        S0 : S;
        δ : S -> Σ -> S;
        ω : S -> Σ -> list Λ
      }.

  Global Arguments mkMachine : default implicits.
  Global Arguments S : default implicits.
  Global Arguments S0 : default implicits.
  Global Arguments δ : default implicits.
  Global Arguments ω : default implicits.

  Section MachineSemantics.
    Variable M : Machine Σ Λ.

    Record Step : Type :=
      mkStep {
          source : S M;
          input : Σ;
          destination : S M;
          output : list Λ;
        }.

    Inductive Trace : list Step -> Prop :=
    | Trace_start : forall σ,
        Trace (mkStep (S0 M) σ (δ M (S0 M) σ) (ω M (S0 M) σ)
                      :: nil)
    | Trace_next : forall ts src σ s' σ' λs',
        Trace (mkStep s' σ' src λs'
                      :: ts) ->
        Trace (mkStep src σ (δ M src σ) (ω M src σ)
                      :: mkStep s' σ' src λs'
                      :: ts).

    Definition Semantics
               (σs : list Σ)
               (λs : list (list Λ)) : Prop :=
      forall ts, Trace ts
        -> σs = map input ts /\ λs = map output ts.

    Fixpoint δ_run (s : S M) (σs : list Σ) : S M :=
      match σs with
      | [] => s
      | σ :: σs' => δ_run (δ M s σ) σs'
      end.

    Fixpoint ω_run (s : S M) (σs : list Σ) : list Λ :=
      match σs with
      | [] => nil
      | σ :: σs' => ω_run (δ M s σ) σs' ++ ω M s σ
      end.
  End MachineSemantics.

  Definition prod (m1 m2 : Machine Σ Λ) : Machine Σ Λ :=
    mkMachine (S0 m1, S0 m2)
              (fun s σ => let (s1, s2) := s in (δ m1 s1 σ, δ m2 s2 σ))
              (fun s σ => let (s1, s2) := s in ω m1 s1 σ ++ ω m2 s2 σ).
End Machines.

Arguments δ_run : default implicits.
Arguments ω_run : default implicits.
Arguments prod : default implicits.

Definition wire {Σ Λ' Λ} (m1 : Machine Σ Λ') (m2 : Machine Λ' Λ) :
  Machine Σ Λ :=
  mkMachine (S0 m1, S0 m2)
            (fun s σ =>
               (let (s1, s2) := s in
                let s1' := δ m1 s1 σ in
                let λ1s := ω m1 s1 σ in
                let s2' := δ_run m2 s2 λ1s in
                (s1', s2')))
            (fun s σ =>
               (let (s1, s2) := s in
                (* let s1' := δ m1 s1 σ in *)
                let λ1s := ω m1 s1 σ in
                ω_run m2 s2 λ1s)).
