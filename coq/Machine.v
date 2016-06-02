(** Basic state machine and trace definitions. Needs to be extended with
run-to-completion semantics, operations for synchronous products of machines,
and a mechanism for asynchronous machine communication via channels. *)
Require Import Coq.Lists.List.

Section Machines.
  Variable Σ : Type.
  Variable Λ : Type.

  Record Machine (Σ Λ : Type) :=
    mkMachine
      { S : Type;
        S0 : S;
        δ : S -> Σ -> S;
        ω : S -> Σ -> list Λ
      }.

  Global Arguments mkMachine {_ _} _ _ _ _.
  Global Arguments S {_ _} _.
  Global Arguments S0 {_ _} _.
  Global Arguments δ {_ _} _ _ _.
  Global Arguments ω {_ _} _ _ _.

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
                      ::nil)
    | Trace_next : forall ts src σ s' σ' λs',
        Trace (mkStep s' σ' src λs'
                      ::ts) ->
        Trace (mkStep src σ (δ M src σ) (ω M src σ)
                      ::mkStep s' σ' src λs'
                      ::ts).

    Definition Semantics
               (σs : list Σ)
               (λs : list (list Λ)) : Prop :=
      forall ts, Trace ts ->
                 σs = List.map input ts /\
                 λs = List.map output ts.
  End MachineSemantics.

  Definition prod (m1 m2 : Machine Σ Λ) : Machine Σ Λ :=
    mkMachine (S m1 * S m2)
              (S0 m1, S0 m2)
              (fun s σ =>
                 let (s1, s2) := s in
                 (δ m1 s1 σ, δ m2 s2 σ))
              (fun s σ =>
                 let (s1, s2) := s in
                 List.app (ω m1 s1 σ)
                          (ω m2 s2 σ)).
End Machines. 