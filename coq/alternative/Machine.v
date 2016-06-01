Require Import Coq.Lists.List.

Record Machine :=
  mkMachine
    { S : Type;
      Σ : Type;
      Λ : Type;
      S0 : S;
      δ : S -> Σ -> S;
      ω : S -> Σ -> list Λ
    }.

Section MachineSemantics.
  Variable M : Machine.

  Record Configuration : Type :=
    mkConfiguration {
        source : S M;
        input : Σ M;
        destination : S M;
        output : list (Λ M);
      }.

  Inductive Trace : list Configuration -> Prop :=
  | Trace_start : forall σ,
      Trace (mkConfiguration (S0 M) σ (δ M (S0 M) σ) (ω M (S0 M) σ)
               ::nil)
  | Trace_next : forall ts src σ s' σ' λs',
      Trace (mkConfiguration s' σ' src λs'
               ::ts) ->
      Trace (mkConfiguration src σ (δ M src σ) (ω M src σ)
               ::mkConfiguration s' σ' src λs'
               ::ts).

  Definition Semantics
             (σs : list (Σ M))
             (λs : list (list (Λ M))) : Prop :=
    forall ts, Trace ts ->
               σs = List.map input ts /\
               λs = List.map output ts.
End MachineSemantics.