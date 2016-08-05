Require Import Coq.Program.Program.
Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.

Section Scenarios.
  (* Data state. Information that is global to a machine--and so visible outside
  of a scenario. *)
  Variable DState : Type.
  (* Input events *)
  Variable IEvent : Type.
  (* Output events *)
  Variable OEvent : Type.
  (* Internal events *)
  Variable MEvent : Type.

  Record Scenario :=
    mkScenario
      { (* Machine state. I.e. Q in a normal state machine. *)
        MState : Type;
        start_state : MState;
        error_state : MState;
        transition :
          MState -> DState -> (IEvent + OEvent + MEvent) -> MState;
        dstate_update :
          MState -> DState -> (IEvent + OEvent + MEvent) -> DState;
        output :
          MState -> DState -> (IEvent + OEvent + MEvent) ->
          list (IEvent + OEvent + MEvent);

        (* Error state properties *)
        error_state_distinct : error_state <> start_state;
        error_event : OEvent;   (* TODO name location of error *)
        error_state_stuck : forall ds ie,
          transition error_state ds ie = error_state;
        error_state_silent : forall ds ie,
          output error_state ds ie = nil;
        error_state_idempotent : forall ds ie,
          dstate_update error_state ds ie = ds;
        error_state_entry : forall ms ds ie,
            transition ms ds ie = error_state ->
            output ms ds ie = error_event::nil;
      }.

  Record ScenarioConfig (S : Scenario) :=
    mkScenarioConfig
      { sc_mstate : MState S;
        sc_dstate : DState;
        sc_ievents : list IEvent;
      }.

  Arguments sc_mstate {_} _.
  Arguments sc_dstate {_} _.
  Arguments sc_ievents {_} _.

  Inductive MicroStep (S : Scenario) (sc1 sc2 : ScenarioConfig S) : Prop :=
  | MicroStep_basic : forall ie ms2,
      transition S (sc_mstate sc1) (sc_dstate sc1) ie = sc_mstate sc2 ->
      dstate_update S (sc_mstate sc1) (sc_dstate sc1) ie = sc_dstate sc2 ->
      List.In ie (sc_ievents sc1) ->
      (sc_ievents sc2) = (sc_ievents sc1) \\ ie ∪ (output S ...) ->
      output S (sc_mstate sc1) (sc_dstate sc1) ie = ms2 ->
      (sc_mstate sc2) <> error_state S ->
      MicroStep S sc1 sc2.

  .
End Scenarios.

Section Machines.
  Variable State : Type.
  Variable DataState : Type.
  Variable InputEvent : Type.
  Variable OutputEvent : Type.
  Variable InternalEvent : Type.

  Record Machine :=
    mkMachine
      { initial : State;
        transition :
          State -> DataState -> InputEvent -> State * DataState;
        output :
          State -> DataState -> InputEvent -> list (OutputEvent + InternalEvent);
        error_state : State;
        no_update_on_err : forall s d σ d',
            transition s d σ = (error_state, d') -> d = d';
        no_output_on_err : forall s d σ,
            transition s d σ = (error_state, d) -> output s d σ = nil;
      }.

  Record Configuration :=
    mkConfiguration
      { S