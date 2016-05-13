Record Transition {s : Type} {e : Type} := mkTransition
  { source : s;
    event : e;
    output : list e;
    destination : s;
  }.

Arguments mkTransition {_} {_} _ _ _ _.

(* Semantics *)
Record FSM := mkFSM
  { fsmState : Type;
    fsmEvent : Type;
    fsmTransitions :> @Transition fsmState fsmEvent -> Type;
  }.

Definition full_trace (fsm : FSM) :=
  list (@Transition (fsmState fsm) (fsmEvent fsm)).

Inductive FullTrace : forall (fsm : FSM), full_trace fsm -> Type :=
| FullTrace_Empty fsm : FullTrace fsm nil
| FullTrace_Step fsm : forall s s' s'' e e' es es' ts,
    FullTrace fsm (mkTransition s e es s'::ts)
    -> fsm (mkTransition s e es s')
    -> FullTrace fsm (mkTransition s' e' es' s''::
                                    mkTransition s e es s'::
                                    ts).

Fixpoint extract (fsm : FSM) (tr : full_trace fsm) : list (fsmEvent fsm) :=
  match tr with
  | nil => nil
  | t::tr' => app (output t) (extract fsm tr')
  end.

Definition Produces (fsm : FSM) (es : list (fsmEvent fsm)) : Type :=
  exists tr, extract fsm tr = es.