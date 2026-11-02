import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StrategyRun

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EagerDelivery

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

-- This is the original fresh-packet predicate, evaluated on the callback's
-- actual event memory and frame. It neither mints a packet nor asserts payment.
def candidates (baseline : Nat) (past : Events code) (frame : code.Frame) : List (Choice code) :=
  code.eventAlphabet.attach.filter fun event => match event.val with
    | .deliver serial => decide (serial < frame.sent.length ∧ serial ∉ QueueScheduler.attempted code baseline past)
    | _ => false

def callback (start : Cursor code) : Opponent code := fun _ past frame =>
  (candidates (OriginQueue.baseline start) past frame).head?

theorem reply_is_the_first_actual_fresh_packet (start current : Cursor code) :
    EventStep.selected current (callback start) = (InterferenceEnvelope.fresh start current).head? := rfl

private theorem fresh_event_is_external (start current : Cursor code) (event : Choice code)
    (member : event ∈ InterferenceEnvelope.fresh start current) :
    Distributed.Recall.Information.Agency.externalChoice code (some event) = some event := by
  obtain ⟨serial, kind, _⟩ := CompletionEnvelope.every_generated_delivery_has_a_real_fresh_admitted_packet start current event member
  rcases event with ⟨event, supported⟩
  dsimp only at kind
  subst event
  rfl

theorem every_actual_reply_is_within_the_source_communication_domain
    (start : Cursor code) (past : List (EventHistory.Stage (code := code))) (allowance : Nat) :
    (InterferenceEnvelope.observe start past allowance (callback start)).within = true := by
  change decide (CompletionEnvelope.intake (EventHistory.execute start past) (callback start) ∈
    InterferenceEnvelope.choices start past allowance) = true
  apply decide_eq_true
  unfold CompletionEnvelope.intake CompletionEnvelope.raw
  by_cases owned : (Distributed.Recall.Information.Agency.ownerAt code
      (EventHistory.execute start past).ownerStart (EventStep.seed (EventHistory.execute start past)).history.length).isSome = true
  · simp [InterferenceEnvelope.choices, owned, Distributed.Recall.Information.Agency.externalChoice]
  · rw [if_neg owned, reply_is_the_first_actual_fresh_packet]
    cases pending : InterferenceEnvelope.fresh start (EventHistory.execute start past) with
    | nil => simp [InterferenceEnvelope.choices, owned, pending, Distributed.Recall.Information.Agency.externalChoice]
    | cons head tail =>
      have member : head ∈ InterferenceEnvelope.fresh start (EventHistory.execute start past) := by rw [pending]; exact List.mem_cons_self
      simp only [List.head?_cons, fresh_event_is_external start _ head member]
      simp only [InterferenceEnvelope.choices, owned, Bool.false_eq_true, if_false, pending]
      split_ifs <;> simp

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (allowance : Nat)

theorem the_actual_executor_always_has_a_compliant_callback
    (rounds : Nat) (state : StrategyPlan.State model) :
    ((StrategyRun.execute model start vocabulary encoding law allowance rounds state (callback start)).inputs.all
      fun input => input.within) = true := by
  induction rounds generalizing state with
  | zero => rfl
  | succ rounds ih =>
    by_cases complete : StrategyRun.Ready model start vocabulary encoding law state
    · simp only [StrategyRun.execute, if_pos complete, List.all_nil]
    · by_cases empty : CompletionState.fuel model start state = 0
      · simp only [StrategyRun.execute, if_neg complete, if_pos empty, List.all_nil]
      · simp only [StrategyRun.execute, if_neg complete, if_neg empty]
        cases chosen : StrategyRun.continuation model start vocabulary encoding law allowance rounds state with
        | none => rfl
        | some plan =>
          simp only [every_actual_reply_is_within_the_source_communication_domain, if_true, List.all_cons, Bool.true_and]
          exact ih _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EagerDelivery
