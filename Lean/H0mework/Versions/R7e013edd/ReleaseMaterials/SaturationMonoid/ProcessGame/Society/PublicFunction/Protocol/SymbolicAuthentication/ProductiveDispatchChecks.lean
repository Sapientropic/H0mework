import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveDispatchTrace

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveDispatchChecks
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open ProductiveDispatchSource ProductiveDispatchTrace

theorem current_state_generates_the_productive_and_communication_trace :
    (journey initial 21).2 = emitted := by
  have generated := congrArg (fun state : State => state.inputs)
    (the_generated_transcript_executes_the_same_actual_state initial 21)
  have copied := LocalCommandRun.fold_keeps_all_inputs model start (journey initial 21).2 initial
  have kept : actual.inputs = (journey initial 21).2 :=
    generated.trans (copied.trans (List.nil_append _))
  exact kept.symm.trans ((congrArg (fun state : State => state.inputs)
    actual_is_the_original_execution_of_its_emitted_inputs).trans
      (LocalCommandRun.the_source_keeps_every_input_in_order model start emitted))

theorem generated_transcript_length (state : State) (count : Nat) : (journey state count).2.length = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change ((journey state count).2 ++ [_]).length = count+1
    rw [List.length_append,List.length_singleton,ih]

theorem generated_transcript_prefix (state : State) (before after : Nat) :
    (journey state before).2 = (journey state (before+after)).2.take before := by
  induction after with
  | zero =>
    change (journey state before).2 = (journey state before).2.take before
    simpa only [generated_transcript_length] using (List.take_length (l := (journey state before).2)).symm
  | succ after ih =>
    change (journey state before).2 = ((journey state (before+after)).2 ++ [_]).take before
    rw [List.take_append_of_le_length (by rw [generated_transcript_length]; omega)]
    exact ih

theorem every_bounded_generated_prefix_is_the_original_emitted_source (count : Nat) (bounded : count ≤ 21) :
    (journey initial count).1 = LocalCommandRun.run model start (emitted.take count) := by
  have savedPrefix := generated_transcript_prefix initial count (21-count)
  rw [Nat.add_sub_of_le bounded,current_state_generates_the_productive_and_communication_trace] at savedPrefix
  rw [the_generated_transcript_executes_the_same_actual_state,savedPrefix]
  rfl

theorem actual_production_and_wages_generate_the_original_paid_ballots :
    (StageTrace.records start actual.stages).flatMap (fun row => row.submitted) = work ∧
    (StageBudget.ledger vocabulary start actual.stages).map (fun ballot => (ballot.actor,ballot.cut,ballot.fee)) =
      [(true,42,1),(false,48,1),(false,52,2)] := by
  rw [actual_is_the_original_execution_of_its_emitted_inputs]
  decide +kernel

theorem the_same_actual_production_funds_both_identity_quorums :
    nextWork actual = none ∧
    (observed actual zero).receipts.length = 2 ∧ (observed actual one).receipts.length = 2 ∧
    ActorQuorum.support (observed actual zero) scope true = {false,true} ∧
    ActorQuorum.support (observed actual one) scope true = {false,true} ∧
    ActorStageEnvelope.budget start vocabulary actual.stages scope = 0 ∧
    decideAt actual zero = .decided true ∧ decideAt actual one = .decided true := by
  rw [actual_is_the_original_execution_of_its_emitted_inputs]
  decide +kernel

theorem actual_joint_progress_generates_new_material_and_keeps_the_original_debt_and_revocation :
    (EventStep.seed (actual.current model start)).current.stock false true = 6 ∧
    (EventStep.seed (actual.current model start)).current.stock true true = 2 ∧
    (EventStep.seed (actual.current model start)).current.claims () false true = 7 ∧
    (EventStep.seed (actual.current model start)).current.technology.holder = none ∧
    (actual.current model start).cut = 62 ∧
    (EventStep.seed (actual.current model start)).remaining = 2 := by
  rw [actual_is_the_original_execution_of_its_emitted_inputs]
  decide +kernel

theorem the_entire_joint_execution_is_source_admitted : admitted initial 21 = .running actual :=
  original_fuel_generates_the_entire_admitted_productive_dispatch initial 21
    (by rw [the_original_native_service_endpoint_funds_twenty_three_invocations]; omega)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveDispatchChecks
