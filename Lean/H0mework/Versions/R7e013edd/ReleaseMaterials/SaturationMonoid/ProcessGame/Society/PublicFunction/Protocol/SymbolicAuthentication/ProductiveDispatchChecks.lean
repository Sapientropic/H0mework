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
  let cache := CachedCommandRun.run model start emitted
  have rows : StageTrace.records start actual.stages = cache.rows :=
    (congrArg (fun state : State => StageTrace.records start state.stages)
      actual_is_the_original_execution_of_its_emitted_inputs).trans cache.rows_eq.symm
  have ledger : StageBudget.ledger vocabulary start actual.stages = CachedWorkDispatch.ledger vocabulary cache.rows :=
    (CachedWorkDispatch.ledger_eq vocabulary start actual.stages).symm.trans
      (congrArg (CachedWorkDispatch.ledger vocabulary) rows)
  have checked : cache.rows.flatMap (fun row => row.submitted) = work ∧
      (CachedWorkDispatch.ledger vocabulary cache.rows).map (fun ballot => (ballot.actor,ballot.cut,ballot.fee)) =
        [(true,42,1),(false,48,1),(false,52,2)] := by
    dsimp only [cache]
    decide +kernel
  exact ⟨(congrArg (fun history => history.flatMap (fun row => row.submitted)) rows).trans checked.1,
    (congrArg (fun ballots => ballots.map (fun ballot => (ballot.actor,ballot.cut,ballot.fee))) ledger).trans checked.2⟩

theorem the_same_actual_production_funds_both_identity_quorums :
    nextWork actual = none ∧
    (observed actual zero).receipts.length = 2 ∧ (observed actual one).receipts.length = 2 ∧
    ActorQuorum.support (observed actual zero) scope true = {false,true} ∧
    ActorQuorum.support (observed actual one) scope true = {false,true} ∧
    ActorStageEnvelope.budget start vocabulary actual.stages scope = 0 ∧
    decideAt actual zero = .decided true ∧ decideAt actual one = .decided true := by
  let cache := CachedCommandRun.run model start emitted
  have rows : StageTrace.records start actual.stages = cache.rows :=
    (congrArg (fun state : State => StageTrace.records start state.stages)
      actual_is_the_original_execution_of_its_emitted_inputs).trans cache.rows_eq.symm
  let pending (history : List (StageTrace.Record (code := model.source.code))) :=
    work.find? fun request => !(history.any fun row =>
      (StageTrace.items row).any fun item =>
        decide (item.request = request ∧ model.source.code.law.Valid item.before item.request))
  have originalWork : nextWork actual = pending (StageTrace.records start actual.stages) := rfl
  have cachedWork : pending cache.rows = CachedWorkDispatch.nextWork work cache := rfl
  have workDone := originalWork.trans ((congrArg pending rows).trans cachedWork)
  have reception (receiver : Fin model.source.code.sites) :
      observed actual receiver = CachedWorkDispatch.observed vocabulary law cache receiver := by
    change HeaderDispatch.observed model start vocabulary law actual receiver = _
    rw (config := {transparency := .default}) [actual_is_the_original_execution_of_its_emitted_inputs]
    exact (CachedWorkDispatch.observed_eq vocabulary law cache receiver).symm
  have affected : ActorStageEnvelope.affected start vocabulary actual.stages scope =
      CachedWorkDispatch.affected vocabulary start cache.rows scope :=
    (CachedWorkDispatch.affected_eq vocabulary start actual.stages scope).symm.trans
      (congrArg (fun rows => CachedWorkDispatch.affected vocabulary start rows scope) rows)
  have decision (receiver : Fin model.source.code.sites) :
      decideAt actual receiver = CachedWorkDispatch.produce vocabulary start law cache.rows receiver scope 2 :=
    (CachedWorkDispatch.produce_eq vocabulary start law actual.stages receiver scope 2).symm.trans
      (congrArg (fun rows => CachedWorkDispatch.produce vocabulary start law rows receiver scope 2) rows)
  let seen := CachedWorkDispatch.observed vocabulary law cache
  let result := CachedWorkDispatch.produce vocabulary start law cache.rows
  have checked : CachedWorkDispatch.nextWork work cache = none ∧
      (seen zero).receipts.length = 2 ∧ (seen one).receipts.length = 2 ∧
      ActorQuorum.support (seen zero) scope true = {false,true} ∧
      ActorQuorum.support (seen one) scope true = {false,true} ∧
      (CachedWorkDispatch.affected vocabulary start cache.rows scope).card = 0 ∧
      result zero scope 2 = .decided true ∧ result one scope 2 = .decided true := by
    dsimp only [seen, result, cache]
    decide +kernel
  rcases checked with ⟨done, zeroCount, oneCount, zeroSupport, oneSupport, budget, zeroResult, oneResult⟩
  exact ⟨workDone.trans done,
    (congrArg (fun receiver => receiver.receipts.length) (reception zero)).trans zeroCount,
    (congrArg (fun receiver => receiver.receipts.length) (reception one)).trans oneCount,
    (congrArg (fun receiver => ActorQuorum.support receiver scope true) (reception zero)).trans zeroSupport,
    (congrArg (fun receiver => ActorQuorum.support receiver scope true) (reception one)).trans oneSupport,
    (congrArg (fun actors : Finset Bool => actors.card) affected).trans budget, (decision zero).trans zeroResult, (decision one).trans oneResult⟩

theorem actual_joint_progress_generates_new_material_and_keeps_the_original_debt_and_revocation :
    (EventStep.seed (actual.current model start)).current.stock false true = 6 ∧
    (EventStep.seed (actual.current model start)).current.stock true true = 2 ∧
    (EventStep.seed (actual.current model start)).current.claims () false true = 7 ∧
    (EventStep.seed (actual.current model start)).current.technology.holder = none ∧
    (actual.current model start).cut = 62 ∧
    (EventStep.seed (actual.current model start)).remaining = 2 := by
  let cache := CachedCommandRun.run model start emitted
  have current : actual.current model start = cache.cursor :=
    (congrArg (fun state : State => state.current model start)
      actual_is_the_original_execution_of_its_emitted_inputs).trans cache.cursor_eq.symm
  have seed : EventStep.seed (actual.current model start) = cache.before := by
    rw (config := {transparency := .default}) [current]
    exact cache.before_eq.symm
  have checked : cache.before.current.stock false true = 6 ∧
      cache.before.current.stock true true = 2 ∧ cache.before.current.claims () false true = 7 ∧
      cache.before.current.technology.holder = none ∧ cache.cursor.cut = 62 ∧ cache.before.remaining = 2 := by
    dsimp only [cache]
    decide +kernel
  rcases checked with ⟨falseStock, trueStock, claims, holder, cut, fuel⟩
  exact ⟨(congrArg (fun s => s.current.stock false true) seed).trans falseStock,
    (congrArg (fun s => s.current.stock true true) seed).trans trueStock,
    (congrArg (fun s => s.current.claims () false true) seed).trans claims,
    (congrArg (fun s => s.current.technology.holder) seed).trans holder,
    (congrArg (fun cursor => cursor.cut) current).trans cut,
    (congrArg (fun s => s.remaining) seed).trans fuel⟩

theorem the_entire_joint_execution_is_source_admitted : admitted initial 21 = .running actual :=
  original_fuel_generates_the_entire_admitted_productive_dispatch initial 21
    (by rw [the_original_native_service_endpoint_funds_twenty_three_invocations]; omega)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveDispatchChecks
