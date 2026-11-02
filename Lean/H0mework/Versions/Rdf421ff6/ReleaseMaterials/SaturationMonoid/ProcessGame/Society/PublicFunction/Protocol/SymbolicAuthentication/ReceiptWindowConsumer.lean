import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowCompletion
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenConsumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenBudget

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 60000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowConsumer
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open ReceiptDrivenSource ReceiptWindowSource

abbrev census (rival : Opponent (code .normal)) := ReceiptDrivenRuntime.rooted (model .normal) initial
  ReceiptWindowSource.programme vocabulary (encoding .normal) (law .normal) allowance rival slot 0

theorem the_original_root_consumes_the_uniform_conditional_completion
    (rival : Opponent (code .normal))
    (compliant : (((census rival).answer.inputs).all fun input => input.within) = true) :
    (census rival).answer.status = .jointComplete ∧ (census rival).answer.state.past.length = horizon ∧
      InterferenceValidity.Goal (model .normal) initial vocabulary (encoding .normal) (law .normal) (census rival).answer.state := by
  have same : (census rival).answer = actual rival := (census rival).answer_exact
  rw [same] at compliant ⊢
  exact ReceiptWindowCompletion.every_original_compliant_adaptive_callback_completes_before_the_source_deadline rival compliant

theorem a_real_source_callback_satisfies_the_original_communication_condition :
    (((census (EagerDelivery.callback initial)).answer.inputs).all fun input => input.within) = true := by
  rw [ReceiptDrivenRuntime.Census.answer_exact]
  exact ReceiptDrivenBudget.the_actual_executor_has_a_compliant_callback
    (model .normal) initial vocabulary (encoding .normal) (law .normal) allowance _ _ _

theorem the_actual_uniformly_guaranteed_history_is_consumed_literally_by_the_original_root
    (rival : Opponent (code .normal))
    (compliant : (((census rival).answer.inputs).all fun input => input.within) = true) :
    ReceiptDrivenRuntime.full (model .normal) initial ReceiptWindowSource.programme vocabulary (encoding .normal) (law .normal)
      allowance rival =
    ReceiptDrivenRuntime.actual (model .normal) initial ReceiptWindowSource.programme vocabulary (encoding .normal) (law .normal)
      allowance rival :=
  ReceiptDrivenConsumer.completed_history_is_consumed_by_the_root_without_further_stages
    (model .normal) initial ReceiptWindowSource.programme vocabulary (encoding .normal) (law .normal) allowance rival slot 0
    (the_original_root_consumes_the_uniform_conditional_completion rival compliant).1

theorem the_same_emitter_root_consumes_all_history_whole_ledger_and_literal_next
    (rival : Opponent (code .normal)) :
    let state := ReceiptDrivenRuntime.runtime (model .normal) initial ReceiptWindowSource.programme vocabulary
      (encoding .normal) (law .normal) allowance rival slot 0
    ReceiptDrivenRuntime.actual (model .normal) initial ReceiptWindowSource.programme vocabulary (encoding .normal) (law .normal)
      allowance rival <+:
      ReceiptDrivenRuntime.full (model .normal) initial ReceiptWindowSource.programme vocabulary (encoding .normal) (law .normal)
        allowance rival ∧
    HEq ((ReceiptDrivenRuntime.facade (model .normal) initial ReceiptWindowSource.programme vocabulary
      (encoding .normal) (law .normal) allowance rival slot 0).readoutAt state .recovery)
      (state.tick.generated.projectionOutcome (.component ())) ∧
    HEq state.tick.generated.wholeLedgerWriteBack
      (state.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt state.current.visit.current) ∧
    state.tick.nextCurrent =
      (ReceiptDrivenRuntime.facade (model .normal) initial ReceiptWindowSource.programme vocabulary
        (encoding .normal) (law .normal) allowance rival slot 0).process.stateAt
        ((ReceiptDrivenRuntime.facade (model .normal) initial ReceiptWindowSource.programme vocabulary
          (encoding .normal) (law .normal) allowance rival slot 0).process.successor state.state) :=
  ReceiptDrivenConsumer.the_same_root_consumes_history_entire_ledger_and_literal_next
    (model .normal) initial ReceiptWindowSource.programme vocabulary (encoding .normal) (law .normal) allowance rival slot 0

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowConsumer
