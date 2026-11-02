import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowTrace
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowService

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 60000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowCompletion
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open ReceiptDrivenSource ReceiptWindowSource

theorem every_timing_closes_all_native_responsibilities :
    ∀ timing : Timing, LocalJointResponse.Clear (model .normal) initial vocabulary (encoding .normal) (law .normal)
      (stages timing) := by
  rintro ⟨a, b⟩
  cases a <;> cases b <;> decide +kernel

theorem every_timing_has_no_unserved_final_local_intent (timing : Timing) :
    BatchReentry.idle (model .normal) initial vocabulary (encoding .normal) (law .normal) (stages timing) := by
  intro site
  apply ReceiptDrivenService.an_empty_local_word_has_no_authenticated_intent
  rcases timing with ⟨a, b⟩
  cases a <;> cases b <;> revert site <;> decide +kernel

theorem every_generated_timing_closes_the_complete_original_goal (timing : Timing) :
    InterferenceValidity.Goal (model .normal) initial vocabulary (encoding .normal) (law .normal)
      (LocalWindowRun.audit (model .normal) (stages timing) []) := by
  have paid := ReceiptWindowService.every_original_snapshot_has_its_own_valid_complete_service timing
  refine ⟨⟨⟨every_timing_closes_all_native_responsibilities timing,
    every_timing_has_no_unserved_final_local_intent timing⟩, ?_⟩, paid⟩
  intro entry registered site needed
  obtain ⟨index, bounded, later, row, actualRow, owner, submitted, _, stage, actualStage, aligned⟩ :=
    paid entry registered site needed
  exact ⟨index, bounded, later, row, actualRow, owner, submitted, stage, actualStage, aligned⟩

theorem every_generated_timing_has_complete_communication_and_no_pending_notification :
    ∀ timing : Timing,
      ReceiptDrivenRun.empty (model .normal)
        (FreshReception.queue (ReceiptDrivenMaterialization.finalPending (model .normal) (fun _ => []) (path timing))
          (FreshReception.poll vocabulary (encoding .normal) (law .normal) initial (stages timing))) = true ∧
      ReceiptDrivenRun.sendsClosed (model .normal) initial vocabulary (encoding .normal) (law .normal) (stages timing) = true := by
  rintro ⟨a, b⟩
  cases a <;> cases b <;> decide +kernel

theorem every_generated_timing_completes (timing : Timing) :
    (ReceiptWindowTrace.terminal timing).status = .jointComplete := by
  obtain ⟨empty, received⟩ := every_generated_timing_has_complete_communication_and_no_pending_notification timing
  have ready : LocalWindowRun.Ready (model .normal) initial vocabulary (encoding .normal) (law .normal)
      (LocalWindowRun.audit (model .normal) (stages timing) []) :=
    ⟨rfl, every_generated_timing_closes_the_complete_original_goal timing⟩
  change (ReceiptDrivenRun.finish (model .normal) initial vocabulary (encoding .normal) (law .normal) (stages timing) _ []).status = .jointComplete
  simp only [ReceiptDrivenRun.finish, if_pos (And.intro empty (And.intro received ready))]

theorem every_original_compliant_adaptive_callback_completes_before_the_source_deadline
    (rival : Opponent (code .normal))
    (compliant : ((actual rival).inputs.all fun input => input.within) = true) :
    (actual rival).status = .jointComplete ∧ (actual rival).state.past.length = horizon ∧
      InterferenceValidity.Goal (model .normal) initial vocabulary (encoding .normal) (law .normal) (actual rival).state := by
  obtain ⟨timing, sameState, sameStatus, _⟩ :=
    ReceiptWindowTrace.every_compliant_adaptive_execution_is_one_of_the_original_generated_histories rival compliant
  have complete := sameStatus.trans (every_generated_timing_completes timing)
  refine ⟨complete, ?_, ?_⟩
  · rw [sameState]
    change (stages timing).length = horizon
    simp only [stages, List.length_map, List.length_range]
  · exact (ReceiptDrivenRun.success_keeps_the_entire_original_goal (model .normal) initial vocabulary (encoding .normal)
      (law .normal) allowance _ [] (fun _ => []) rival complete).2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowCompletion
