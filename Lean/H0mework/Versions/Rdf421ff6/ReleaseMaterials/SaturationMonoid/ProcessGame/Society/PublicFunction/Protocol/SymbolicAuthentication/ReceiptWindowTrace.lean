import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowSource

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 60000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowTrace
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open ReceiptDrivenSource ReceiptWindowSource

theorem all_original_admitted_moves_are_covered_at_every_actual_cut :
    ReceiptBranchCoverage.covers (model .normal) initial vocabulary (encoding .normal) (law .normal) allowance
      (ReceiptDrivenRun.template (model .normal) initial ReceiptWindowSource.programme) [] (fun _ => []) paths = true := by decide +kernel

theorem every_timing_is_source_generated (timing : Timing) : timing ∈ timings := by
  rcases timing with ⟨a, b⟩
  cases a <;> cases b <;> decide +kernel

theorem each_path_has_its_literal_complete_actual_history (timing : Timing) :
    ReceiptDrivenMaterialization.extend (model .normal) [] (path timing) = stages timing := by
  simp only [ReceiptDrivenMaterialization.extend, path, stages, List.nil_append, List.map_map, Function.comp_def]

def terminal (timing : Timing) := ReceiptDrivenRun.run (model .normal) initial vocabulary (encoding .normal) (law .normal) allowance
  [] (stages timing) (ReceiptDrivenMaterialization.finalPending (model .normal) (fun _ => []) (path timing)) (EventStep.fixed none)

theorem every_compliant_adaptive_execution_is_one_of_the_original_generated_histories
    (rival : Opponent (code .normal))
    (compliant : ((actual rival).inputs.all fun input => input.within) = true) :
    ∃ timing : Timing, (actual rival).state = (terminal timing).state ∧
      (actual rival).status = (terminal timing).status ∧ (actual rival).pending = (terminal timing).pending := by
  obtain ⟨selected, member, checked⟩ := ReceiptBranchCoverage.covered_paths_contain_every_compliant_actual_execution
    (model .normal) initial vocabulary (encoding .normal) (law .normal) allowance _ [] (fun _ => []) paths rival
    all_original_admitted_moves_are_covered_at_every_actual_cut compliant
  obtain ⟨timing, _, same⟩ := List.mem_map.mp member
  subst selected
  have exactRun := ReceiptDrivenMaterialization.verified_slots_are_the_original_dynamic_executor
    (model .normal) initial vocabulary (encoding .normal) (law .normal) allowance rival _ [] (fun _ => []) (path timing) checked
  rw [each_path_has_its_literal_complete_actual_history] at exactRun
  exact ⟨timing, exactRun⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowTrace
