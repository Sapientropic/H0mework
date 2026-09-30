import H0mework.Fock.CopyGraph.CostPrice

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCost

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceConditionalCorrection
open SourceGeneratedAcquisitionMeasure SourceGeneratedJointClockGraph SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyProgram (Index)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem explicit_error (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    ‖SourceConditionalGraph.copyRead depth bound index value -
      SourceConditionalGraphDecoder.action depth bound index query (recovery depth bound index query value)‖ ^ 2 =
        ‖residual (historyPMF bound) query value‖ ^ 2 + strength depth bound index * ‖clockPair bound query value‖ ^ 2 /
          denominator depth bound index query := by
  rw [recovery_source, SourceConditionalGraphDecoder.minimum_cost]
  exact minimum_cost depth bound index query value

theorem original_minimum_cost (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : FieldSpace depth bound) :
    let task := Actor.currentPullback depth bound value
    ‖SourceCopyGraph.action depth index (fieldRead depth bound value) -
      SourceCopyGraph.action depth index (fieldRead depth bound (fieldRecovery depth bound index query value))‖ ^ 2 =
        ‖Actor.currentTransfer depth bound (residual (historyPMF bound) query task)‖ ^ 2 +
          strength depth bound index * ‖clockPair bound query task‖ ^ 2 / denominator depth bound index query := by
  dsimp only
  rw [field_recovery_original]
  change ‖SourceCopyGraph.action depth index (fieldRead depth bound value) -
    SourceCopyGraph.action depth index (fieldRead depth bound (SourceConditionalGraphDecoder.realizeObserved depth bound query
      (SourceConditionalGraphDecoder.decode depth bound index query (SourceCopyGraph.action depth index (fieldRead depth bound value)))))‖ ^ 2 = _
  rw [SourceConditionalGraphDecoder.realized_action, SourceConditionalGraphDecoder.minimum_cost, actor_transfer_norm]
  exact minimum_cost depth bound index query (Actor.currentPullback depth bound value)

theorem original_residual_budget (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : FieldSpace depth bound) :
    let remaining := value - fieldRecovery depth bound index query value
    ‖SourceCopyGraph.action depth index (fieldRead depth bound remaining)‖ ^ 2 =
      ‖Actor.currentTransfer depth bound (residual (historyPMF bound) query (Actor.currentPullback depth bound value))‖ ^ 2 +
        strength depth bound index * ‖clockPair bound query (Actor.currentPullback depth bound value)‖ ^ 2 /
          denominator depth bound index query := by
  dsimp only
  rw [map_sub, map_sub]
  exact original_minimum_cost depth bound index query value

end
end SourceConditionalCost
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
