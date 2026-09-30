import H0mework.Versions.X.Fock.CopyGraph.RefinementPrefix
import H0mework.Versions.X.Fock.CopyGraph.DecoderComparison

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRefinement

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
open SourceGeneratedAcquisitionContinuation SourcePrimeHistoryRecovery
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance completeMeasurable (width : Nat) : MeasurableSpace (SourceFixedInventoryRecovery.Observation width) := ⊤

theorem complete_weighted_residual (runtime : LivingRuntimeState process)
    (value : Space (historyPMF (inventoryBound runtime))) :
    residual (historyPMF (inventoryBound runtime))
      (SourceFixedInventoryRecovery.query runtime (windowBound sourceOwner (inventoryBound runtime))) value = 0 := by
  let bound := inventoryBound runtime
  let query := SourceFixedInventoryRecovery.query runtime (windowBound sourceOwner bound)
  have faithful : Function.Injective query := observe_injective sourceOwner bound
  have task : taskValue (historyPMF bound) (fun actor => value actor) = value :=
    MeasureTheory.Lp.toLp_coeFn value (task_memLp (historyPMF bound) (fun actor => value actor))
  have attained := optimal_attains (historyPMF bound) query (fun actor => value actor)
  have reads (actor : Fin (bound + 1)) :
      optimalDecoder (historyPMF bound) query (fun point => value point) (query actor) = value actor :=
    ObservationRefinement.optimum_injective (historyPMF bound) query faithful (fun point => value point) actor (source_positive bound actor)
  simp only [task, error, reads, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero] at attained
  apply norm_eq_zero.mp
  change ‖residual (historyPMF bound) query value‖ = 0
  nlinarith only [attained, norm_nonneg (residual (historyPMF bound) query value)]

theorem complete_residual (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (value : Space (historyPMF (inventoryBound runtime))) :
    prefixResidual runtime index (windowBound sourceOwner (inventoryBound runtime))
      (SourceConditionalGraph.copyRead (inventoryBound runtime) (inventoryBound runtime) index value) = 0 := by
  apply (SourceConditionalGraphDecoder.recovery_zero_iff (inventoryBound runtime) (inventoryBound runtime) index
    (SourceFixedInventoryRecovery.query runtime (windowBound sourceOwner (inventoryBound runtime))) value).mpr
  exact complete_weighted_residual runtime value

theorem full_gain_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (value : Space (historyPMF (inventoryBound runtime))) :
    ‖prefixResidual runtime index 0
      (SourceConditionalGraph.copyRead (inventoryBound runtime) (inventoryBound runtime) index value)‖ ^ 2 =
        ∑ stage ∈ Finset.range (windowBound sourceOwner (inventoryBound runtime)),
          ‖prefixGain runtime index stage
            (SourceConditionalGraph.copyRead (inventoryBound runtime) (inventoryBound runtime) index value)‖ ^ 2 := by
  have generated := prefix_total runtime index (windowBound sourceOwner (inventoryBound runtime))
    (SourceConditionalGraph.copyRead (inventoryBound runtime) (inventoryBound runtime) index value)
  rw [complete_residual, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at generated
  exact generated

end
end SourceGraphRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
