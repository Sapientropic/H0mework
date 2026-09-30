import H0mework.Fock.HistoryConditional.ModelLoss
import H0mework.Fock.HistoryConditional.ModelRestore

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalModel

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceObservationInvariantControls (parity)
open SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton

local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem variance_original_account (runtime : LivingRuntimeState process) (depth : Nat) (decode : NextModel runtime → ℂ) :
    let value := taskValue (historyPMF (inventoryBound runtime)) (decode ∘ nextRead runtime)
    let retained := SourceGeneratedEmpiricalHilbert.retainedHistory parity runtimeSeed (inventoryBound runtime) (depth + 1)
      (SourceWeightedRecovery.Runtime.Actor.actorTransfer parity runtimeSeed (inventoryBound runtime) value)
    (∑ index, (historyPMF (inventoryBound runtime) index).toReal *
      SourceConditionalNext.variance (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth)
        (SourceConditionalNext.Image.actual (nextRead runtime)) (fun item => decode item.val) (dynamicRead runtime depth index)
        (observed_supported _ _ index (positive runtime index))) =
      ‖SourceWeightedRecovery.Runtime.Actor.actorResidual parity runtimeSeed (inventoryBound runtime) value‖ ^ 2 +
        SourceGeneratedEmpiricalHilbert.inventoryEnergy parity runtimeSeed (inventoryBound runtime) (depth + 1) retained.2 := by
  let task := decode ∘ nextRead runtime
  let value := taskValue (historyPMF (inventoryBound runtime)) task
  let retained := SourceGeneratedEmpiricalHilbert.retainedHistory parity runtimeSeed (inventoryBound runtime) (depth + 1)
    (SourceWeightedRecovery.Runtime.Actor.actorTransfer parity runtimeSeed (inventoryBound runtime) value)
  have attained := SourceWeightedRecovery.Runtime.Actor.History.complete_error_attains parity runtimeSeed (inventoryBound runtime) depth task
  have upper := optimal_lower_bound (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth) task (fun atom => retained.1 atom)
  change error (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth) task (fun atom => retained.1 atom) =
    ‖SourceWeightedRecovery.Runtime.Actor.actorResidual parity runtimeSeed (inventoryBound runtime) value‖ ^ 2 +
      SourceGeneratedEmpiricalHilbert.inventoryEnergy parity runtimeSeed (inventoryBound runtime) (depth + 1) retained.2 at attained
  rw [attained, optimal_attains] at upper
  have lower := SourceWeightedRecovery.Runtime.Actor.History.complete_error_lower_bound parity runtimeSeed (inventoryBound runtime) depth task
    (optimalDecoder (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth) task)
  change ‖SourceWeightedRecovery.Runtime.Actor.actorResidual parity runtimeSeed (inventoryBound runtime) value‖ ^ 2 +
    SourceGeneratedEmpiricalHilbert.inventoryEnergy parity runtimeSeed (inventoryBound runtime) (depth + 1) retained.2 ≤
      error (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth) task
        (optimalDecoder (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth) task) at lower
  rw [optimal_attains] at lower
  have same := le_antisymm upper lower
  have variance := SourceConditionalNext.Image.residual_variance_original (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth)
    (nextRead runtime) decode (positive runtime)
  exact variance.symm.trans same

end
end SourceConditionalModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
