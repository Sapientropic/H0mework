import H0mework.Fock.HistoryConditional.GCostCapacity

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGInformationCost

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceConditionalInventory (values)
open SourceConditionalModel (dynamicRead)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem variance_original (runtime : LivingRuntimeState process) (depth : Nat) :
    totalVariance (inventoryBound runtime) (dynamicRead runtime depth) = SourceConditionalVector.dynamicVariance runtime depth := by
  simp only [totalVariance, SourceConditionalVector.dynamicVariance, SourceVectorMoment.variance, SourceVectorMoment.error,
    SourceConditionalVector.remaining, SourceConditionalVector.mean_source, Function.comp_def, SourceConditionalVector.actor_material, values]
  rfl

theorem current_full_variance (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalVector.dynamicVariance runtime depth =
      SourceConditionalInventory.cost (inventoryBound runtime) (dynamicRead runtime depth) / (inventoryBound runtime + 1 : ℝ) +
      ‖SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth)
        (SourceWeightedRecovery.taskValue (historyPMF (inventoryBound runtime)) (SourceJointClockGraph.clock ∘ values (inventoryBound runtime)))‖ ^ 2 := by
  rw [← variance_original]
  exact full_variance_cost _ _

theorem current_information_lower (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalInventory.cost (inventoryBound runtime) (dynamicRead runtime depth) / (inventoryBound runtime + 1 : ℝ) +
      (Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy (inventoryBound runtime) (dynamicRead runtime depth)) - 1) / 12 ≤
        SourceConditionalVector.dynamicVariance runtime depth := by
  rw [← variance_original]
  exact information_lower _ _

theorem current_decoder_lower (runtime : LivingRuntimeState process) (depth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) :
    SourceConditionalInventory.cost (inventoryBound runtime) (dynamicRead runtime depth) / (inventoryBound runtime + 1 : ℝ) +
      (Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy (inventoryBound runtime) (dynamicRead runtime depth)) - 1) / 12 ≤
        SourceConditionalVector.dynamicError runtime depth decoder := by
  have source := decoder_information_lower (inventoryBound runtime) (dynamicRead runtime depth) decoder
  change _ ≤ SourceConditionalInventory.recoveryError (inventoryBound runtime) depth decoder at source
  rw [SourceConditionalInventory.recovery_error_original] at source
  exact source

theorem current_error_account (runtime : LivingRuntimeState process) (depth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) :
    SourceConditionalVector.dynamicError runtime depth decoder =
      SourceConditionalInventory.cost (inventoryBound runtime) (dynamicRead runtime depth) / (inventoryBound runtime + 1 : ℝ) +
      ‖SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth)
        (SourceWeightedRecovery.taskValue (historyPMF (inventoryBound runtime)) (SourceJointClockGraph.clock ∘ values (inventoryBound runtime)))‖ ^ 2 +
      ∑ i : SourceConditionalModel.Actors runtime, (historyPMF (inventoryBound runtime) i).toReal *
        ‖SourceConditionalVector.realizeModel runtime (SourceConditionalVector.dynamicEstimate runtime depth i) - decoder (dynamicRead runtime depth i)‖ ^ 2 := by
  rw [SourceConditionalVector.dynamic_error_decomposition, current_full_variance]

end
end SourceGInformationCost
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
