import H0mework.Probability.Information.Model
import H0mework.Versions.X.Fock.HistoryConditional.GCostMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInformationReadback

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceConditionalModel (Actors nextRead positive dynamicRead dynamicInformation)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
universe u
attribute [local instance] SourceConditionalNext.Image.valuesFintype
  SourceConditionalNext.Image.valuesMeasurable SourceConditionalNext.Image.valuesSingleton
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem model_information (runtime : LivingRuntimeState process) {Observed : Type u} [DecidableEq Observed]
    (query : Actors runtime → Observed) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) query
      (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) =
        SourceUniformFibreInformation.conditionalEntropy (inventoryBound runtime) query :=
  SourceUniformFibreInformation.image_conditional_entropy _ query _ (SourceActualImageStep.nextRead_injective runtime) _

theorem dynamic_information (runtime : LivingRuntimeState process) (depth : Nat) :
    dynamicInformation runtime depth =
      SourceUniformFibreInformation.conditionalEntropy (inventoryBound runtime) (dynamicRead runtime depth) :=
  model_information runtime (dynamicRead runtime depth)

theorem model_information_cost (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalInventory.cost (inventoryBound runtime) (dynamicRead runtime depth) / (inventoryBound runtime + 1 : ℝ) +
      (Real.exp (2 * dynamicInformation runtime depth) - 1) / 12 ≤ SourceConditionalVector.dynamicVariance runtime depth := by
  rw [dynamic_information]
  exact SourceGInformationCost.current_information_lower runtime depth

theorem model_decoder_cost (runtime : LivingRuntimeState process) (depth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) :
    SourceConditionalInventory.cost (inventoryBound runtime) (dynamicRead runtime depth) / (inventoryBound runtime + 1 : ℝ) +
      (Real.exp (2 * dynamicInformation runtime depth) - 1) / 12 ≤ SourceConditionalVector.dynamicError runtime depth decoder := by
  rw [dynamic_information]
  exact SourceGInformationCost.current_decoder_lower runtime depth decoder

end
end SourceInformationReadback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
