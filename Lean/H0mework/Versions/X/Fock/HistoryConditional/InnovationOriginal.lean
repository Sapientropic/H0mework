import H0mework.Versions.X.Fock.HistoryConditional.InnovationUpdate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInnovation

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceObservationInvariantControls (parity)
open SourceConditionalInventory (count bornObservation)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem decoder_current (runtime : LivingRuntimeState process) (depth : Nat) :
    decoder (inventoryBound runtime) depth = SourceConditionalVector.vectorDecoder runtime (SourceConditionalModel.dynamicRead runtime depth) := by
  rw [decoder, SourceConditionalModel.original_runtime]

theorem update_current (runtime : LivingRuntimeState process) (depth : Nat) :
    updateDecoder (inventoryBound runtime) depth =
      SourceConditionalVector.vectorDecoder runtime.tick.next (SourceConditionalModel.dynamicRead runtime.tick.next depth) := by
  rw [update_decoder, decoder, SourceConditionalInventory.next_runtime]

theorem update_attains_current (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalVector.dynamicError runtime.tick.next depth (updateDecoder (inventoryBound runtime) depth) =
      SourceConditionalVector.dynamicVariance runtime.tick.next depth := by
  rw [update_current]
  exact SourceConditionalVector.dynamic_attains _ _

theorem minimum_current (runtime : LivingRuntimeState process) (depth : Nat) :
    ((inventoryBound runtime + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance runtime.tick.next depth =
      ((inventoryBound runtime + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance runtime depth +
        count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) /
          (count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) + 1) *
          ‖SourceCopyNativeModelStep.sourceValue runtime.tick.next.tick.next -
            SourceConditionalVector.vectorDecoder runtime (SourceConditionalModel.dynamicRead runtime depth)
              (bornObservation (inventoryBound runtime) depth)‖ ^ 2 := by
  have paid := minimum_update (inventoryBound runtime) depth
  rw [SourceConditionalInventory.next_runtime, SourceConditionalModel.original_runtime,
    SourceConditionalInventory.born_current, decoder_current] at paid
  exact paid

theorem update_error_current (runtime : LivingRuntimeState process) (depth : Nat) :
    ((inventoryBound runtime + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicError runtime.tick.next depth (updateDecoder (inventoryBound runtime) depth) =
      ((inventoryBound runtime + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance runtime depth +
        count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) /
          (count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) + 1) *
          ‖SourceCopyNativeModelStep.sourceValue runtime.tick.next.tick.next -
            SourceConditionalVector.vectorDecoder runtime (SourceConditionalModel.dynamicRead runtime depth)
              (bornObservation (inventoryBound runtime) depth)‖ ^ 2 := by
  rw [update_attains_current]
  exact minimum_current runtime depth

theorem update_information_current (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceInformationReadback.model_decoder_cost runtime.tick.next depth (updateDecoder (inventoryBound runtime) depth)) :=
  SourceInformationReadback.model_decoder_cost runtime.tick.next depth (updateDecoder (inventoryBound runtime) depth)

end
end SourceConditionalInnovation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
