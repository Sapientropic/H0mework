import H0mework.Fock.HistoryConditional.ModelUpdateAction

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalModelUpdate

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceConditionalModel (dynamicRead)
open SourceObservationInvariantControls (parity)
open SourceConditionalInventory (count bornObservation)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem update_attains (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalVector.dynamicError runtime.tick.next depth
      (fun value => SourceConditionalVector.realizeModel runtime.tick.next (updateModel runtime depth value)) =
        SourceConditionalVector.dynamicVariance runtime.tick.next depth := by
  rw [decoded_update]
  exact SourceConditionalInnovation.update_attains_current runtime depth

theorem update_error (runtime : LivingRuntimeState process) (depth : Nat) :
    ((inventoryBound runtime + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicError runtime.tick.next depth
      (fun value => SourceConditionalVector.realizeModel runtime.tick.next (updateModel runtime depth value)) =
      ((inventoryBound runtime + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance runtime depth +
        count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) /
          (count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) + 1) *
          ‖SourceCopyNativeModelStep.sourceValue runtime.tick.next.tick.next -
            SourceConditionalVector.vectorDecoder runtime (dynamicRead runtime depth)
              (bornObservation (inventoryBound runtime) depth)‖ ^ 2 := by
  rw [decoded_update]
  exact SourceConditionalInnovation.update_error_current runtime depth

theorem information_cost (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceInformationReadback.model_decoder_cost runtime.tick.next depth
      (fun value => SourceConditionalVector.realizeModel runtime.tick.next (updateModel runtime depth value))) :=
  SourceInformationReadback.model_decoder_cost runtime.tick.next depth _

theorem fresh_model_recovers (runtime : LivingRuntimeState process) (depth : Nat)
    (fresh : bornObservation (inventoryBound runtime) depth ∉
      ((historyPMF (inventoryBound runtime)).map (SourceConditionalInventory.observation (inventoryBound runtime) depth)).support) :
    updateModel runtime depth (bornObservation (inventoryBound runtime) depth) = (SourceActualImageStep.birth runtime).val := by
  apply SourceActualImageStep.realize_injective runtime.tick.next
  rw [update_realization, birth_realization]
  exact SourceConditionalInnovation.update_recovers_fresh (inventoryBound runtime) depth fresh

end
end SourceConditionalModelUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
