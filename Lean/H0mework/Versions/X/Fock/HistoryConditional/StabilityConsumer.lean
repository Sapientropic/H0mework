import H0mework.Versions.X.Fock.HistoryConditional.StabilityCounterexample

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePosteriorStability

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceConditionalModel (Actors NextModel dynamicRead positive)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem updated_inventory_error (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (dynamicRead runtime.tick.next depth)).support)
    (model : NextModel runtime.tick.next) :
    (∑ actor : Actors runtime.tick.next,
      |(SourcePosteriorReadback.readWeight runtime.tick.next model actor).toReal -
        (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime.tick.next))
          (dynamicRead runtime.tick.next depth) value supported actor).toReal| ^ 2) ≤
      ‖SourceConditionalVector.realizeModel runtime.tick.next model -
        SourceConditionalVector.realizeModel runtime.tick.next (SourceConditionalModelUpdate.updateModel runtime depth value)‖ ^ 2 := by
  rw [SourceConditionalModelUpdate.update_is_next, SourceConditionalModelUpdate.modelDecoder, dif_pos supported]
  exact posterior_inventory_error _ _ _ _ _

theorem updated_support_restored (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (dynamicRead runtime.tick.next depth)).support)
    (model : NextModel runtime.tick.next)
    (small : ‖SourceConditionalVector.realizeModel runtime.tick.next model -
      SourceConditionalVector.realizeModel runtime.tick.next (SourceConditionalModelUpdate.updateModel runtime depth value)‖ < threshold runtime.tick.next) :
    restoredSupport runtime.tick.next model =
      SourceUniformFibreVariance.fibre (inventoryBound runtime.tick.next) (dynamicRead runtime.tick.next depth) value := by
  rw [SourceConditionalModelUpdate.update_is_next, SourceConditionalModelUpdate.modelDecoder, dif_pos supported] at small
  exact support_restored _ _ _ _ _ small

theorem profile_error_budget (runtime : LivingRuntimeState process) (depth : Nat) (models : Field parity → NextModel runtime) :
    (∑ index : Actors runtime, (historyPMF (inventoryBound runtime) index).toReal *
      ∑ actor : Actors runtime,
        |(SourcePosteriorReadback.readWeight runtime (models (dynamicRead runtime depth index)) actor).toReal -
          (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth)
            (dynamicRead runtime depth index) (SourceWeightedRecovery.observed_supported _ _ index (positive runtime index)) actor).toReal| ^ 2) ≤
      SourceConditionalVector.dynamicError runtime depth (fun value => SourceConditionalVector.realizeModel runtime (models value)) -
        SourceConditionalVector.dynamicVariance runtime depth := by
  have localBound (index : Actors runtime) := weights_inventory runtime
    (models (dynamicRead runtime depth index)) (SourceConditionalVector.dynamicEstimate runtime depth index)
  have multiplied (index : Actors runtime) := mul_le_mul_of_nonneg_left (localBound index)
    (ENNReal.toReal_nonneg (a := historyPMF (inventoryBound runtime) index))
  have summed := Finset.sum_le_sum (fun index (_ : index ∈ (Finset.univ : Finset (Actors runtime))) => multiplied index)
  have account :
      (∑ index : Actors runtime, (historyPMF (inventoryBound runtime) index).toReal *
        ‖SourceConditionalVector.realizeModel runtime (models (dynamicRead runtime depth index)) -
          SourceConditionalVector.realizeModel runtime (SourceConditionalVector.dynamicEstimate runtime depth index)‖ ^ 2) =
        SourceConditionalVector.dynamicError runtime depth (fun value => SourceConditionalVector.realizeModel runtime (models value)) -
          SourceConditionalVector.dynamicVariance runtime depth := by
    rw [SourceConditionalVector.dynamic_error_decomposition, add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro index _
    rw [norm_sub_rev (SourceConditionalVector.realizeModel runtime (models (dynamicRead runtime depth index)))
      (SourceConditionalVector.realizeModel runtime (SourceConditionalVector.dynamicEstimate runtime depth index))]
  have bounded := summed.trans_eq account
  simpa only [SourceConditionalVector.dynamicEstimate, SourcePosteriorReadback.weight_estimate] using bounded

end
end SourcePosteriorStability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
