import H0mework.Fock.HistoryConditional.PosteriorRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePosteriorReadback

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceConditionalModel (Actors dynamicRead positive)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem updated_posterior (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (dynamicRead runtime.tick.next depth)).support) :
    readWeight runtime.tick.next (SourceConditionalModelUpdate.updateModel runtime depth value) =
      (fun actor => SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime.tick.next))
        (dynamicRead runtime.tick.next depth) value supported actor) := by
  rw [SourceConditionalModelUpdate.update_is_next, SourceConditionalModelUpdate.modelDecoder, dif_pos supported]
  exact posterior_recovered _ _ _ _

theorem updated_support (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (dynamicRead runtime.tick.next depth)).support)
    (actor : Actors runtime.tick.next) :
    readWeight runtime.tick.next (SourceConditionalModelUpdate.updateModel runtime depth value) actor ≠ 0 ↔
      dynamicRead runtime.tick.next depth actor = value := by
  rw [SourceConditionalModelUpdate.update_is_next, SourceConditionalModelUpdate.modelDecoder, dif_pos supported]
  exact recovered_support _ _ _ _ _

theorem updated_eq_source_iff (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (dynamicRead runtime.tick.next depth)).support)
    (actor : Actors runtime.tick.next) :
    SourceConditionalModelUpdate.updateModel runtime depth value = SourceConditionalModel.nextRead runtime.tick.next actor ↔
      SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime.tick.next))
        (dynamicRead runtime.tick.next depth) value supported = PMF.pure actor := by
  rw [SourceConditionalModelUpdate.update_is_next, SourceConditionalModelUpdate.modelDecoder, dif_pos supported]
  exact estimate_eq_source_iff _ _ _ _ _

theorem updated_mixture_not_actual (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime.tick.next) (depth : Nat) :
    SourceConditionalModelUpdate.updateModel runtime depth (dynamicRead runtime.tick.next depth (0 : Actors runtime.tick.next)) ∉
      Set.range (SourceConditionalModel.nextRead runtime.tick.next) := by
  have supported := SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound runtime.tick.next))
    (dynamicRead runtime.tick.next depth) 0 (positive runtime.tick.next 0)
  rw [SourceConditionalModelUpdate.update_is_next, SourceConditionalModelUpdate.modelDecoder, dif_pos supported]
  exact mixture_not_actual runtime.tick.next (dynamicRead runtime.tick.next depth) _ supported 0
    (SourceConditionalModel.two runtime.tick.next enough) rfl
    (SourceConditionalModel.dynamic_same runtime.tick.next enough depth).symm
    (Ne.symm (SourceConditionalModel.two_ne_zero runtime.tick.next enough))

end
end SourcePosteriorReadback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
