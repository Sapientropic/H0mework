import H0mework.Versions.X.Fock.HistoryCopy.ObservationInformation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyObservation

open SourceWeightedRecovery SourceConditionalInventory SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open scoped Classical
noncomputable section

local instance fieldParentMeasurable : MeasurableSpace ParentCarrier := ⊤

def jointSnapshot (depth : Nat) (index : Index depth) (value : Field nativeStep (rawWords depth)) : ParentCarrier × ParentCarrier :=
  (inputSnapshot depth value, copySnapshot depth index value)

theorem joint_original_read (depth bound : Nat) (index : Index depth) (actor : Fin (bound + 1)) :
    jointSnapshot depth index (Actor.originalRead depth bound actor) = joint depth bound index actor := rfl

theorem original_decoder_lower (depth bound : Nat)
    (decoder : Fin (bound + 1) → ParentCarrier → ℂ) :
    cost bound (before depth bound) ≤ ∑ actor,
      error (historyPMF bound) (Actor.originalRead depth bound)
        (fun point => (unitTask bound actor point : ℂ)) (decoder actor ∘ inputSnapshot depth) := by
  have generated := all_decoder_lower bound (before depth bound) decoder
  rw [← cost_eq] at generated
  simpa only [before, error, Function.comp_apply] using generated

theorem original_joint_decoder_error (depth bound : Nat) (index : Index depth)
    (decoder : Fin (bound + 1) → ParentCarrier × ParentCarrier → ℂ) :
    (∑ actor, error (historyPMF bound) (Actor.originalRead depth bound)
      (fun point => (unitTask bound actor point : ℂ)) (decoder actor ∘ jointSnapshot depth index)) =
      cost bound (joint depth bound index) +
      ∑ actor, error (historyPMF bound) (joint depth bound index)
        (fun point => optimalDecoder (historyPMF bound) (joint depth bound index)
          (fun original => (unitTask bound actor original : ℂ)) (joint depth bound index point)) (decoder actor) := by
  have generated := all_decoder_error bound (joint depth bound index) decoder
  rw [← cost_eq] at generated
  simpa only [error, Function.comp_apply, joint_original_read] using generated

theorem original_conditional_transfer (depth bound : Nat) (index : Index depth) (value : FieldSpace depth bound)
    (atom : ParentCarrier × ParentCarrier)
    (supported : atom ∈ (SourceWeightedRecovery.observed (historyPMF bound) (joint depth bound index)).support) :
    SourceWeightedRecovery.transfer (historyPMF bound) (joint depth bound index)
        (Actor.currentPullback depth bound value) atom =
      ∑ actor : Fin (bound + 1),
        (SourceConditionalHistory.conditional (historyPMF bound) (joint depth bound index) atom supported actor).toReal •
          value (Actor.originalRead depth bound actor) := by
  have sameTask : taskValue (historyPMF bound) (fun actor => value (Actor.originalRead depth bound actor)) =
      Actor.currentPullback depth bound value := by
    apply MeasureTheory.Lp.ext
    exact Filter.Eventually.of_forall fun actor =>
      (taskValue_at _ _ actor (SourceUniformFibreVariance.source_positive bound actor)).trans
        (Actor.currentPullback_at depth bound value actor).symm
  rw [← sameTask]
  exact optimal_is_conditional (historyPMF bound) (joint depth bound index)
    (fun actor => value (Actor.originalRead depth bound actor)) atom supported

theorem original_reconstruction (depth bound : Nat) (index : Index depth) (value : FieldSpace depth bound) :
    Actor.currentTransfer depth bound
        (SourceWeightedRecovery.pullback (historyPMF bound) (joint depth bound index)
          (SourceWeightedRecovery.transfer (historyPMF bound) (joint depth bound index)
            (Actor.currentPullback depth bound value))) +
      Actor.currentTransfer depth bound
        (SourceWeightedRecovery.residual (historyPMF bound) (joint depth bound index)
          (Actor.currentPullback depth bound value)) = value := by
  have generated := congrArg (Actor.currentTransfer depth bound)
    (IsometricRetainedTransfer.pullback_transfer_add_residual
      (SourceWeightedRecovery.pullback (historyPMF bound) (joint depth bound index))
      (Actor.currentPullback depth bound value))
  rw [map_add] at generated
  exact generated.trans (IsometricRetainedTransfer.transfer_pullback (Actor.currentPullback depth bound) value)

theorem original_energy (depth bound : Nat) (index : Index depth) (value : FieldSpace depth bound) :
    ‖value‖ ^ 2 =
      ‖SourceWeightedRecovery.transfer (historyPMF bound) (joint depth bound index)
        (Actor.currentPullback depth bound value)‖ ^ 2 +
      ‖Actor.currentTransfer depth bound
        (SourceWeightedRecovery.residual (historyPMF bound) (joint depth bound index)
          (Actor.currentPullback depth bound value))‖ ^ 2 := by
  rw [actor_transfer_norm]
  have generated := IsometricRetainedTransfer.energy_decomposition
    (SourceWeightedRecovery.pullback (historyPMF bound) (joint depth bound index))
    (Actor.currentPullback depth bound value)
  simpa only [(Actor.currentPullback depth bound).norm_map] using generated

theorem original_inventory_cost (depth bound : Nat) (index : Index depth) :
    (∑ actor : Fin (bound + 1),
      ‖Actor.currentTransfer depth bound
        (SourceWeightedRecovery.residual (historyPMF bound) (joint depth bound index)
          (taskValue (historyPMF bound) (fun point => (unitTask bound actor point : ℂ))))‖ ^ 2) =
      cost bound (joint depth bound index) := by
  simp_rw [actor_transfer_norm]
  rfl

end
end SourceCopyObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
