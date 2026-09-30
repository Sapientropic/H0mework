import H0mework.Fock.InverseDistribution.G
import H0mework.Fock.InverseDistribution.InverseDistribution.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionBirth

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceCopyTimeModel
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem model_update (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (read : Nat → Key) (key : Key) :
    SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
      (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next.tick.next)
      (decoder runtime depth word read key) = SourceConditionalNativeBirth.update runtime read key := by
  rw [decoder_next, SourceConditionalNativePosterior.decoder, SourceConditionalStream.project_realization,
    SourceConditionalNativeBirth.update_is_next]

theorem model_feedback (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (read : Nat → Key) (key : Key) :
    SourceCopyNativeSharedUpdate.modelStep runtime.tick.next.tick.next
      (SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
        (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next.tick.next)
        (decoder runtime depth word read key)) = SourceConditionalNativePosterior.effect runtime.tick.next read key := by
  rw [model_update, SourceConditionalNativeBirth.update_is_next]
  rfl

theorem stale_strict (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (read : Nat → Key) :
    (∑ actor : SourceConditionalModel.Actors runtime.tick.next,
      ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor -
        decoder runtime depth word read (read actor.val)‖ ^ 2) <
    ∑ actor : SourceConditionalModel.Actors runtime.tick.next,
      ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor -
        SourceConditionalNativePosterior.decoder runtime read (read actor.val)‖ ^ 2 := by
  simp only [decoder_next]
  exact SourceConditionalNativeBirth.stale_strict runtime read

end
end SourceInverseDistributionBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
