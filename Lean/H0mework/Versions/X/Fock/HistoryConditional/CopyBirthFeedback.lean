import H0mework.Versions.X.Fock.HistoryConditional.CopyBirthSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCopyBirth

open SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

theorem joint_stale (runtime : LivingRuntimeState process)
    (index : SourceCopyObservation.Index (inventoryBound runtime)) :
    (∑ actor : Actors runtime.tick.next,
      ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor -
        SourceConditionalVector.vectorDecoder runtime.tick.next
          (SourceCopyObservation.joint (inventoryBound runtime) (inventoryBound runtime.tick.next) index)
          (SourceCopyObservation.joint (inventoryBound runtime) (inventoryBound runtime.tick.next) index actor)‖ ^ 2) <
    (∑ actor : Actors runtime.tick.next,
      ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor -
        SourceConditionalVector.vectorDecoder runtime
          (SourceCopyObservation.joint (inventoryBound runtime) (inventoryBound runtime) index)
          (SourceCopyObservation.joint (inventoryBound runtime) (inventoryBound runtime.tick.next) index actor)‖ ^ 2) := by
  have paid := SourceConditionalNativeBirth.stale_strict runtime
    (SourceCopyInventory.read (SourceOwnedObservationHistory.NativeCopy.Fock.material (inventoryBound runtime) index))
  simp only [SourceConditionalNativeBirth.total, decoder_original] at paid
  simpa only [SourceCopyInventory.joint_source] using paid

end
end SourceConditionalCopyBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
