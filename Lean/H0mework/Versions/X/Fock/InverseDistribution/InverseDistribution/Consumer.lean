import H0mework.Versions.X.Fock.InverseDistribution.Moments
import H0mework.Versions.X.Fock.HistoryConditional.NativePosteriorEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeInverseDistribution

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceCopyTimeModel
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem decoder_residual (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (read : Nat → Key) (key : Key) :
    let weights := (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let remainder := SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (residual (inventoryBound runtime) program weights))
    SourceGWordInverse.residual depth word (SourceConditionalNativePosterior.decoder runtime read key) +
      SourceCompiledGWord.effect depth word (SourceCopyGraph.axes (mass remainder)
        ((program.1 : ℂ)⁻¹ * (SourceJointClockGraph.clock remainder - (program.2 : ℂ) * mass remainder))) = remainder := by
  dsimp only
  change SourceConditionalNativePosterior.decoder runtime read key -
    SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime read key)) + _ = _
  rw [decoder_moments, map_add, ← decoder_reconstruction runtime depth word read key]
  abel

theorem model_feedback (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (read : Nat → Key) (key : Key) :
    let weights := (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceCopyNativeSharedUpdate.modelStep runtime.tick.next
      (SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
        (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next)
        (SourceCompiledGWord.effect depth word (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
          (recovered (inventoryBound runtime) program weights))) +
          SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (residual (inventoryBound runtime) program weights)))) =
      SourceConditionalNativePosterior.effect runtime read key := by
  dsimp only
  rw [decoder_reconstruction, SourceConditionalNativePosterior.decoder, SourceConditionalStream.project_realization]
  rfl

end
end SourceNativeInverseDistribution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
