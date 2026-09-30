import H0mework.Versions.X.Fock.InverseDistribution.InverseDistribution.G
import H0mework.Versions.X.Fock.HistoryConditional.GWordInverseClock

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeInverseDistribution

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceCopyTimeModel
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

private theorem axes_of_hilbert_zero (value : SourceJointClockGraph.Carrier) (zero : hilbert value = 0) :
    value = SourceCopyGraph.axes (mass value) (SourceJointClockGraph.clock value) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    exact Prod.ext zero rfl
  · rfl

theorem residual_recovery (bound depth : Nat) (word : List (Fock.Letter depth)) (weights : Fin (bound + 1) → ℚ) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let value := SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (residual bound program weights))
    SourceGWordInverse.recover depth word value =
      SourceCopyGraph.axes (mass value) ((program.1 : ℂ)⁻¹ * (SourceJointClockGraph.clock value - (program.2 : ℂ) * mass value)) := by
  dsimp only
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  let value := SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (residual bound program weights))
  change SourceGWordInverse.recover depth word value =
    SourceCopyGraph.axes (mass value) ((program.1 : ℂ)⁻¹ * (SourceJointClockGraph.clock value - (program.2 : ℂ) * mass value))
  have zero : hilbert (SourceGWordInverse.recover depth word value) = 0 := by
    apply lp.ext
    funext coordinate
    rw [SourceGWordInverse.hilbert_recover]
    change SourceSuccessorBoundary.readWord (SourceConditionalRationalStream.embedWord (residual bound program weights))
      (SourceCopyWordAffine.execute program coordinate) = 0
    rw [SourceSuccessorBoundary.readWord_coordinate]
    change ((residual bound program weights (SourceCopyWordAffine.execute program coordinate) : ℚ) : ℂ) = 0
    rw [residual_image_zero bound program (SourceCompiledWordOperator.slope_positive _) weights coordinate]
    simp only [Rat.cast_zero]
  rw [axes_of_hilbert_zero _ zero, SourceGWordInverse.mass_recover, SourceGWordInverse.clock_recover]

theorem decoder_moments {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let weights := (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let remainder := SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (residual (inventoryBound runtime) program weights))
    SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime read key) =
      SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (recovered (inventoryBound runtime) program weights)) +
      SourceCopyGraph.axes (mass remainder)
        ((program.1 : ℂ)⁻¹ * (SourceJointClockGraph.clock remainder - (program.2 : ℂ) * mass remainder)) := by
  dsimp only
  rw [decoder_inverse, residual_recovery]

end
end SourceNativeInverseDistribution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
