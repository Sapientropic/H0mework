import H0mework.NavierStokes.CorrectionControl.WholeActual

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeTurbulenceControl

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw

noncomputable section

/-- The bounded whole-carrier read is the literal force in the already
generated native equation, on the same source-selected block and receipt. -/
theorem native_equation_controlled {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry)
    (block index : Nat)
    (inBlock : index ∈ Finset.Ico (law.blocks.contactIndex block) (law.blocks.contactIndex (block + 1)))
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    let modes := wholeRestartModes (2 * (law.blocks.contactIndex block + 1))
    let receipt := (run initial index).nextContact.prefixReceipt
    (∀ᵐ time ∂commonTimeMeasure (run initial index).nextContact.time.1,
      (if wave ∈ modes then receipt.rowTangent wave nonzero time else 0) =
        wholeLatticeVorticityFourierTangentAt nu.coeff (complexSharpSupportProjection modes (receipt.wholePath time)) wave +
          integerWaveNormSq wave ^ 2 • receiptWholeCorrection receipt modes time wave) ∧
    (∀ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
      ‖puncturedEuclideanize (receiptWholeCorrection receipt modes time)‖ ^ 2 ≤
        3 * wholeBudget ‖puncturedWholeVelocityEuclideanState initial.initialState‖) := by
  dsimp only
  constructor
  · filter_upwards [law.fourierLaw block index inBlock wave nonzero] with time equation
    rw [receiptWholeCorrection, wholeCorrection_reconstruct]
    exact equation
  · exact original_wholeCorrection_norm_sq_le initial index _

end
end SaturationMonoid.NavierStokes.NativeTurbulenceControl
