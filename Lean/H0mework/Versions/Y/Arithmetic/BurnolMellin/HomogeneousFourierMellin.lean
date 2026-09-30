import H0mework.Versions.Y.Arithmetic.BurnolMellin.GenericGaussianFubini
import H0mework.Versions.Y.Arithmetic.BurnolMellin.SourceStripGaussianFubini

/-! # Homogeneous Fourier--Mellin identity on the Burnol physical face -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory

noncomputable section

/-- Ordinary Fourier transports the completed right-half evaluator to the
actual complementary source read.  The left-half side is paid by the same
compact co-Poisson source throughout the open strip. -/
theorem burnolCompactAdditiveFourierHomogeneousIdentity
    (source : burnolCompactAnnulusSource)
    (coordinate : BurnolCompletedMellinCoordinate) :
    Gammaℝ coordinate.value *
        burnolCompletedMellinEvaluator coordinate
          (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
            (burnolCompactAdditivePhysicalState source)) =
      Gammaℝ (1 - coordinate.value) *
        burnolCompactAdditiveMellinRead source (1 - coordinate.value) := by
  rw [burnolGenericHomogeneousGammaMellinBridge]
  have heatFourier := burnolGenericGaussianFourierHomogeneousIdentity
    (burnolCompactAdditivePhysicalState source) coordinate.value
  change (1 / 2 : ℂ) * mellin
      (burnolGenericGaussianHeatPairTotal
        (fourierL2 (burnolCompactAdditivePhysicalState source : BurnolL2)))
      (coordinate.value / 2) = _
  rw [heatFourier]
  have complementPositive : 0 < (1 - coordinate.value).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [coordinate.belowOne]
  have complementBelowOne : (1 - coordinate.value).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [coordinate.rightHalf]
  change (1 / 2 : ℂ) * mellin
      (burnolGenericGaussianHeatPairTotal (burnolCompactAdditiveL2 source))
      ((1 - coordinate.value) / 2) = _
  rw [burnolSourceStripGaussianFubini source (1 - coordinate.value)
    complementPositive complementBelowOne]

end


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
