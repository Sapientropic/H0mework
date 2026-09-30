import H0mework.Versions.Y.Arithmetic.MobiusSource.TateForcing

/-! The two unchanged paired-projection corrections are generated from one source and its actual reciprocal. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped InnerProductSpace ENNReal
noncomputable section
local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
local notation "q" => (1 / 4 : ℝ)

/-- The installed block solve is fed by an actual L² source, not by a
second independent Hilbert-state coordinate. -/
def burnolPaIntervalSourceCorrection (shift : ℝ) (source : BurnolL2) : BurnolL2 :=
  let b := burnolMeanZeroBlockInverse
    (burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto
      (burnolQuarterRestriction (burnolMultiplicativeDilation shift source)))
  burnolAmbientEvenPart
    (burnolQuarterZeroExtension (b : BurnolQuarterIntervalL2) -
      fourierL2 (burnolQuarterZeroExtension
        (burnolMeanZeroTruncatedFourier b : BurnolQuarterIntervalL2)))

/-- Both corrections in the unchanged paired action come from one
extracted source and its generated reciprocal action. -/
theorem burnolPaPairedProjection_oneSource (shift : ℝ)
    (nonnegative : 0 ≤ shift) (small : shift ≤ Real.log 2) (value : Ambient)
    (inPa : value ∈ burnolCompactCoPoissonClosedRange) :
    (burnolPairedAmbientCompression shift value : BurnolL2) =
      pairedBurnolMultiplicativeDilation shift (value : BurnolL2) -
        (1 / 2 : ℂ) •
          (burnolPaIntervalSourceCorrection shift (burnolMobiusSourceL2 value) +
            fourierL2 (burnolPaIntervalSourceCorrection shift
              (burnolTateReciprocalL2 (burnolMobiusSourceL2 value)))) := by
  have sourceFourier : burnolMobiusSourceL2
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value) =
        burnolTateReciprocalL2 (burnolMobiusSourceL2 value) :=
    burnolMobiusSource_fourier value inPa
  rw [burnolFirstCellPairedProjection_formula shift nonnegative small value]
  change pairedBurnolMultiplicativeDilation shift (value : BurnolL2) -
      (1 / 2 : ℂ) •
        (burnolPaIntervalSourceCorrection shift (burnolMobiusSourceL2 value) +
          fourierL2 (burnolPaIntervalSourceCorrection shift (burnolMobiusSourceL2
            (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value)))) = _
  rw [sourceFourier]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
