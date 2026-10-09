import H0mework.Versions.V2.Arithmetic.RieszColumns.Half
import H0mework.Versions.V2.Arithmetic.RieszColumns.Transpose
import H0mework.Versions.V2.Arithmetic.RieszFiniteSource.SourceBoundary

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteColumns

open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszFiniteSource
noncomputable section

/-- The original first integer sample reads the same complete source, its Tate face and both means. -/
def firstSourceRead (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (value : BurnolPaAmbientCarrier) : ℂ :=
  (inner ℂ (burnolAnnulusSamplingL2 (positionColumn coordinate shift) 0) (burnolMobiusSourceL2 value) +
    burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value *
      star (∫ x : ℝ, positionColumn coordinate shift x)) +
  (inner ℂ (burnolAnnulusSamplingL2 (fourierColumn coordinate shift) 0)
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 value)) +
    burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value) *
      star (∫ x : ℝ, fourierColumn coordinate shift x))

theorem forcing_firstSourceRead (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (bounded : |shift| ≤ Real.log 2) (value : BurnolPaAmbientCarrier)
    (inPa : value ∈ burnolCompactCoPoissonClosedRange) :
    inner ℂ (forcingIntegral coordinate shift) (value : BurnolL2) =
      firstSourceRead coordinate shift value := by
  rw [forcingIntegral_columns]
  have generated := twoColumn_fullPa_transpose (positionColumn coordinate shift)
    (fourierColumn coordinate shift) (positionColumn_integrable coordinate shift)
    (positionColumn_firstMoment coordinate shift) (fourierColumn_integrable coordinate shift)
    (fourierColumn_firstMoment coordinate shift) value inPa
  rw [samplingKernel_eq_first_of_half_cutoff _ (positionColumn_half coordinate shift bounded),
    samplingKernel_eq_first_of_half_cutoff _ (fourierColumn_half coordinate shift bounded)] at generated
  exact generated

theorem original_K_sourceAction_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (bounded : |shift| ≤ Real.log 2) (value : BurnolPaAmbientCarrier)
    (inPa : value ∈ burnolCompactCoPoissonClosedRange) :
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
        (burnolMultiplicativeDilation shift (value : BurnolL2)) =
      firstSourceRead coordinate (-shift) value := by
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate zero
  have initial : inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (value : BurnolL2) = 0 :=
    (Submodule.mem_orthogonal' _ _).mp orthogonal value inPa
  have flip := ((burnolMultiplicativeDilation shift).symm.inner_map_eq_flip
    (burnolCompletedMellinRieszVector coordinate : BurnolL2) (value : BurnolL2)).symm
  change inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (burnolMultiplicativeDilation shift (value : BurnolL2)) =
    inner ℂ ((burnolMultiplicativeDilation shift).symm
      (burnolCompletedMellinRieszVector coordinate : BurnolL2)) (value : BurnolL2) at flip
  rw [← burnolMultiplicativeDilation_neg_eq_symm, original_finite_action,
    inner_add_left, inner_smul_left, initial, mul_zero, zero_add] at flip
  exact flip.trans (forcing_firstSourceRead coordinate (-shift)
    (by simpa only [abs_neg] using bounded) value inPa)

end
end OriginalRieszFiniteColumns
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
