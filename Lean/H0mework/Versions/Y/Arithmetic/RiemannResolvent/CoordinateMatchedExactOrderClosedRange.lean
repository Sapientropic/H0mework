import H0mework.Versions.Y.Arithmetic.RiemannAnnulus.CoordinateNormalizedAnnulusSource
import H0mework.Versions.Y.Arithmetic.RiemannDivision.BareRiemannZeroLocalizedAction
import H0mework.Versions.Y.Arithmetic.RiemannAnnulus.CompactCoPoissonQuarterProjection

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace BurnolPhysicalState

open Complex MeasureTheory Set

noncomputable section

/-- The exact-order quotient coordinate exposed by the same analytic owner and
the coordinate-matched compact source. -/
def burnolCoordinateMatchedLocalizedSpectrum
    (owner : GlobalGermOwner) (coordinate value : ℂ) : ℂ :=
  (2 : ℂ) *
    generatedRiemannBareZeroLocalizedSpectrum owner coordinate value *
      coPoissonMuntzEvenSourceMellin
        (burnolCoordinateNormalizedAnnulusSource coordinate).1 value

/-- The actual compact co-Poisson relation factors by the full source-generated
Xi zero order.  No simple-zero premise or caller-supplied normalizer occurs. -/
theorem burnolCoordinateMatchedQuarterMellin_factorization
    (owner : GlobalGermOwner) (coordinate value : ℂ)
    (valuePositive : 0 < value.re) (valueBelowOne : value.re < 1)
    (valueNeZero : value ≠ 0) (valueNeOne : value ≠ 1)
    (gammaNeZero : Gammaℝ value ≠ 0) :
    mellin
        (positiveMellinExtension
          (coPoissonQuarterMellinMap
            (burnolCoordinateNormalizedAnnulusSource coordinate).1))
        (value / 2) =
      (value - coordinate) ^ generatedRiemannXiZeroOrder owner coordinate *
        burnolCoordinateMatchedLocalizedSpectrum owner coordinate value := by
  rw [positiveMellinExtension_coPoissonQuarterMellinMap_factorization]
  · rw [show (2 : ℂ) * (value / 2) = value by ring,
      ← generatedRiemannZeta_eq_mathlib owner,
      generatedRiemannZeta_zero_factorization owner coordinate value
        valueNeZero valueNeOne gammaNeZero]
    unfold coPoissonQuarterMuntzSourceMellin
      burnolCoordinateMatchedLocalizedSpectrum
    ring
  · rw [Complex.div_re]
    norm_num
    linarith
  · rw [Complex.div_re]
    norm_num
    linarith

/-- The canonical normalization identifies the localized coordinate with the
existing bare-zeta exact-order spectrum literally at its generating point. -/
theorem burnolCoordinateMatchedLocalizedSpectrum_at_eq_bare
    (owner : GlobalGermOwner) (coordinate : ℂ) :
    burnolCoordinateMatchedLocalizedSpectrum owner coordinate coordinate =
      generatedRiemannBareZeroLocalizedSpectrum owner coordinate coordinate := by
  unfold burnolCoordinateMatchedLocalizedSpectrum
  have normalization :=
    burnolCoordinateNormalizedAnnulusSource_mellin_normalization coordinate
  calc
    (2 : ℂ) * generatedRiemannBareZeroLocalizedSpectrum owner coordinate coordinate *
          coPoissonMuntzEvenSourceMellin
            (burnolCoordinateNormalizedAnnulusSource coordinate).1 coordinate =
        generatedRiemannBareZeroLocalizedSpectrum owner coordinate coordinate *
          ((2 : ℂ) * coPoissonMuntzEvenSourceMellin
            (burnolCoordinateNormalizedAnnulusSource coordinate).1 coordinate) := by
      ring
    _ = generatedRiemannBareZeroLocalizedSpectrum owner coordinate coordinate * 1 := by
      rw [normalization]
    _ = _ := mul_one _

/-- At the selected nontrivial zero, exact-order division leaves a nonzero
localized coordinate. -/
theorem burnolCoordinateMatchedLocalizedSpectrum_at_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    burnolCoordinateMatchedLocalizedSpectrum owner observation.coordinate
        observation.coordinate ≠ 0 := by
  rw [burnolCoordinateMatchedLocalizedSpectrum_at_eq_bare]
  exact generatedRiemannBareZeroLocalizedSpectrum_at_ne_zero
    observation nontrivial

/-- Direct source consumer: the selected compact relation has zero Mellin
boundary, its projected physical state is in the existing closed range, while
the source-generated exact-order quotient coordinate is nonzero.  These are
three dependent faces of the same coordinate-matched source. -/
theorem zeroOwnedCoordinateMatchedAnnulus_directConsumer
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    let z := observation.coordinate / 2
    let source := burnolCoordinateNormalizedAnnulusSource observation.coordinate
    let relation := coPoissonQuarterMellinConvergentMap z
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      source.1
    quarterMellinL2Functional z relation = 0 ∧
      quarterMellinAdditiveProjectedPhysicalState relation ∈
        burnolCompactCoPoissonClosedRange ∧
      burnolCoordinateMatchedLocalizedSpectrum owner observation.coordinate
        observation.coordinate ≠ 0 := by
  dsimp only
  refine ⟨?_, ?_,
    burnolCoordinateMatchedLocalizedSpectrum_at_ne_zero
      observation nontrivial⟩
  · exact LinearMap.congr_fun
      (selectedZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
        observation nontrivial)
      (burnolCoordinateNormalizedAnnulusSource observation.coordinate).1
  · exact compactQuarterMellinAdditiveProjectedPhysicalState_mem_closedRange
      (observation.coordinate / 2)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      (burnolCoordinateNormalizedAnnulusSource observation.coordinate)

end
end BurnolPhysicalState
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
