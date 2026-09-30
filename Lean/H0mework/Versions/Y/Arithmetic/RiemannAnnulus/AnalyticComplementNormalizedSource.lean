import H0mework.Versions.Y.Arithmetic.RiemannDivision.RiemannXiComplementLocalization
import H0mework.Versions.Y.Arithmetic.RiemannResolvent.CoordinateMatchedExactOrderClosedRange

/-!
# Analytic-complement normalized compact source

For a zero coordinate `rho`, the right resolvent at `rho/2` is resonant with
the additive Mellin coordinate `(1-rho)/2`.  The compact source is therefore
normalized at `1-rho`, while remaining owned by the same zero occurrence.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace BurnolPhysicalState

open Complex

noncomputable section

def burnolAnalyticComplementNormalizedSource
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    burnolCompactAnnulusSource :=
  burnolCoordinateNormalizedAnnulusSource (1 - observation.coordinate)

/-- The same source exposes the full zero order at the coordinate actually
resonant with the right resolvent. -/
theorem burnolAnalyticComplementNormalizedSource_factorization
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (value : ℂ)
    (valuePositive : 0 < value.re) (valueBelowOne : value.re < 1)
    (valueNeZero : value ≠ 0) (valueNeOne : value ≠ 1)
    (gammaNeZero : Gammaℝ value ≠ 0) :
    mellin
        (positiveMellinExtension
          (coPoissonQuarterMellinMap
            (burnolAnalyticComplementNormalizedSource observation).1))
        (value / 2) =
      (value - (1 - observation.coordinate)) ^
          generatedRiemannXiZeroOrder owner observation.coordinate *
        burnolCoordinateMatchedLocalizedSpectrum owner
          (1 - observation.coordinate) value := by
  have source := burnolCoordinateMatchedQuarterMellin_factorization
    owner (1 - observation.coordinate) value valuePositive valueBelowOne
      valueNeZero valueNeOne gammaNeZero
  rw [generatedRiemannXiZeroOrder_one_sub] at source
  exact source

/-- The complement-normalized source reads the selected bare localization
with the exact functional-equation sign and Gamma ratio. -/
theorem burnolAnalyticComplementNormalizedSource_localizedRead
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    burnolCoordinateMatchedLocalizedSpectrum owner
        (1 - observation.coordinate) (1 - observation.coordinate) =
      (-1 : ℂ) ^ generatedRiemannXiZeroOrder owner observation.coordinate *
        (Gammaℝ observation.coordinate / Gammaℝ (1 - observation.coordinate)) *
          generatedRiemannBareZeroLocalizedSpectrum owner
            observation.coordinate observation.coordinate := by
  rw [burnolCoordinateMatchedLocalizedSpectrum_at_eq_bare]
  exact generatedRiemannBareZeroLocalizedSpectrum_one_sub_at
    observation nontrivial

theorem burnolAnalyticComplementNormalizedSource_localizedRead_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    burnolCoordinateMatchedLocalizedSpectrum owner
        (1 - observation.coordinate) (1 - observation.coordinate) ≠ 0 := by
  rw [burnolCoordinateMatchedLocalizedSpectrum_at_eq_bare]
  exact generatedRiemannBareZeroLocalizedSpectrum_one_sub_at_ne_zero
    observation nontrivial

end
end BurnolPhysicalState
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
