import H0mework.Versions.Y.Arithmetic.RiemannResolvent.AnalyticComplementExactOrderResolvent

/-!
# Cancellation-aware analytic-complement finite part

Away from resonance, one right-resolvent orbit contributes the Cauchy
factor `1/(z+w-1/2)`.  At resonance that scalar kernel is not integrable, so
the full source-generated Xi zero factor is cancelled first.  The resulting
finite part is nonzero for arbitrary zero multiplicity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState

noncomputable section

theorem positiveMellinQuarterRightResolvent_scalarKernel
    (z w : ℂ)
    (decay : (((1 / 2 : ℂ) - z - w).re < 0)) :
    (∫ shift : ℝ in Ioi (0 : ℝ),
      positiveMellinQuarterRightResolventWeight z shift *
        quarterDilationCharacter w (Real.exp shift)) =
      1 / (z + w - (1 / 2 : ℂ)) := by
  have integrand : (fun shift : ℝ =>
      positiveMellinQuarterRightResolventWeight z shift *
        quarterDilationCharacter w (Real.exp shift)) =
      fun shift : ℝ =>
        Complex.exp (((1 / 2 : ℂ) - z - w) * (shift : ℂ)) := by
    funext shift
    unfold positiveMellinQuarterRightResolventWeight quarterDilationCharacter
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero shift))]
    rw [← Complex.ofReal_log (Real.exp_pos shift).le, Real.log_exp]
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [integrand, integral_exp_mul_complex_Ioi decay 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have denominator : z + w - (1 / 2 : ℂ) =
      -((1 / 2 : ℂ) - z - w) := by ring
  rw [denominator]
  field_simp

/-- The full-coordinate factorization in the quarter coordinate seen by the
feature completion. -/
def burnolAnalyticComplementQuarterQuotient
    (owner : GlobalGermOwner)
    (observation : GeneratedRiemannZeroObservationAt owner)
    (w : ℂ) : ℂ :=
  (2 : ℂ) ^ generatedRiemannXiZeroOrder owner observation.coordinate *
    burnolCoordinateMatchedLocalizedSpectrum owner
      (1 - observation.coordinate) (2 * w)

theorem burnolAnalyticComplementQuarter_factorization
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (w : ℂ)
    (valuePositive : 0 < (2 * w).re) (valueBelowOne : (2 * w).re < 1)
    (valueNeZero : 2 * w ≠ 0) (valueNeOne : 2 * w ≠ 1)
    (gammaNeZero : Gammaℝ (2 * w) ≠ 0) :
    mellin
        (positiveMellinExtension
          (coPoissonQuarterMellinMap
            (burnolAnalyticComplementNormalizedSource observation).1)) w =
      (w - ((1 / 2 : ℂ) - observation.coordinate / 2)) ^
          generatedRiemannXiZeroOrder owner observation.coordinate *
        burnolAnalyticComplementQuarterQuotient owner observation w := by
  have source := burnolAnalyticComplementNormalizedSource_factorization
    observation (2 * w) valuePositive valueBelowOne valueNeZero valueNeOne
      gammaNeZero
  rw [show (2 * w) / 2 = w by ring] at source
  rw [source]
  unfold burnolAnalyticComplementQuarterQuotient
  have base :
      2 * w - (1 - observation.coordinate) =
        2 * (w - ((1 / 2 : ℂ) - observation.coordinate / 2)) := by
    ring
  rw [base, mul_pow]
  ring

theorem burnolAnalyticComplementQuarterQuotient_at
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    burnolAnalyticComplementQuarterQuotient owner observation
        ((1 / 2 : ℂ) - observation.coordinate / 2) =
      (2 : ℂ) ^ generatedRiemannXiZeroOrder owner observation.coordinate *
        ((-1 : ℂ) ^ generatedRiemannXiZeroOrder owner observation.coordinate *
          (Gammaℝ observation.coordinate /
            Gammaℝ (1 - observation.coordinate)) *
          generatedRiemannBareZeroLocalizedSpectrum owner
            observation.coordinate observation.coordinate) := by
  unfold burnolAnalyticComplementQuarterQuotient
  rw [show 2 * ((1 / 2 : ℂ) - observation.coordinate / 2) =
      1 - observation.coordinate by ring]
  rw [burnolAnalyticComplementNormalizedSource_localizedRead
    observation nontrivial]

/-- The finite part after all right-resolvent divisions. -/
def burnolAnalyticComplementIteratedResolventFinitePart
    (owner : GlobalGermOwner)
    (observation : GeneratedRiemannZeroObservationAt owner)
    (w : ℂ) : ℂ :=
  (-1 : ℂ) ^ generatedRiemannXiZeroOrder owner observation.coordinate *
    burnolAnalyticComplementQuarterQuotient owner observation w

/-- Nonresonant Fubini calculation for all generated divisions.  This
identity justifies the finite part without evaluating the divergent kernel
at resonance. -/
theorem burnolAnalyticComplementIteratedResolvent_nonresonantFubini
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (w : ℂ)
    (decay : (((1 / 2 : ℂ) - observation.coordinate / 2 - w).re < 0))
    (valuePositive : 0 < (2 * w).re) (valueBelowOne : (2 * w).re < 1)
    (valueNeZero : 2 * w ≠ 0) (valueNeOne : 2 * w ≠ 1)
    (gammaNeZero : Gammaℝ (2 * w) ≠ 0)
    (nonresonant : w ≠ (1 / 2 : ℂ) - observation.coordinate / 2) :
    (-∫ shift : ℝ in Ioi (0 : ℝ),
        positiveMellinQuarterRightResolventWeight
            (observation.coordinate / 2) shift *
          quarterDilationCharacter w (Real.exp shift)) ^
          generatedRiemannXiZeroOrder owner observation.coordinate *
        mellin
          (positiveMellinExtension
            (coPoissonQuarterMellinMap
              (burnolAnalyticComplementNormalizedSource observation).1)) w =
      burnolAnalyticComplementIteratedResolventFinitePart
        owner observation w := by
  have kernel := positiveMellinQuarterRightResolvent_scalarKernel
    (observation.coordinate / 2) w decay
  have factorization := burnolAnalyticComplementQuarter_factorization
    observation w valuePositive valueBelowOne valueNeZero valueNeOne
      gammaNeZero
  let difference : ℂ :=
    w - ((1 / 2 : ℂ) - observation.coordinate / 2)
  have differenceNe : difference ≠ 0 := sub_ne_zero.mpr nonresonant
  have powerNe :
      difference ^ generatedRiemannXiZeroOrder owner observation.coordinate ≠ 0 :=
    pow_ne_zero _ differenceNe
  have denominator : observation.coordinate / 2 + w - (1 / 2 : ℂ) =
      difference := by
    dsimp only [difference]
    ring
  rw [kernel, denominator, factorization]
  unfold burnolAnalyticComplementIteratedResolventFinitePart
  rw [show -(1 / difference) = (-1 : ℂ) / difference by ring,
    div_pow]
  field_simp [powerNe]
  ring

theorem burnolAnalyticComplementIteratedResolventFinitePart_at
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    burnolAnalyticComplementIteratedResolventFinitePart owner observation
        ((1 / 2 : ℂ) - observation.coordinate / 2) =
      (2 : ℂ) ^ generatedRiemannXiZeroOrder owner observation.coordinate *
        (Gammaℝ observation.coordinate /
          Gammaℝ (1 - observation.coordinate)) *
        generatedRiemannBareZeroLocalizedSpectrum owner
          observation.coordinate observation.coordinate := by
  unfold burnolAnalyticComplementIteratedResolventFinitePart
  rw [burnolAnalyticComplementQuarterQuotient_at observation nontrivial]
  let sign : ℂ :=
    (-1 : ℂ) ^ generatedRiemannXiZeroOrder owner observation.coordinate
  have signSq : sign * sign = 1 := by
    dsimp only [sign]
    rw [← mul_pow]
    norm_num
  change sign *
      ((2 : ℂ) ^ generatedRiemannXiZeroOrder owner observation.coordinate *
        (sign *
          (Gammaℝ observation.coordinate /
            Gammaℝ (1 - observation.coordinate)) *
          generatedRiemannBareZeroLocalizedSpectrum owner
            observation.coordinate observation.coordinate)) = _
  calc
    _ = (2 : ℂ) ^ generatedRiemannXiZeroOrder owner observation.coordinate *
        (sign * sign) *
        (Gammaℝ observation.coordinate /
          Gammaℝ (1 - observation.coordinate)) *
        generatedRiemannBareZeroLocalizedSpectrum owner
          observation.coordinate observation.coordinate := by ring
    _ = _ := by rw [signSq, mul_one]

/-- Scalar produced after the additive rechart and homogeneous Fourier
transport back to the selected right-half coordinate. -/
def burnolAnalyticComplementExpectedPhysicalFourierRead
    (owner : GlobalGermOwner)
    (observation : GeneratedRiemannZeroObservationAt owner) : ℂ :=
  (Gammaℝ (1 - observation.coordinate) / Gammaℝ observation.coordinate) *
    (1 / 2 : ℂ) *
      burnolAnalyticComplementIteratedResolventFinitePart owner observation
        ((1 / 2 : ℂ) - observation.coordinate / 2)

theorem burnolAnalyticComplementExpectedPhysicalFourierRead_eq
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    burnolAnalyticComplementExpectedPhysicalFourierRead owner observation =
      ((2 : ℂ) ^ generatedRiemannXiZeroOrder owner observation.coordinate / 2) *
        generatedRiemannBareZeroLocalizedSpectrum owner
          observation.coordinate observation.coordinate := by
  rw [burnolAnalyticComplementExpectedPhysicalFourierRead,
    burnolAnalyticComplementIteratedResolventFinitePart_at
      observation nontrivial]
  have gammaSelectedNe : Gammaℝ observation.coordinate ≠ 0 :=
    observation.gammaReal_ne_zero_of_nontrivial nontrivial
  have gammaComplementNe : Gammaℝ (1 - observation.coordinate) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.sub_re, Complex.one_re]
    linarith [observation.coordinate_re_lt_one]
  field_simp [gammaSelectedNe, gammaComplementNe]

theorem burnolAnalyticComplementExpectedPhysicalFourierRead_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    burnolAnalyticComplementExpectedPhysicalFourierRead owner observation ≠ 0 := by
  rw [burnolAnalyticComplementExpectedPhysicalFourierRead_eq
    observation nontrivial]
  exact mul_ne_zero
    (div_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num))
    (generatedRiemannBareZeroLocalizedSpectrum_at_ne_zero
      observation nontrivial)

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
