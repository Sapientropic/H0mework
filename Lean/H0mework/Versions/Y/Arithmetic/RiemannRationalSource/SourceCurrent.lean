import Mathlib.Analysis.Calculus.Deriv.Star
import H0mework.Versions.Y.Arithmetic.RiemannRationalSource.ReciprocalCells
import H0mework.Versions.Y.Arithmetic.RiemannRationalSource.SecondPrimitive

/-! The source-generated second primitive is tested against the actual reciprocal cell. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def reciprocalGreenCurrent (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (n k : ℕ) (t : ℝ) : ℂ :=
  secondFlux coordinate source t * reciprocalSampleWave coordinate.value n k t -
    secondCoefficient coordinate source t * reciprocalSampleFlux coordinate.value n k t

theorem reciprocalGreenCurrent_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (n k : ℕ) (positive : 0 < n)
    {t : ℝ} (lower : (1 / 4 : ℝ) ≤ t) :
    HasDerivAt (reciprocalGreenCurrent coordinate source n k)
      (4 * source.1 t * reciprocalSampleWave coordinate.value n k t +
        (2 * coordinate.value - 1) * secondCoefficient coordinate source t / (t : ℂ)) t := by
  have tp : 0 < t := lt_of_lt_of_le (by norm_num) lower
  have generated := ((secondFlux_derivative coordinate source lower).mul
    (reciprocal_sample_derivative coordinate n k positive tp)).sub
      ((secondCoefficient_derivative coordinate source lower).mul
        (reciprocal_sample_flux_derivative coordinate n k positive tp))
  convert! generated using 1
  simp only [Complex.cpow_neg, Complex.cpow_two]
  ring

theorem reciprocal_source_green_cell (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (n k : ℕ) (positive : 0 < n)
    {a b : ℝ} (lower : (1 / 4 : ℝ) ≤ a) (ordered : a ≤ b) :
    4 * (∫ t : ℝ in a..b, source.1 t * reciprocalSampleWave coordinate.value n k t) =
      reciprocalGreenCurrent coordinate source n k b -
        reciprocalGreenCurrent coordinate source n k a -
          (2 * coordinate.value - 1) * (∫ t : ℝ in a..b,
            secondCoefficient coordinate source t / (t : ℂ)) := by
  have inRange (t : ℝ) (ht : t ∈ Icc a b) : (1 / 4 : ℝ) ≤ t := lower.trans ht.1
  have wave : ContinuousOn (reciprocalSampleWave coordinate.value n k) (Icc a b) :=
    fun t ht => (reciprocal_sample_derivative coordinate n k positive
      (lt_of_lt_of_le (by norm_num) (inRange t ht))).continuousAt.continuousWithinAt
  have coefficient : ContinuousOn (secondCoefficient coordinate source) (Icc a b) :=
    fun t ht => (secondCoefficient_derivative coordinate source (inRange t ht)).continuousAt.continuousWithinAt
  have sampled : IntervalIntegrable
      (fun t : ℝ => source.1 t * reciprocalSampleWave coordinate.value n k t) volume a b :=
    (source.1.continuous.continuousOn.mul wave).intervalIntegrable_of_Icc ordered
  have primitive : IntervalIntegrable
      (fun t : ℝ => secondCoefficient coordinate source t / (t : ℂ)) volume a b :=
    (coefficient.div Complex.continuous_ofReal.continuousOn
      (fun t ht => Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_of_lt_of_le (by norm_num) (inRange t ht))))).intervalIntegrable_of_Icc ordered
  have derivative (t : ℝ) (ht : t ∈ uIcc a b) :=
    reciprocalGreenCurrent_derivative coordinate source n k positive
      (inRange t (by simpa only [uIcc_of_le ordered] using ht))
  have current := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative
    (by simpa only [mul_assoc, mul_div_assoc] using
      (sampled.const_mul 4).add (primitive.const_mul (2 * coordinate.value - 1)))
  have split : (∫ t : ℝ in a..b,
      4 * (source.1 t * reciprocalSampleWave coordinate.value n k t) +
        (2 * coordinate.value - 1) * (secondCoefficient coordinate source t / (t : ℂ))) =
      (∫ t : ℝ in a..b, 4 * (source.1 t * reciprocalSampleWave coordinate.value n k t)) +
        (∫ t : ℝ in a..b, (2 * coordinate.value - 1) *
          (secondCoefficient coordinate source t / (t : ℂ))) :=
    intervalIntegral.integral_add (sampled.const_mul 4)
      (primitive.const_mul (2 * coordinate.value - 1))
  simp only [mul_assoc, mul_div_assoc] at current
  rw [split, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at current
  linear_combination current

theorem reciprocalGreenCurrent_outer (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (n k : ℕ) :
    reciprocalGreenCurrent coordinate source n k 4 = 0 := by
  simp only [reciprocalGreenCurrent, secondFlux_outer, secondCoefficient_outer,
    zero_mul, sub_self]

theorem reciprocalGreenCurrent_contact (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (n k : ℕ) (positive : 0 < n) :
    reciprocalGreenCurrent coordinate source n (k + 1) ((n : ℝ) / (k + 1 : ℝ)) -
      reciprocalGreenCurrent coordinate source n k ((n : ℝ) / (k + 1 : ℝ)) =
        (2 * coordinate.value - 1) *
          secondCoefficient coordinate source ((n : ℝ) / (k + 1 : ℝ)) / (k + 1 : ℂ) := by
  have nn : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positive
  have point : (n : ℝ) / ((n : ℝ) / (k + 1 : ℝ)) = k + 1 := by
    field_simp
  have wave : reciprocalSampleWave coordinate.value n (k + 1) ((n : ℝ) / (k + 1 : ℝ)) =
      reciprocalSampleWave coordinate.value n k ((n : ℝ) / (k + 1 : ℝ)) := by
    simp only [reciprocalSampleWave, point, OriginalPaGreenContact.cell_wave_at_contact]
  unfold reciprocalGreenCurrent
  rw [wave]
  have flux := reciprocal_sample_flux_contact coordinate.value n k positive
  linear_combination
    secondCoefficient coordinate source ((n : ℝ) / (k + 1 : ℝ)) * flux

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
