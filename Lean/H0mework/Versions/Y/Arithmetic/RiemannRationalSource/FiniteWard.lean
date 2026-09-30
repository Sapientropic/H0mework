import H0mework.Versions.Y.Arithmetic.RiemannRationalSource.SourceCurrent
import H0mework.Versions.Y.Arithmetic.RiemannRationalSource.Grid

/-! Every contact in one complete original reciprocal sampling channel is retained. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def sourceReciprocalCellIntegral (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (n j : ℕ) : ℂ :=
  ∫ t : ℝ in reciprocalSampleGrid n (j + 1)..reciprocalSampleGrid n j,
    source.1 t * reciprocalSampleWave coordinate.value n (n / 4 + j) t

private theorem primitive_intervalIntegrable (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) {a b : ℝ}
    (lower : (1 / 4 : ℝ) ≤ a) (ordered : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => secondCoefficient coordinate source t / (t : ℂ))
      volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc ordered
  apply ContinuousOn.div _ Complex.continuous_ofReal.continuousOn
  · intro t ht
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by norm_num) (lower.trans ht.1)))
  · intro t ht
    exact (secondCoefficient_derivative coordinate source
      (lower.trans ht.1)).continuousAt.continuousWithinAt

theorem source_green_grid_contact (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (n j : ℕ) (positive : 0 < n) :
    reciprocalGreenCurrent coordinate source n (n / 4 + (j + 1))
        (reciprocalSampleGrid n (j + 1)) -
      reciprocalGreenCurrent coordinate source n (n / 4 + j)
        (reciprocalSampleGrid n (j + 1)) =
      (2 * coordinate.value - 1) *
        (secondCoefficient coordinate source (reciprocalSampleGrid n (j + 1)) /
          ((n / 4 + j + 1 : ℕ) : ℂ)) := by
  simpa only [reciprocal_sample_grid_succ, Nat.add_assoc, Nat.cast_add, add_assoc,
    Nat.cast_one, mul_div_assoc] using
    reciprocalGreenCurrent_contact coordinate source n (n / 4 + j) positive

theorem source_reciprocal_ward_prefix (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (n : ℕ) (positive : 0 < n)
    (m : ℕ) (bounded : m < reciprocalSampleGridLength n) :
    4 * (∑ j ∈ Finset.range (m + 1), sourceReciprocalCellIntegral coordinate source n j) =
      -reciprocalGreenCurrent coordinate source n (n / 4 + m)
        (reciprocalSampleGrid n (m + 1)) +
      (2 * coordinate.value - 1) * (∑ j ∈ Finset.range m,
        secondCoefficient coordinate source (reciprocalSampleGrid n (j + 1)) /
          ((n / 4 + j + 1 : ℕ) : ℂ)) -
      (2 * coordinate.value - 1) * (∫ t : ℝ in reciprocalSampleGrid n (m + 1)..4,
        secondCoefficient coordinate source t / (t : ℂ)) := by
  induction m with
  | zero =>
    have cell := reciprocal_source_green_cell coordinate source n (n / 4) positive
      (reciprocal_sample_grid_bounds n positive (Nat.succ_le_of_lt bounded)).1
      (reciprocal_sample_grid_antitone_step n positive bounded)
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero,
      sourceReciprocalCellIntegral, reciprocal_sample_grid_zero, reciprocalGreenCurrent_outer,
      zero_sub, mul_zero, add_zero] using cell
  | succ m ih =>
    have previous := ih (by omega)
    have next := reciprocal_source_green_cell coordinate source n (n / 4 + (m + 1)) positive
      (reciprocal_sample_grid_bounds n positive (Nat.succ_le_of_lt bounded)).1
      (reciprocal_sample_grid_antitone_step n positive bounded)
    have contact := source_green_grid_contact coordinate source n m positive
    have intervals := intervalIntegral.integral_add_adjacent_intervals
      (primitive_intervalIntegrable coordinate source
        (reciprocal_sample_grid_bounds n positive (Nat.succ_le_of_lt bounded)).1
        (reciprocal_sample_grid_antitone_step n positive bounded))
      (primitive_intervalIntegrable coordinate source
        (reciprocal_sample_grid_bounds n positive (by omega : m + 1 ≤ reciprocalSampleGridLength n)).1
        (reciprocal_sample_grid_bounds n positive (by omega : m + 1 ≤ reciprocalSampleGridLength n)).2)
    change 4 * sourceReciprocalCellIntegral coordinate source n (m + 1) = _ at next
    simp only [Finset.sum_range_succ] at previous ⊢
    linear_combination previous + next + contact - (2 * coordinate.value - 1) * intervals

theorem source_reciprocal_finite_ward (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (n : ℕ) (positive : 0 < n) :
    4 * (∑ j ∈ Finset.range (reciprocalSampleGridLength n),
      sourceReciprocalCellIntegral coordinate source n j) =
      -reciprocalGreenCurrent coordinate source n (4 * n - 1) (1 / 4) +
      (2 * coordinate.value - 1) * (∑ j ∈ Finset.range (reciprocalSampleGridLength n - 1),
        secondCoefficient coordinate source (reciprocalSampleGrid n (j + 1)) /
          ((n / 4 + j + 1 : ℕ) : ℂ)) -
      (2 * coordinate.value - 1) * (∫ t : ℝ in (1 / 4)..4,
        secondCoefficient coordinate source t / (t : ℂ)) := by
  have lengthPositive := reciprocal_sample_grid_length_pos n positive
  have last : reciprocalSampleGridLength n - 1 + 1 = reciprocalSampleGridLength n := by omega
  have generated := source_reciprocal_ward_prefix coordinate source n positive
    (reciprocalSampleGridLength n - 1) (by omega)
  have index : n / 4 + (reciprocalSampleGridLength n - 1) = 4 * n - 1 := by
    dsimp only [reciprocalSampleGridLength]
    omega
  rw [last, reciprocal_sample_grid_last n positive, index] at generated
  exact generated

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
