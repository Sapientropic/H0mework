import H0mework.Versions.Y.Arithmetic.RiemannRationalSource.FiniteWard
import H0mework.Versions.Y.Arithmetic.RiemannRationalSource.ActualSampling

/-! The complete finite rational Ward is a read of the original W sampler. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def sourceReciprocalContactLoad (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (n : ℕ) : ℂ :=
  -reciprocalGreenCurrent coordinate source n (4 * n - 1) (1 / 4) +
    (2 * coordinate.value - 1) * (∑ j ∈ Finset.range (reciprocalSampleGridLength n - 1),
      secondCoefficient coordinate source (reciprocalSampleGrid n (j + 1)) /
        ((n / 4 + j + 1 : ℕ) : ℂ)) -
    (2 * coordinate.value - 1) * (∫ t : ℝ in (1 / 4)..4,
      secondCoefficient coordinate source t / (t : ℂ))

private theorem source_reciprocal_grid_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (n : ℕ) (positive : 0 < n)
    {j : ℕ} (bounded : j < reciprocalSampleGridLength n) :
    IntervalIntegrable (fun t : ℝ => source.1 t *
      originalReciprocalSampleWave coordinate.value n t) volume
      (reciprocalSampleGrid n (j + 1)) (reciprocalSampleGrid n j) := by
  have ordered := reciprocal_sample_grid_antitone_step n positive bounded
  have lower := (reciprocal_sample_grid_bounds n positive (Nat.succ_le_of_lt bounded)).1
  have regular : ContinuousOn (fun t : ℝ => source.1 t *
      reciprocalSampleWave coordinate.value n (n / 4 + j) t)
      (Icc (reciprocalSampleGrid n (j + 1)) (reciprocalSampleGrid n j)) := by
    apply source.1.continuous.continuousOn.mul
    intro t ht
    exact (reciprocal_sample_derivative coordinate n (n / 4 + j) positive
      (lt_of_lt_of_le (by norm_num) (lower.trans ht.1))).continuousAt.continuousWithinAt
  apply (regular.intervalIntegrable_of_Icc ordered).congr_uIoo
  intro t ht
  have inside : t ∈ Ioo (reciprocalSampleGrid n (j + 1)) (reciprocalSampleGrid n j) := by
    simpa only [uIoo_of_le ordered] using ht
  exact congrArg (fun x : ℂ => source.1 t * x)
    (reciprocal_sample_grid_raw_read coordinate.value n positive bounded inside).symm

theorem source_reciprocal_original_finite_ward (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (n : ℕ) (positive : 0 < n) :
    4 * (∫ t : ℝ in (1 / 4)..4,
      source.1 t * originalReciprocalSampleWave coordinate.value n t) =
        sourceReciprocalContactLoad coordinate source n := by
  have sampled (j : ℕ) (hj : j < reciprocalSampleGridLength n) :
      sourceReciprocalCellIntegral coordinate source n j =
        ∫ t : ℝ in reciprocalSampleGrid n (j + 1)..reciprocalSampleGrid n j,
          source.1 t * originalReciprocalSampleWave coordinate.value n t := by
    apply intervalIntegral.integral_congr_Ioo_of_le
      (reciprocal_sample_grid_antitone_step n positive hj)
    intro t ht
    exact congrArg (fun x : ℂ => source.1 t * x)
      (reciprocal_sample_grid_raw_read coordinate.value n positive hj ht).symm
  have partition := intervalIntegral.sum_integral_adjacent_intervals
    (fun j hj => (source_reciprocal_grid_integrable coordinate source n positive hj).symm)
  rw [reciprocal_sample_grid_zero, reciprocal_sample_grid_last n positive] at partition
  have joined : (∑ j ∈ Finset.range (reciprocalSampleGridLength n),
      sourceReciprocalCellIntegral coordinate source n j) =
      ∫ t : ℝ in (1 / 4)..4,
        source.1 t * originalReciprocalSampleWave coordinate.value n t := by
    calc
      _ = -(∑ j ∈ Finset.range (reciprocalSampleGridLength n),
          ∫ t : ℝ in reciprocalSampleGrid n j..reciprocalSampleGrid n (j + 1),
            source.1 t * originalReciprocalSampleWave coordinate.value n t) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [sampled j (Finset.mem_range.mp hj), intervalIntegral.integral_symm]
      _ = _ := by rw [partition, intervalIntegral.integral_symm, neg_neg]
  have generated := source_reciprocal_finite_ward coordinate source n positive
  rw [joined] at generated
  exact generated

theorem original_W_sampling_ward {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (n : ℕ) :
    let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    4 * (∫ t : ℝ in (1 / 4)..4, source.1 t *
      burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n) t) =
        sourceReciprocalContactLoad coordinate source (n + 1) := by
  intro coordinate one W
  have actual := (ae_restrict_iff' measurableSet_Ioo).mp
    (original_reciprocal_sample_coeFn observation nontrivial rightHalf n)
  have same : (∫ t : ℝ in (1 / 4)..4, source.1 t *
      burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n) t) =
      ∫ t : ℝ in (1 / 4)..4, source.1 t *
        originalReciprocalSampleWave observation.coordinate (n + 1) t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [actual, volume.ae_ne (4 : ℝ)] with t read different ht
    have inside : t ∈ Ioc (1 / 4 : ℝ) 4 := by
      simpa only [uIoc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 4)] using ht
    exact congrArg (fun x : ℂ => source.1 t * x)
      (read ⟨inside.1, lt_of_le_of_ne inside.2 different⟩)
  rw [same]
  exact source_reciprocal_original_finite_ward coordinate source (n + 1) (by omega)

theorem original_W_finite_sampling_ward {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (N : ℕ) :
    let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    4 * (∫ t : ℝ in (1 / 4)..4, source.1 t *
      ∑ n ∈ Finset.range N, burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n) t) =
        ∑ n ∈ Finset.range N, sourceReciprocalContactLoad coordinate source (n + 1) := by
  intro coordinate one W
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro n _
    exact original_W_sampling_ward observation nontrivial rightHalf source n
  · intro n _
    exact ((source.1.memLp 2 volume).integrable_mul
      (Lp.memLp (burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n)))).intervalIntegrable

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
