import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ReturnConstantTail

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction

/-- The complete first reverse source pays the fixed exterior tail, including its normalization. -/
def outside : BurnolL2 := DualSource.source 1 ConstantDual.seed + ConstantDual.seed

def outsideRaw (x : ℝ) : ℂ := if q < |x| then -((q / |x| : ℝ) : ℂ) else 0

theorem outside_coeFn : (outside : ℝ → ℂ) =ᵐ[volume] outsideRaw := by
  filter_upwards [Lp.coeFn_add (DualSource.source 1 ConstantDual.seed) ConstantDual.seed,
    ConstantDual.finite_coeFn 1, ConstantDual.seed_coeFn, volume.ae_ne (0 : ℝ)]
      with x added finite seed nonzero
  rw [outside, added, Pi.add_apply, finite, seed]
  by_cases large : q < |x|
  · have ratio : q / |x| < (1 : ℝ) := (div_lt_one (abs_pos.mpr nonzero)).mpr large
    rw [ConstantDual.finite_stabilizes 1 x (by simpa using ratio),
      ConstantDual.sawtooth_tail x large, ConstantDual.seedRaw,
      if_neg large.not_ge, outsideRaw, if_pos large, add_zero]
  · have small := le_of_not_gt large
    have ratio : (1 : ℝ) ≤ q / |x| := (le_div_iff₀ (abs_pos.mpr nonzero)).mpr (by simpa using small)
    rw [ConstantDual.finite_clipped 1 (by decide) x (by simpa using ratio),
      ConstantDual.seedRaw, if_pos small, outsideRaw, if_neg large]
    ring

private theorem cutoff_read (value : BurnolL2) :
    (E (R value) : ℝ → ℂ) =ᵐ[volume] (symmetricInterval q).indicator (value : ℝ → ℂ) := by
  have restriction := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value)
  filter_upwards [burnolQuarterZeroExtension_coe (R value), restriction] with x extension restricted
  rw [extension]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside]
    exact restricted inside
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]

/-- Every positive finite program has exactly the same exterior source. -/
theorem finite_split (N : ℕ) (positive : 0 < N) :
    DualSource.source N ConstantDual.seed = E (R (DualSource.source N ConstantDual.seed)) + outside := by
  apply Lp.ext
  filter_upwards [ConstantDual.finite_coeFn N, cutoff_read (DualSource.source N ConstantDual.seed),
    outside_coeFn, Lp.coeFn_add (E (R (DualSource.source N ConstantDual.seed))) outside]
      with x finite cutoff tail added
  rw [added, Pi.add_apply, cutoff, tail]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, outsideRaw, if_neg (not_lt.mpr (abs_le.mpr inside)), add_zero]
  · have large : q < |x| := lt_of_not_ge (fun h => inside (abs_le.mp h))
    have ratio : q / |x| < (N : ℝ) :=
      ((div_lt_one (lt_trans (by norm_num : (0 : ℝ) < q) large)).mpr large).trans_le
        (by exact_mod_cast positive)
    rw [indicator_of_notMem inside, zero_add, finite,
      ConstantDual.finite_stabilizes N x ratio, ConstantDual.sawtooth_tail x large,
      outsideRaw, if_pos large]

theorem value_split : ConstantDual.value = E (R ConstantDual.value) + outside := by
  have same := ConstantDual.original_tendsto.congr' (show
      (fun N : ℕ => DualSource.source N ConstantDual.seed) =ᶠ[atTop]
        (fun N : ℕ => E (R (DualSource.source N ConstantDual.seed)) + outside) from by
    filter_upwards [eventually_ge_atTop 1] with N positive
    exact finite_split N positive)
  have target := (((burnolQuarterZeroExtension.continuous.tendsto _).comp
    (burnolQuarterRestriction.continuous.tendsto _)).comp
    ConstantDual.original_tendsto).add_const outside
  exact tendsto_nhds_unique same target

theorem outside_even : reflectL2 outside = outside := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving outside negMeasurePreserving,
    outside_coeFn, negMeasurePreserving.quasiMeasurePreserving.ae outside_coeFn]
      with x reflected positive negative
  rw [show reflectL2 outside x = outside (-x) from reflected, negative, positive]
  simp only [outsideRaw, abs_neg]

private theorem fourier_outside_pair (value : BurnolL2) :
    inner ℂ (fourierL2 value) outside = inner ℂ value (fourierL2 outside) := by
  have actual := fourierL2.inner_map_map value (fourierL2 outside)
  rwa [fourierL2_fourierL2, outside_even] at actual

private theorem return_split (coordinate : BurnolCompletedMellinCoordinate) :
    (Constructor.returnState coordinate : BurnolQuarterIntervalL2) =
      burnolTruncatedFourier (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) -
        burnolQuarterMeanCoefficient (burnolTruncatedFourier
          (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) • intervalConstant q := by
  rw [Constructor.returnState, burnolMeanZeroTruncatedFourier_coe,
    burnolMeanZeroProjection_eq_sub_constant]

private theorem return_pair (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (E (Constructor.returnState coordinate : BurnolQuarterIntervalL2)) value -
        inner ℂ (fourierL2 (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) value =
      -star (burnolQuarterMeanCoefficient (burnolTruncatedFourier
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) *
          inner ℂ ConstantDual.seed value -
        inner ℂ (fourierL2 (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)))
          (value - E (R value)) := by
  have returned := ContinuousLinearMap.adjoint_inner_left R value
    (Constructor.returnState coordinate : BurnolQuarterIntervalL2)
  have constant := ContinuousLinearMap.adjoint_inner_left R value (intervalConstant q)
  have fourier := ContinuousLinearMap.adjoint_inner_right R
    (fourierL2 (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) (R value)
  change inner ℂ (E (Constructor.returnState coordinate : BurnolQuarterIntervalL2)) value = _ at returned
  change inner ℂ ConstantDual.seed value = _ at constant
  change inner ℂ (fourierL2 (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) (E (R value)) =
    inner ℂ (burnolTruncatedFourier (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) (R value) at fourier
  rw [returned, return_split, inner_sub_left, inner_smul_left, constant, inner_sub_right, fourier]
  simp only [starRingEnd_apply]
  ring

/-- The same finite source cancels the entire inner return/Fourier contact; its mean and exterior survive. -/
theorem finite_pair (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    inner ℂ (E (Constructor.returnState coordinate : BurnolQuarterIntervalL2))
        (DualSource.source N ConstantDual.seed) -
      inner ℂ (fourierL2 (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)))
        (DualSource.source N ConstantDual.seed) =
      -star (burnolQuarterMeanCoefficient (burnolTruncatedFourier
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) *
          inner ℂ ConstantDual.seed (DualSource.source N ConstantDual.seed) -
        inner ℂ (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) (fourierL2 outside) := by
  rw [return_pair]
  have tail : DualSource.source N ConstantDual.seed - E (R (DualSource.source N ConstantDual.seed)) = outside := by
    exact sub_eq_iff_eq_add.mpr ((finite_split N positive).trans (add_comm _ _))
  rw [tail, fourier_outside_pair]

theorem original_pair (coordinate : BurnolCompletedMellinCoordinate) :
    inner ℂ (E (Constructor.returnState coordinate : BurnolQuarterIntervalL2)) ConstantDual.value -
      inner ℂ (fourierL2 (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) ConstantDual.value =
      -star (burnolQuarterMeanCoefficient (burnolTruncatedFourier
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) *
          inner ℂ ConstantDual.seed ConstantDual.value -
        inner ℂ (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) (fourierL2 outside) := by
  rw [return_pair]
  have tail : ConstantDual.value - E (R ConstantDual.value) = outside := by
    exact sub_eq_iff_eq_add.mpr (value_split.trans (add_comm _ _))
  rw [tail, fourier_outside_pair]

/-- The original gap and Fourier means combine into the original position mean. -/
theorem original_mean_pair (coordinate : BurnolCompletedMellinCoordinate) :
    star (GapEuler.gapMean q coordinate) * inner ℂ ConstantDual.seed ConstantDual.value +
      inner ℂ (E (Constructor.returnState coordinate : BurnolQuarterIntervalL2)) ConstantDual.value -
        inner ℂ (fourierL2 (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) ConstantDual.value =
      star (positionMean coordinate) * inner ℂ ConstantDual.seed ConstantDual.value -
        inner ℂ (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) (fourierL2 outside) := by
  have actual := original_pair coordinate
  rw [positionMean_eq, star_sub]
  linear_combination actual

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ReturnConstantTail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
