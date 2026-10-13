import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.InverseTail
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FiniteForcing
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.InverseSummation

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource InverseAction InverseTail
open OriginalRieszFinitePairing.CoPoisson.Ward

noncomputable section

local instance : CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete

/-- The actual original restriction and mean projection, as a continuous map. -/
def quarterCentered : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  Constructor.zeroMean.comp burnolQuarterRestriction

theorem projected_channel (scale : ℝ) (state : BurnolQuarterMeanZeroCarrier) :
    quarterCentered (ContinuousChannels.channel (-1) scale
      (burnolQuarterZeroExtension (state : BurnolQuarterIntervalL2))) = centeredCounting scale state := by
  simp only [quarterCentered, ContinuousLinearMap.comp_apply, ContinuousChannels.channel,
    neg_one_mul, map_smul, centeredCounting, countingWindow]

theorem projected_integer_channel (n : ℕ) (state : BurnolQuarterMeanZeroCarrier) :
    quarterCentered (Channels.sourceChannel n
      (burnolQuarterZeroExtension (state : BurnolQuarterIntervalL2))) = centeredCounting (n : ℝ) state := by
  simp only [quarterCentered, ContinuousLinearMap.comp_apply, Channels.sourceChannel,
    map_smul, centeredCounting, countingWindow]

theorem centeredCounting_continuousOn (state : BurnolQuarterMeanZeroCarrier) :
    ContinuousOn (fun scale : ℝ => centeredCounting scale state) (Ioi 0) := by
  have regular : ContinuousOn (fun scale : ℝ => ContinuousChannels.channel (-1) scale
      (burnolQuarterZeroExtension (state : BurnolQuarterIntervalL2))) (Ioi 0) := by
    unfold ContinuousChannels.channel
    apply ((Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn.inv₀
      (fun scale positive => Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr positive).ne')).smul
    exact (burnolMultiplicativeDilation_stronglyContinuous _).comp_continuousOn
      ((Real.continuousOn_log.mono (fun _ positive => ne_of_gt positive)).const_mul (-1))
  simpa only [Function.comp_def, projected_channel] using! quarterCentered.continuous.comp_continuousOn regular

/-- The local integral is paid on the original full L² source before restriction. -/
theorem centeredCounting_integrable_local (upper : ℝ) (state : BurnolQuarterMeanZeroCarrier) :
    IntegrableOn (fun scale : ℝ => centeredCounting scale state) (Ioc 0 upper) := by
  have original := ContinuousChannels.channel_integrable (-1) upper
    (burnolQuarterZeroExtension (state : BurnolQuarterIntervalL2))
  simpa only [projected_channel] using! quarterCentered.integrable_comp original

theorem smooth_inverse_integrable_tail (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun scale : ℝ => centeredCounting scale (burnolMeanZeroTruncatedFourier
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)))) (Ioi 1) := by
  have powers : IntegrableOn (fun scale : ℝ => scale⁻¹ ^ 3) (Ioi 1) := by
    simpa only [show (-3 : ℝ) = -(3 : ℕ) by norm_num,
      Real.rpow_neg_natCast, zpow_neg, zpow_natCast, inv_pow] using!
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1))
  apply (powers.const_mul (2 * returnMass coordinate)).mono'
    (((centeredCounting_continuousOn _).mono (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).aestronglyMeasurable
      measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with scale large
  exact original_inverse_counting_norm_bound coordinate scale large.le

theorem smooth_inverse_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun scale : ℝ => centeredCounting scale (burnolMeanZeroTruncatedFourier
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)))) (Ioi 0) := by
  have actual := (centeredCounting_integrable_local 1
    (burnolMeanZeroTruncatedFourier
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)))).union
        (smooth_inverse_integrable_tail coordinate)
  rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at actual

/-- Each cutoff uses exactly the same integer N for the discrete and continuous source. -/
theorem finite_source_projection (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    quarterCentered (FiniteForcing.source N (burnolQuarterZeroExtension
      (burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier
        (burnolRieszSingleFourierSource coordinate)) : BurnolQuarterIntervalL2))) =
      (∑ n ∈ Finset.Ico 1 N, centeredCounting (n : ℝ) (burnolMeanZeroTruncatedFourier
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)))) -
      ∫ scale : ℝ in Ioc 0 (N : ℝ), centeredCounting scale (burnolMeanZeroTruncatedFourier
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate))) := by
  unfold FiniteForcing.source ContinuousChannels.normalization
  rw [map_sub, map_sum, ← quarterCentered.integral_comp_comm
    (ContinuousChannels.channel_integrable (-1) (N : ℝ) _)]
  simp only [projected_integer_channel, projected_channel]

theorem smooth_inverse_sum_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N, centeredCounting (n : ℝ)
      (burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier
        (burnolRieszSingleFourierSource coordinate)))) atTop
      (𝓝 (∑' n : ℕ, centeredCounting (n : ℝ) (burnolMeanZeroTruncatedFourier
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate))))) := by
  have actual := (original_inverse_counting_summable coordinate).hasSum.tendsto_sum_nat
  apply actual.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N large
  rw [Finset.sum_Ico_eq_sub _ large]
  simp [centeredCounting, countingWindow]

theorem smooth_inverse_integral_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => ∫ scale : ℝ in Ioc 0 (N : ℝ), centeredCounting scale
      (burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier
        (burnolRieszSingleFourierSource coordinate)))) atTop
      (𝓝 (∫ scale : ℝ in Ioi 0, centeredCounting scale (burnolMeanZeroTruncatedFourier
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate))))) := by
  have actual := intervalIntegral_tendsto_integral_Ioi 0 (smooth_inverse_integrable coordinate)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply actual.congr'
  filter_upwards with N
  exact intervalIntegral.integral_of_le (Nat.cast_nonneg N)

/-- Strong L² convergence belongs to the original smooth inverse return.
The full b and its explicit forcing are kept out of this tail-only claim. -/
theorem smooth_inverse_finite_source_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => quarterCentered (FiniteForcing.source N (burnolQuarterZeroExtension
      (burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier
        (burnolRieszSingleFourierSource coordinate)) : BurnolQuarterIntervalL2)))) atTop
      (𝓝 ((∑' n : ℕ, centeredCounting (n : ℝ) (burnolMeanZeroTruncatedFourier
          (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)))) -
        ∫ scale : ℝ in Ioi 0, centeredCounting scale (burnolMeanZeroTruncatedFourier
          (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate))))) := by
  simp_rw [finite_source_projection]
  exact (smooth_inverse_sum_tendsto coordinate).sub (smooth_inverse_integral_tendsto coordinate)

end
end OriginalRieszFinitePairing.CoPoisson.Ward.InverseSummation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
