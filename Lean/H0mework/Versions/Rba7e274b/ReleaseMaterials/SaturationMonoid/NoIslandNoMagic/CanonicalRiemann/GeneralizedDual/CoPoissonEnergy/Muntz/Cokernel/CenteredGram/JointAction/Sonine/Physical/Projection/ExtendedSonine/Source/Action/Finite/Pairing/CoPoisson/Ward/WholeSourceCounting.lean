import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ForcingTail
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SingularCounting
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.InverseSummation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.WholeSourceCounting

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalRieszSource.Translator
open OriginalRieszFinitePairing.CoPoisson.Ward.InverseAction OriginalRieszFinitePairing.CoPoisson.Ward.InverseSummation

noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

local instance : CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete

/-- These existing projected-source mouths use literally the same restriction
and original mean-zero projection. -/
theorem projectedSource_eq_quarterCentered (N : ℕ) (state : BurnolQuarterMeanZeroCarrier) :
    SingularCounting.projectedSource N state =
      quarterCentered (FiniteForcing.source N (burnolQuarterZeroExtension
        (state : BurnolQuarterIntervalL2))) := rfl

private theorem secondReturn_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    Constructor.secondReturnRaw coordinate (-x) = Constructor.secondReturnRaw coordinate x := by
  unfold Constructor.secondReturnRaw burnolMeanZeroFourierRaw
  rw [OriginalRieszFinitePairing.return_fourier_even]

theorem original_raw_decomposition (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (nonzero : x ≠ 0) :
    burnolRieszSingleFourierSourceRaw coordinate x =
      ForcingPrimitive.leadingCoefficient coordinate * SingularCounting.powerRaw coordinate x +
        ForcingTail.forcingRemainder coordinate x - ForcingMeanZero.mean coordinate +
          Constructor.secondReturnRaw coordinate x := by
  have generated := ForcingTail.original_source_read coordinate |x| (abs_pos.mpr nonzero)
  have sourceAbs : burnolRieszSingleFourierSourceRaw coordinate |x| =
      burnolRieszSingleFourierSourceRaw coordinate x := by
    rcases le_total 0 x with positive | negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative, OriginalRieszFinitePairing.source_raw_even]
  have returnAbs : Constructor.secondReturnRaw coordinate |x| = Constructor.secondReturnRaw coordinate x := by
    rcases le_total 0 x with positive | negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative, secondReturn_even]
  have remainderAbs : ForcingTail.forcingRemainder coordinate |x| =
      ForcingTail.forcingRemainder coordinate x := by
    simp only [ForcingTail.forcingRemainder, ForcingTail.edgeRemainder, abs_abs]
  rw [sourceAbs, returnAbs, remainderAbs] at generated
  exact generated

private theorem original_interval_decomposition (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) =
      ForcingPrimitive.leadingCoefficient coordinate • SingularCounting.powerL2 coordinate +
        ForcingTail.forcingRemainderState coordinate -
          ForcingMeanZero.mean coordinate • intervalConstant q +
      (burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier
        (burnolRieszSingleFourierSource coordinate)) : BurnolQuarterIntervalL2) := by
  let power := ForcingPrimitive.leadingCoefficient coordinate • SingularCounting.powerL2 coordinate
  let remainder := ForcingTail.forcingRemainderState coordinate
  let mean := ForcingMeanZero.mean coordinate • intervalConstant q
  let second : BurnolQuarterIntervalL2 := burnolMeanZeroTruncatedFourier
    (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate))
  apply Lp.ext
  filter_upwards [burnolRieszSingleFourierSource_ae_raw coordinate,
    Lp.coeFn_add (power + remainder - mean) second,
    Lp.coeFn_sub (power + remainder) mean, Lp.coeFn_add power remainder,
    Lp.coeFn_smul (ForcingPrimitive.leadingCoefficient coordinate) (SingularCounting.powerL2 coordinate),
    Lp.coeFn_smul (ForcingMeanZero.mean coordinate) (intervalConstant q),
    SingularCounting.power_coeFn coordinate, ForcingTail.forcingRemainderState_ae_raw coordinate,
    Constructor.secondReturnRaw_read coordinate, intervalConstant_coeFn q,
    ae_restrict_of_ae (s := symmetricInterval q) (volume.ae_ne (0 : ℝ))]
      with x source fullAdd subAt addAt powerSmul meanSmul powerRaw remainderRaw secondRaw constant nonzero
  change _ = (power + remainder - mean + second : BurnolQuarterIntervalL2) x
  rw [source, fullAdd]
  change _ = (power + remainder - mean : BurnolQuarterIntervalL2) x + second x
  rw [subAt]
  change _ = (power + remainder : BurnolQuarterIntervalL2) x - mean x + second x
  rw [addAt]
  change _ = power x + remainder x - mean x + second x
  rw [powerSmul, meanSmul]
  change _ = ForcingPrimitive.leadingCoefficient coordinate * SingularCounting.powerL2 coordinate x +
    remainder x - ForcingMeanZero.mean coordinate * intervalConstant q x + second x
  change second x = Constructor.secondReturnRaw coordinate x at secondRaw
  rw [powerRaw, remainderRaw, secondRaw, constant, mul_one]
  exact original_raw_decomposition coordinate x nonzero

private theorem zeroMean_fixed (state : BurnolQuarterMeanZeroCarrier) :
    Constructor.zeroMean (state : BurnolQuarterIntervalL2) = state := by
  apply Subtype.ext
  rw [Constructor.zeroMean_read, Constructor.mean_zero, zero_smul, sub_zero]

/-- The original b itself is reconstructed in L²; its original constant mean
is removed by the same actual mean-zero projection applied to every term. -/
theorem original_b_decomposition (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRieszSingleFourierSource coordinate =
      ForcingPrimitive.leadingCoefficient coordinate • SingularCounting.centeredPower coordinate +
        ForcingTail.meanZeroRemainder coordinate +
      burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier
        (burnolRieszSingleFourierSource coordinate)) := by
  have generated := congrArg Constructor.zeroMean (original_interval_decomposition coordinate)
  simpa only [map_add, map_sub, map_smul, Constructor.zeroMean_constant, smul_zero, sub_zero,
    zeroMean_fixed, SingularCounting.centeredPower, ForcingTail.meanZeroRemainder] using generated

/-- The actual unprojected source equation also computes its original mean.
This identity alone does not erase the subsequent small-scale window contacts. -/
theorem original_mean_balance (coordinate : BurnolCompletedMellinCoordinate) :
    ForcingMeanZero.mean coordinate =
      ForcingPrimitive.leadingCoefficient coordinate * burnolQuarterMeanCoefficient (SingularCounting.powerL2 coordinate) +
        burnolQuarterMeanCoefficient (ForcingTail.forcingRemainderState coordinate) := by
  have oneMean : burnolQuarterMeanCoefficient (intervalConstant q) = 1 := by
    rw [Constructor.mean_integral, integral_congr_ae (intervalConstant_coeFn q), integral_const,
      burnolRadiusInterval_measureReal_univ (by norm_num : (0 : ℝ) < q), Complex.real_smul]
    norm_num
  have balance := congrArg burnolQuarterMeanCoefficient (original_interval_decomposition coordinate)
  simp only [burnolQuarterMeanCoefficient, inner_add_right, inner_sub_right,
    inner_smul_right, add_div, sub_div, mul_div_assoc] at balance
  change burnolQuarterMeanCoefficient (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) =
    ForcingPrimitive.leadingCoefficient coordinate * burnolQuarterMeanCoefficient (SingularCounting.powerL2 coordinate) +
      burnolQuarterMeanCoefficient (ForcingTail.forcingRemainderState coordinate) -
      ForcingMeanZero.mean coordinate * burnolQuarterMeanCoefficient (intervalConstant q) +
      burnolQuarterMeanCoefficient (burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier
        (burnolRieszSingleFourierSource coordinate)) : BurnolQuarterIntervalL2) at balance
  rw [Constructor.mean_zero, Constructor.mean_zero, oneMean, mul_one] at balance
  linear_combination balance

theorem remainder_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun scale : ℝ => centeredCounting scale (ForcingTail.meanZeroRemainder coordinate)) (Ioi 0) := by
  have powers : IntegrableOn (fun scale : ℝ => scale⁻¹ ^ 3) (Ioi 1) := by
    simpa only [show (-3 : ℝ) = -(3 : ℕ) by norm_num,
      Real.rpow_neg_natCast, zpow_neg, zpow_natCast, inv_pow] using!
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1))
  have tail : IntegrableOn (fun scale : ℝ => centeredCounting scale
      (ForcingTail.meanZeroRemainder coordinate)) (Ioi 1) := by
    apply (powers.const_mul (8 * ‖ForcingWhole.coefficient coordinate‖)).mono'
      (((centeredCounting_continuousOn _).mono (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).aestronglyMeasurable
        measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with scale large
    exact ForcingTail.input_counting_norm_bound coordinate scale large.le
  have full := (centeredCounting_integrable_local 1 (ForcingTail.meanZeroRemainder coordinate)).union tail
  rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at full

theorem projectedSource_as_counting (N : ℕ) (state : BurnolQuarterMeanZeroCarrier) :
    SingularCounting.projectedSource N state =
      (∑ n ∈ Finset.Ico 1 N, centeredCounting (n : ℝ) state) -
        ∫ scale : ℝ in Ioc 0 (N : ℝ), centeredCounting scale state := by
  rw [projectedSource_eq_quarterCentered]
  unfold FiniteForcing.source ContinuousChannels.normalization
  rw [map_sub, map_sum, ← quarterCentered.integral_comp_comm
    (ContinuousChannels.channel_integrable (-1) (N : ℝ) _)]
  simp only [projected_integer_channel, projected_channel]

private theorem counting_add (scale : ℝ) (left right : BurnolQuarterMeanZeroCarrier) :
    centeredCounting scale (left + right) = centeredCounting scale left + centeredCounting scale right := by
  simp only [centeredCounting, countingWindow, Submodule.coe_add, map_add, smul_add]

theorem projectedSource_add (N : ℕ) (left right : BurnolQuarterMeanZeroCarrier) :
    SingularCounting.projectedSource N (left + right) =
      SingularCounting.projectedSource N left + SingularCounting.projectedSource N right := by
  rw [projectedSource_as_counting, projectedSource_as_counting, projectedSource_as_counting]
  simp_rw [counting_add]
  rw [Finset.sum_add_distrib,
    integral_add (centeredCounting_integrable_local (N : ℝ) left)
      (centeredCounting_integrable_local (N : ℝ) right)]
  abel

theorem remainder_source_limit (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => SingularCounting.projectedSource N (ForcingTail.meanZeroRemainder coordinate)) atTop
      (𝓝 ((∑' n : ℕ, centeredCounting (n : ℝ) (ForcingTail.meanZeroRemainder coordinate)) -
        ∫ scale : ℝ in Ioi 0, centeredCounting scale (ForcingTail.meanZeroRemainder coordinate))) := by
  have integerLimit : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N,
      centeredCounting (n : ℝ) (ForcingTail.meanZeroRemainder coordinate)) atTop
      (𝓝 (∑' n : ℕ, centeredCounting (n : ℝ) (ForcingTail.meanZeroRemainder coordinate))) := by
    apply (ForcingTail.input_counting_summable coordinate).hasSum.tendsto_sum_nat.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N large
    rw [Finset.sum_Ico_eq_sub _ large]
    simp [centeredCounting, countingWindow]
  have continuousLimit : Tendsto (fun N : ℕ => ∫ scale : ℝ in Ioc 0 (N : ℝ),
      centeredCounting scale (ForcingTail.meanZeroRemainder coordinate)) atTop
      (𝓝 (∫ scale : ℝ in Ioi 0, centeredCounting scale (ForcingTail.meanZeroRemainder coordinate))) := by
    apply (intervalIntegral_tendsto_integral_Ioi 0 (remainder_integrable coordinate)
      (tendsto_natCast_atTop_atTop (R := ℝ))).congr'
    filter_upwards with N
    exact intervalIntegral.integral_of_le (Nat.cast_nonneg N)
  simp_rw [projectedSource_as_counting]
  exact integerLimit.sub continuousLimit

/-- The complete original mean-zero b is acted on by one actual same-N source,
and all three generated components retain their full strong limits. -/
theorem original_source_limit (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N : ℕ => SingularCounting.projectedSource N (burnolRieszSingleFourierSource coordinate)) atTop
      (𝓝 ((ForcingPrimitive.leadingCoefficient coordinate • SingularCounting.smallScaleResidual coordinate +
        ((∑' n : ℕ, centeredCounting (n : ℝ) (ForcingTail.meanZeroRemainder coordinate)) -
          ∫ scale : ℝ in Ioi 0, centeredCounting scale (ForcingTail.meanZeroRemainder coordinate))) +
        ((∑' n : ℕ, centeredCounting (n : ℝ) (burnolMeanZeroTruncatedFourier
            (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)))) -
          ∫ scale : ℝ in Ioi 0, centeredCounting scale (burnolMeanZeroTruncatedFourier
            (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)))))) := by
  have inverseLimit := smooth_inverse_finite_source_tendsto coordinate
  rw [show (fun N : ℕ => quarterCentered (FiniteForcing.source N (burnolQuarterZeroExtension
      (burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier
        (burnolRieszSingleFourierSource coordinate)) : BurnolQuarterIntervalL2)))) =
      (fun N : ℕ => SingularCounting.projectedSource N (burnolMeanZeroTruncatedFourier
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)))) from rfl] at inverseLimit
  have assembled := ((SingularCounting.original_singular_limit coordinate zero).add
    (remainder_source_limit coordinate)).add inverseLimit
  apply assembled.congr'
  filter_upwards with N
  conv_rhs => rw [original_b_decomposition, projectedSource_add, projectedSource_add]
  rfl

end
end OriginalRieszFinitePairing.CoPoisson.Ward.WholeSourceCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
