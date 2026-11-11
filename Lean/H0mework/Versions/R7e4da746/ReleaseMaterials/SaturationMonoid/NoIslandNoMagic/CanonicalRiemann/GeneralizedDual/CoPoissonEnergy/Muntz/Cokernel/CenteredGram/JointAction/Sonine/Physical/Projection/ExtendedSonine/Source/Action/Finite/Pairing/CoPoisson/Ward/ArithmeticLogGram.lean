import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ArithmeticForcingKernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ArithmeticMomentGram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CenteredCountingDual
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ArithmeticLogGram
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "Hq" => BurnolQuarterIntervalL2
local notation "ell" => CenteredCountingDual.logarithm

private def logReal (x : ℝ) : ℝ := Real.log x - Real.log q + 1

private theorem logReal_even (x : ℝ) : logReal (-x) = logReal x := by
  simp only [logReal, Real.log_neg_eq_log]

private theorem logReal_integrable (a b : ℝ) : IntervalIntegrable logReal volume a b :=
  (intervalIntegral.intervalIntegrable_log'.sub intervalIntegrable_const).add intervalIntegrable_const

private theorem logReal_derivative {x : ℝ} (positive : 0 < x) : HasDerivAt logReal x⁻¹ x :=
  ((Real.hasDerivAt_log positive.ne').sub_const _).add_const _

private def powerPrimitive (j : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * j + 1) * (logReal x / (2 * (j : ℝ) + 1) - 1 / (2 * (j : ℝ) + 1) ^ 2)

private theorem powerPrimitive_derivative (j : ℕ) {x : ℝ} (positive : 0 < x) :
    HasDerivAt (powerPrimitive j) (logReal x * x ^ (2 * j)) x := by
  have denominator : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  convert! (hasDerivAt_pow (2 * j + 1) x).mul
    ((logReal_derivative positive).div_const (2 * (j : ℝ) + 1) |>.sub_const (1 / (2 * (j : ℝ) + 1) ^ 2)) using 1
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [pow_succ]
  field_simp [denominator, positive.ne']
  ring

private theorem powerPrimitive_origin (j : ℕ) : Tendsto (powerPrimitive j) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have exponent : 0 < ((2 * j + 1 : ℕ) : ℝ) := by positivity
  have power : Tendsto (fun x : ℝ => x ^ (2 * j + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_pow (by omega : 2 * j + 1 ≠ 0)] using
      (tendsto_nhdsWithin_of_tendsto_nhds ((continuous_pow (2 * j + 1)).tendsto 0) :
        Tendsto (fun x : ℝ => x ^ (2 * j + 1)) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ (2 * j + 1))))
  have weighted : Tendsto (fun x : ℝ => x ^ (2 * j + 1) * Real.log x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_comm] using! tendsto_log_mul_rpow_nhdsGT_zero exponent
  have primitive := (((weighted.sub (power.mul_const (Real.log q))).add power).div_const (2 * (j : ℝ) + 1)).sub
    (power.div_const ((2 * (j : ℝ) + 1) ^ 2))
  simp only [zero_mul, sub_zero, add_zero, zero_div] at primitive
  apply primitive.congr'
  filter_upwards with x
  unfold powerPrimitive logReal
  ring

private theorem positive_power_integral (j : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..q, logReal x * x ^ (2 * j)) =
      2 * (j : ℝ) * q ^ (2 * j + 1) / (2 * (j : ℝ) + 1) ^ 2 := by
  have integrable := (logReal_integrable 0 q).mul_continuousOn (continuous_pow (2 * j)).continuousOn
  have primitive := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (b := q)
    (by norm_num) (fun x inside => powerPrimitive_derivative j inside.1) integrable (powerPrimitive_origin j)
    (tendsto_nhdsWithin_of_tendsto_nhds (show Tendsto (powerPrimitive j) (𝓝 q) (𝓝 (powerPrimitive j q)) from by
      apply ContinuousAt.tendsto
      have hlog : ContinuousAt Real.log q := Real.continuousAt_log (by norm_num)
      unfold powerPrimitive logReal
      fun_prop))
  rw [primitive, sub_zero, powerPrimitive, logReal, sub_self, zero_add]
  have denominator : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  field_simp [denominator]
  ring

private theorem symmetric_integral (f : ℝ → ℝ) (even : ∀ x, f (-x) = f x)
    (integrable : IntervalIntegrable f volume (-q) q) :
    (∫ x : ℝ in symmetricInterval q, f x) = 2 * ∫ x : ℝ in (0 : ℝ)..q, f x := by
  have left := integrable.mono_set (by
    rw [uIcc_of_le (by norm_num : -q ≤ (0 : ℝ)), uIcc_of_le (by norm_num : -q ≤ q)]
    exact Icc_subset_Icc le_rfl (by norm_num))
  have right := integrable.mono_set (by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ q), uIcc_of_le (by norm_num : -q ≤ q)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have reflected := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := q)
  rw [show (fun x => f (-x)) = f from funext even, neg_zero] at reflected
  rw [symmetricInterval, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : -q ≤ q),
    ← intervalIntegral.integral_add_adjacent_intervals left right, ← reflected]
  ring

private theorem log_power_integral (j : ℕ) :
    (∫ x : ℝ in symmetricInterval q, logReal x * x ^ (2 * j)) =
      4 * (j : ℝ) * q ^ (2 * j + 1) / (2 * (j : ℝ) + 1) ^ 2 := by
  have even (x : ℝ) : logReal (-x) * (-x) ^ (2 * j) = logReal x * x ^ (2 * j) := by
    rw [logReal_even]
    simp only [pow_mul, neg_sq]
  have symmetric : (∫ x : ℝ in symmetricInterval q, logReal x * x ^ (2 * j)) =
      2 * ∫ x : ℝ in (0 : ℝ)..q, logReal x * x ^ (2 * j) := by
    exact symmetric_integral _ even ((logReal_integrable (-q) q).mul_continuousOn (continuous_pow (2 * j)).continuousOn)
  rw [symmetric, positive_power_integral]
  ring

private theorem log_plus_read : ((SmallScaleLog.logL2 + intervalConstant q : Hq) : ℝ → ℂ) =ᵐ[μq]
    fun x => (logReal x : ℂ) := by
  filter_upwards [Lp.coeFn_add SmallScaleLog.logL2 (intervalConstant q), SmallScaleLog.log_coeFn,
    intervalConstant_coeFn q, ae_restrict_of_ae (s := symmetricInterval q) (volume.ae_ne (0 : ℝ))]
    with x addAt logAt oneAt nonzero
  rw [addAt]
  change SmallScaleLog.logL2 x + intervalConstant q x = _
  rw [logAt, oneAt]
  unfold SmallScaleLog.logRaw logReal
  rw [Real.log_div (abs_ne_zero.mpr nonzero) (by norm_num : q ≠ 0), Real.log_abs]
  push_cast
  rfl

theorem original_mean : burnolQuarterMeanCoefficient SmallScaleLog.logL2 = -1 := by
  have zero : burnolQuarterMeanCoefficient (SmallScaleLog.logL2 + intervalConstant q) = 0 := by
    rw [Constructor.mean_integral, integral_congr_ae log_plus_read, integral_complex_ofReal]
    have moment := log_power_integral 0
    simp only [pow_zero, mul_one, Nat.cast_zero, mul_zero, zero_mul, zero_div] at moment
    rw [moment, Complex.ofReal_zero, mul_zero]
  have one : burnolQuarterMeanCoefficient (intervalConstant q) = 1 := by
    rw [Constructor.mean_integral, integral_congr_ae (intervalConstant_coeFn q), integral_const,
      burnolQuarterInterval_measureReal_univ, Complex.real_smul]
    norm_num
  have additive : burnolQuarterMeanCoefficient (SmallScaleLog.logL2 + intervalConstant q) =
      burnolQuarterMeanCoefficient SmallScaleLog.logL2 + burnolQuarterMeanCoefficient (intervalConstant q) := by
    unfold burnolQuarterMeanCoefficient
    rw [inner_add_right, add_div]
  rw [additive, one] at zero
  linear_combination zero

theorem logarithm_coeFn : ((ell : Hq) : ℝ → ℂ) =ᵐ[μq]
    fun x => ((Real.log x - Real.log q + 1 : ℝ) : ℂ) := by
  have centered : (ell : Hq) = SmallScaleLog.logL2 + intervalConstant q := by
    rw [CenteredCountingDual.logarithm, Constructor.zeroMean_read, original_mean]
    simp
  rw [centered]
  exact log_plus_read

theorem inner_centeredPower (j : ℕ) :
    inner ℂ ell (ArithmeticMomentGram.centeredPower j) =
      4 * (j : ℂ) * (q : ℂ) ^ (2 * j + 1) / (2 * (j : ℂ) + 1) ^ 2 := by
  change inner ℂ (ell : Hq) (ArithmeticMomentGram.centeredPower j : Hq) = _
  have drop := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ell (ArithmeticMomentGram.powerL2 j)
  change inner ℂ (ell : Hq) (ArithmeticMomentGram.centeredPower j : Hq) =
    inner ℂ (ell : Hq) (ArithmeticMomentGram.powerL2 j) at drop
  rw [drop, L2.inner_def]
  have raw : (fun x : ℝ => inner ℂ ((ell : Hq) x) (ArithmeticMomentGram.powerL2 j x)) =ᵐ[μq]
      fun x => ((logReal x * x ^ (2 * j) : ℝ) : ℂ) := by
    filter_upwards [logarithm_coeFn, ArithmeticMomentGram.power_coeFn j] with x logAt powerAt
    rw [logAt, powerAt, RCLike.inner_apply]
    simp only [ArithmeticMomentGram.powerRaw, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_pow]
    unfold logReal
    ring
  rw [integral_congr_ae raw, integral_complex_ofReal, log_power_integral]
  push_cast
  rfl
private theorem log_square_origin : Tendsto (fun x : ℝ => x * (Real.log x) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have half : Tendsto (fun x : ℝ => Real.log x * Real.sqrt x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using! tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1 / 2)
  have squared := half.pow 2
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at squared
  apply squared.congr'
  filter_upwards [self_mem_nhdsWithin] with x positive
  rw [mul_pow, Real.sq_sqrt (show 0 ≤ x from positive.le)]
  ring

private def squarePrimitive (x : ℝ) : ℝ := x * ((Real.log x - Real.log q) ^ 2 + 1)

private theorem squarePrimitive_origin : Tendsto squarePrimitive (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have first : Tendsto (fun x : ℝ => x * Real.log x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using! tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have coordinate : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have generated := (log_square_origin.sub (first.mul_const (2 * Real.log q))).add
    (coordinate.mul_const ((Real.log q) ^ 2 + 1))
  simp only [zero_mul, sub_zero, zero_add] at generated
  apply generated.congr'
  filter_upwards with x
  unfold squarePrimitive
  ring

private theorem squarePrimitive_derivative {x : ℝ} (positive : 0 < x) :
    HasDerivAt squarePrimitive ((logReal x) ^ 2) x := by
  convert! (hasDerivAt_id x).mul ((((Real.hasDerivAt_log positive.ne').sub_const (Real.log q)).pow 2).add_const 1) using 1
  simp only [Pi.pow_apply, id_eq]
  unfold logReal
  field_simp [positive.ne']
  ring

private theorem log_square_integrable : IntervalIntegrable (fun x : ℝ => (logReal x) ^ 2) volume (-q) q := by
  have source : MemLp (fun x : ℝ => (logReal x : ℂ)) 2 μq :=
    (Lp.memLp (ell : Hq)).ae_eq logarithm_coeFn
  have actual := (memLp_two_iff_integrable_sq_norm source.aestronglyMeasurable).mp source
  have integrated : IntegrableOn (fun x : ℝ => (logReal x) ^ 2) (Icc (-q) q) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using! actual
  exact intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : -q ≤ q) |>.mpr integrated

private theorem positive_square_integral : (∫ x : ℝ in (0 : ℝ)..q, (logReal x) ^ 2) = q := by
  have integrable := log_square_integrable.mono_set (by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ q), uIcc_of_le (by norm_num : -q ≤ q)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (b := q)
    (by norm_num) (fun x inside => squarePrimitive_derivative inside.1) integrable squarePrimitive_origin
    (tendsto_nhdsWithin_of_tendsto_nhds (show Tendsto squarePrimitive (𝓝 q) (𝓝 (squarePrimitive q)) from by
      apply ContinuousAt.tendsto
      have hlog : ContinuousAt Real.log q := Real.continuousAt_log (by norm_num)
      unfold squarePrimitive
      fun_prop))
  rw [generated, sub_zero, squarePrimitive, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, mul_one]

theorem logarithm_norm_sq : ‖ell‖ ^ 2 = (1 / 2 : ℝ) := by
  change ‖(ell : Hq)‖ ^ 2 = _
  rw [← burnolQuarterInterval_integral_norm_sq]
  have raw : (fun x : ℝ => ‖(ell : Hq) x‖ ^ 2) =ᵐ[μq] fun x => (logReal x) ^ 2 := by
    filter_upwards [logarithm_coeFn] with x read
    rw [read, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rfl
  rw [integral_congr_ae raw, symmetric_integral _ (fun x => by rw [logReal_even]) log_square_integrable,
    positive_square_integral]
  norm_num

/-- Finite forcing coefficients consume the exact original logarithm row of the q Gram. -/
theorem finite_inner (indices : Finset ℕ) (coefficient : ℕ → ℂ) :
    inner ℂ ell (∑ j ∈ indices, coefficient j • ArithmeticMomentGram.centeredPower j) =
      ∑ j ∈ indices, coefficient j *
        (4 * (j : ℂ) * (q : ℂ) ^ (2 * j + 1) / (2 * (j : ℂ) + 1) ^ 2) := by
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  have scaled (a : ℂ) (x y : BurnolQuarterMeanZeroCarrier) : inner ℂ x (a • y) = a * inner ℂ x y := inner_smul_right x y a
  rw [scaled, inner_centeredPower]

/-- The actual strong arithmetic forcing series is read with its complete original log row. -/
theorem original_log_hasSum (coordinate : BurnolCompletedMellinCoordinate) :
    HasSum (fun j : ℕ => ArithmeticForcingKernel.arithmeticCoefficient coordinate j *
      (4 * (j : ℂ) * (q : ℂ) ^ (2 * j + 1) / (2 * (j : ℂ) + 1) ^ 2))
      (inner ℂ ell (CountingForcing.integerSource coordinate)) := by
  have entry (j : ℕ) : inner ℂ (ell : Hq) (ArithmeticMomentGram.centeredPower j : Hq) =
      4 * (j : ℂ) * (q : ℂ) ^ (2 * j + 1) / (2 * (j : ℂ) + 1) ^ 2 := inner_centeredPower j
  simpa only [entry] using! ArithmeticForcingKernel.original_pair coordinate (ell : Hq)

theorem original_log_pair (coordinate : BurnolCompletedMellinCoordinate) :
    inner ℂ ell (CountingForcing.integerSource coordinate) =
      ∑' j : ℕ, ArithmeticForcingKernel.arithmeticCoefficient coordinate j *
        (4 * (j : ℂ) * (q : ℂ) ^ (2 * j + 1) / (2 * (j : ℂ) + 1) ^ 2) :=
  (original_log_hasSum coordinate).tsum_eq.symm

/-- The full counted forcing keeps its actual mean correction in this source contact. -/
theorem forcing_log_pair (coordinate : BurnolCompletedMellinCoordinate) :
    inner ℂ ell (CountingForcing.value coordinate) =
      (∑' j : ℕ, ArithmeticForcingKernel.arithmeticCoefficient coordinate j *
        (4 * (j : ℂ) * (q : ℂ) ^ (2 * j + 1) / (2 * (j : ℂ) + 1) ^ 2)) -
      OriginalRieszSource.Translator.ForcingMeanZero.mean coordinate / 2 := by
  have norm : inner ℂ ell ell = (1 / 2 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    change (‖ell‖ : ℂ) ^ 2 = (1 / 2 : ℂ)
    rw [← Complex.ofReal_pow, logarithm_norm_sq]
    norm_num
  have scaled : inner ℂ ell (OriginalRieszSource.Translator.ForcingMeanZero.mean coordinate • ell) =
      OriginalRieszSource.Translator.ForcingMeanZero.mean coordinate * inner ℂ ell ell :=
    inner_smul_right ell ell (OriginalRieszSource.Translator.ForcingMeanZero.mean coordinate)
  rw [CountingForcing.value, inner_sub_right, scaled, original_log_pair, norm]
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ArithmeticLogGram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
