import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.LogPairClosureSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.Arithmetic.MellinTateSource.Isometry
import H0mework.Versions.R7e4da746.Arithmetic.MellinTateSource.L2Raw
import H0mework.Versions.R7e4da746.Arithmetic.SonineProjection.ConstructorCompact
import H0mework.Versions.R7e4da746.Arithmetic.SonineProjection.Ward
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ForcingPrimitive
import H0mework.Versions.R7e4da746.Arithmetic.RieszGreen.SourceDerivative
import H0mework.Versions.R7e4da746.Arithmetic.RieszGreen.RawDerivative
import H0mework.Arithmetic.MellinProjection.TailKernel
import H0mework.Arithmetic.TruncatedFourier.ActualBridge
import H0mework.Arithmetic.TruncatedFourier.IntegralKernel
import H0mework.Arithmetic.TruncatedFourier.RadiusActualBridge
import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel
import H0mework.Versions.R7e4da746.Arithmetic.BurnolPhysical.L2DirectDilation
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.MultiplicativeDilation

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.FourierLogDomain
open Complex Filter FourierTransform MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.CountingQuadratic OriginalGamma.Source.CountingQuadraticLimit
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.LogPairClosure
noncomputable section
local notation "q" => (1 / 4 : ℝ)
private def seedFourierRaw : ℝ → ℂ := burnolRadiusTruncatedFourierRaw q (intervalConstant q)

private theorem seed_fourier_raw :
    (fourierL2 ConstantDual.seed : ℝ → ℂ) =ᵐ[volume] seedFourierRaw :=
  burnolRadiusFourierL2_zeroExtension_ae_eq_raw (intervalConstant q)

private theorem seed_fourier_bound (x : ℝ) : ‖seedFourierRaw x‖ ≤ 1 / 2 := by
  have source := burnolRadiusTruncatedFourierRaw_norm_le (by norm_num : (0 : ℝ) < q)
    (intervalConstant q) x
  have square := quarterSeed_norm_sq
  have extension : ‖ConstantDual.seed‖ = ‖intervalConstant q‖ := by
    change ‖burnolQuarterZeroExtension (intervalConstant q)‖ = _
    rw [← burnolQuarterZeroExtensionExplicit_is_adjoint]
    exact burnolQuarterZeroExtensionValue_norm _
  rw [extension] at square
  have amplitude : Real.sqrt (2 * q) * ‖intervalConstant q‖ = 1 / 2 := by
    have same : ‖intervalConstant q‖ = Real.sqrt (2 * q) := by
      rw [← Real.sqrt_sq (norm_nonneg (intervalConstant q)), square]
      norm_num
    rw [same, ← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 * q)]
    norm_num
  exact source.trans_eq amplitude

private theorem seed_fourier_inverse_bound (x : ℝ) (nonzero : x ≠ 0) :
    ‖seedFourierRaw x‖ ≤ |x|⁻¹ := by
  have source := Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q)
  have read : seedFourierRaw x = ∫ y : ℝ in (-q)..q, Constructor.phase x y := by
    rw [seedFourierRaw, ← Constructor.fourierRaw_state, congrFun source x,
      Constructor.fourierRaw_integral]
    simp only [mul_one]
  let rate : ℂ := -2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)
  have rateNe : rate ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr nonzero)
  have phase (y : ℝ) : Constructor.phase x y = Complex.exp (rate * (y : ℂ)) := by
    unfold Constructor.phase rate
    rw [Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  rw [read, intervalIntegral.integral_congr (fun y _ => phase y), integral_exp_mul_complex rateNe]
  have numerator : ‖Complex.exp (rate * (q : ℂ)) - Complex.exp (rate * ((-q : ℝ) : ℂ))‖ ≤ 2 := by
    have norms (y : ℝ) : ‖Complex.exp (rate * (y : ℂ))‖ = 1 := by
      rw [← phase y]
      simp only [Constructor.phase, Circle.norm_coe]
    exact (norm_sub_le _ _).trans_eq (by rw [norms, norms]; norm_num)
  rw [norm_div]
  have denominator : ‖rate‖ = 2 * Real.pi * |x| := by
    dsimp [rate]
    simp only [norm_mul, norm_neg, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      norm_I, mul_one, abs_of_pos Real.pi_pos]
  rw [denominator]
  have positive : 0 < |x| := abs_pos.mpr nonzero
  apply (div_le_div_of_nonneg_right numerator (by positivity)).trans
  rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi * |x|)]
  have cancelled : |x|⁻¹ * (2 * Real.pi * |x|) = 2 * Real.pi := by field_simp
  rw [cancelled]
  linarith [Real.two_le_pi]

private theorem log_power_bound (y : ℝ) (positive : 0 < y) :
    |Real.log y| ≤ 4 * (y ^ (-1 / 4 : ℝ) + y ^ (1 / 4 : ℝ)) := by
  have lower := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos positive (-1 / 4 : ℝ))
  have upper := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos positive (1 / 4 : ℝ))
  rw [Real.log_rpow positive] at lower upper
  rw [abs_le]
  constructor <;> nlinarith [Real.rpow_nonneg positive.le (-1 / 4 : ℝ),
    Real.rpow_nonneg positive.le (1 / 4 : ℝ)]

private theorem seed_log_bound (x : ℝ) (nonzero : x ≠ 0) :
    ‖(Real.log |x| : ℂ) * seedFourierRaw x‖ ≤
      8 * (if |x| ≤ 1 then |x| ^ (-1 / 4 : ℝ) else |x| ^ (-3 / 4 : ℝ)) := by
  have positive : 0 < |x| := abs_pos.mpr nonzero
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have logarithm := log_power_bound |x| positive
  by_cases small : |x| ≤ 1
  · rw [if_pos small]
    have compare : |x| ^ (1 / 4 : ℝ) ≤ |x| ^ (-1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge positive small (by norm_num)
    have source := mul_le_mul logarithm (seed_fourier_bound x) (norm_nonneg _)
      (by positivity : 0 ≤ 4 * (|x| ^ (-1 / 4 : ℝ) + |x| ^ (1 / 4 : ℝ)))
    nlinarith [Real.rpow_nonneg positive.le (-1 / 4 : ℝ)]
  · rw [if_neg small]
    have compare : |x| ^ (-1 / 4 : ℝ) ≤ |x| ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_not_ge small) (by norm_num)
    have source := mul_le_mul logarithm (seed_fourier_inverse_bound x nonzero) (norm_nonneg _)
      (by positivity : 0 ≤ 4 * (|x| ^ (-1 / 4 : ℝ) + |x| ^ (1 / 4 : ℝ)))
    have product : |x| ^ (1 / 4 : ℝ) * |x|⁻¹ = |x| ^ (-3 / 4 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add positive]
      norm_num
    calc
      _ ≤ 4 * (|x| ^ (-1 / 4 : ℝ) + |x| ^ (1 / 4 : ℝ)) * |x|⁻¹ := source
      _ ≤ 8 * |x| ^ (1 / 4 : ℝ) * |x|⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr positive.le)
      _ = _ := by rw [mul_assoc, product]

private def powerHead (x : ℝ) : ℂ :=
  (symmetricInterval 1).indicator (fun x : ℝ => ((|x| : ℝ) : ℂ) ^ (-1 / 4 : ℂ)) x

private theorem power_head_memLp : MemLp powerHead 2 volume := by
  have measured : Measurable (fun x : ℝ => ((|x| : ℝ) : ℂ) ^ (-1 / 4 : ℂ)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x outside
    exact (Complex.continuousAt_ofReal_cpow_const |x| (-1 / 4 : ℂ)
      (Or.inr (abs_ne_zero.mpr outside))).comp continuous_abs.continuousAt |>.continuousWithinAt
  apply (memLp_indicator_iff_restrict (measurableSet_symmetricInterval 1)).mpr
  apply (memLp_two_iff_integrable_sq_norm measured.aestronglyMeasurable).mpr
  have native := (intervalIntegral.intervalIntegrable_cpow' (r := (-1 / 2 : ℂ))
    (by norm_num) (a := -1) (b := 1)).norm
  have integral : Integrable (fun x : ℝ => ‖(x : ℂ) ^ (-1 / 2 : ℂ)‖)
      (volume.restrict (symmetricInterval 1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp native
  apply integral.congr
  filter_upwards [ae_restrict_of_ae (s := symmetricInterval 1) (volume.ae_ne (0 : ℝ))] with x nonzero
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num,
    show (-1 / 4 : ℂ) = ((-1 / 4 : ℝ) : ℂ) by norm_num]
  simp only [Complex.norm_cpow_real, Complex.norm_real, Real.norm_eq_abs, abs_abs]
  rw [show (-1 / 2 : ℝ) = (-1 / 4 : ℝ) * 2 by ring,
    Real.rpow_mul (abs_nonneg x), Real.rpow_two]

private def powerHeadL2 : BurnolL2 := power_head_memLp.toLp powerHead
private def powerEnvelopeL2 : BurnolL2 := powerHeadL2 + burnolTateReciprocalL2 powerHeadL2

private def powerProfile (y : ℝ) : ℝ :=
  if y ≤ 1 then y ^ (-1 / 4 : ℝ) else y ^ (-3 / 4 : ℝ)

private def powerEnvelopeRaw (x : ℝ) : ℂ := powerHead x + burnolTateReciprocalRaw powerHead x

private theorem envelope_raw : (powerEnvelopeL2 : ℝ → ℂ) =ᵐ[volume] powerEnvelopeRaw := by
  have source : (powerHeadL2 : ℝ → ℂ) =ᵐ[volume] powerHead := power_head_memLp.coeFn_toLp
  have actual := burnolTateReciprocalL2_coeFn powerHeadL2
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp powerHeadL2) power_head_memLp source
  filter_upwards [Lp.coeFn_add powerHeadL2 (burnolTateReciprocalL2 powerHeadL2), source, actual.trans pulled]
      with x addition first second
  rw [powerEnvelopeL2, addition, Pi.add_apply, first, second]
  rfl

private theorem envelope_norm (x : ℝ) (nonzero : x ≠ 0) : powerProfile |x| ≤ ‖powerEnvelopeRaw x‖ := by
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have inversePositive : 0 < |x⁻¹| := abs_pos.mpr (inv_ne_zero nonzero)
  unfold powerEnvelopeRaw powerHead burnolTateReciprocalRaw powerProfile
  dsimp only
  by_cases small : |x| ≤ 1
  · rw [if_pos small, indicator_of_mem (show x ∈ symmetricInterval 1 from abs_le.mp small)]
    by_cases inverseSmall : |x|⁻¹ ≤ 1
    · have same : |x| = 1 := le_antisymm small ((inv_le_one₀ positive).mp inverseSmall)
      rw [indicator_of_mem (show x⁻¹ ∈ symmetricInterval 1 from abs_le.mp (by
        simpa only [abs_inv] using inverseSmall)), abs_inv, same]
      norm_num
    · rw [indicator_of_notMem (show x⁻¹ ∉ symmetricInterval 1 from fun h => inverseSmall (by
        rw [← abs_inv]; exact abs_le.mpr h)), mul_zero, add_zero,
        Complex.norm_cpow_eq_rpow_re_of_pos positive]
      norm_num
  · rw [if_neg small, indicator_of_notMem (show x ∉ symmetricInterval 1 from fun h => small (abs_le.mpr h))]
    have inverseSmall : |x|⁻¹ ≤ 1 := (inv_le_one₀ positive).mpr (le_of_not_ge small)
    rw [indicator_of_mem (show x⁻¹ ∈ symmetricInterval 1 from abs_le.mp (by simpa only [abs_inv] using inverseSmall)),
      zero_add, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_abs, abs_inv,
      Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr positive)]
    norm_num
    rw [Real.inv_rpow positive.le, ← Real.rpow_neg positive.le, ← Real.rpow_neg_one,
      ← Real.rpow_add positive]
    norm_num


private theorem seed_log_memLp :
    MemLp (fun x : ℝ => (Real.log |x| : ℂ) * seedFourierRaw x) 2 volume := by
  have envelope : MemLp powerEnvelopeRaw 2 volume :=
    (Lp.memLp powerEnvelopeL2).ae_eq envelope_raw
  apply envelope.of_le_mul (c := 8)
    ((by fun_prop : Measurable (fun x : ℝ => (Real.log |x| : ℂ))).mul
      (burnolRadiusTruncatedFourierRaw_continuous (intervalConstant q)).measurable).aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
  exact (seed_log_bound x nonzero).trans
    (mul_le_mul_of_nonneg_left (envelope_norm x nonzero) (by norm_num))

private def seedFourierLog : BurnolL2 :=
  seed_log_memLp.toLp (fun x : ℝ => (Real.log |x| : ℂ) * seedFourierRaw x)

private theorem seed_fourier_log_pair : LogPair (fourierL2 ConstantDual.seed) seedFourierLog := by
  filter_upwards [seed_log_memLp.coeFn_toLp, seed_fourier_raw] with x logRead source
  dsimp only [seedFourierLog]
  rw [logRead, source]

private theorem logPair_smul (a : ℂ) (value logarithm : BurnolL2) (source : LogPair value logarithm) :
    LogPair (a • value) (a • logarithm) := by
  filter_upwards [source, Lp.coeFn_smul a value, Lp.coeFn_smul a logarithm] with x read first second
  rw [first, second]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [read]
  ring

private theorem logPair_sub (left leftLog right rightLog : BurnolL2)
    (hl : LogPair left leftLog) (hr : LogPair right rightLog) :
    LogPair (left - right) (leftLog - rightLog) := by
  filter_upwards [hl, hr, Lp.coeFn_sub left right, Lp.coeFn_sub leftLog rightLog] with x first second raw logarithm
  rw [raw, logarithm]
  simp only [Pi.sub_apply]
  rw [first, second, mul_sub]

private theorem logPair_dilation (h : ℝ) (value logarithm : BurnolL2) (source : LogPair value logarithm) :
    LogPair (burnolMultiplicativeDilation h value)
      (burnolMultiplicativeDilation h logarithm - (h : ℂ) • burnolMultiplicativeDilation h value) := by
  have pulled := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (Real.exp_ne_zero h)).ae source
  filter_upwards [pulled, burnolMultiplicativeDilation_coeFn h value,
    burnolMultiplicativeDilation_coeFn h logarithm,
    Lp.coeFn_sub (burnolMultiplicativeDilation h logarithm) ((h : ℂ) • burnolMultiplicativeDilation h value),
    Lp.coeFn_smul (h : ℂ) (burnolMultiplicativeDilation h value), volume.ae_ne (0 : ℝ)]
    with x read first second difference scalar nonzero
  simp only [smul_eq_mul] at read
  rw [difference]
  simp only [Pi.sub_apply]
  rw [scalar]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [first, second]
  simp only [burnolL2RawNormalizedDilation]
  change logarithm (Real.exp h * x) = _ at read
  rw [read, abs_mul, abs_of_pos (Real.exp_pos h),
    Real.log_mul (Real.exp_ne_zero h) (abs_ne_zero.mpr nonzero), Real.log_exp]
  push_cast
  ring

private theorem weighted_log_power_integrable (p : ℝ) (above : -1 < p) :
    IntegrableOn (fun t : ℝ => |Real.log (4 * t)| * t ^ p) (Ioc 0 q) := by
  let epsilon : ℝ := (p + 1) / 2
  have epsilonPositive : 0 < epsilon := by dsimp [epsilon]; linarith
  have lower : -1 < p - epsilon := by dsimp [epsilon]; linarith
  have head := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := q) lower).1.const_mul epsilon⁻¹
  have regular := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := q) above).1.const_mul |Real.log 4|
  apply (head.add regular).mono'
    (by fun_prop : Measurable (fun t : ℝ => |Real.log (4 * t)| * t ^ p)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
  simp only [Pi.add_apply]
  have unit : t ≤ 1 := by linarith [inside.2]
  have logNegative : Real.log t ≤ 0 := Real.log_nonpos inside.1.le unit
  have source := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos inside.1 (-epsilon))
  rw [Real.log_rpow inside.1] at source
  have logarithm : |Real.log t| ≤ epsilon⁻¹ * t ^ (-epsilon) := by
    rw [abs_of_nonpos logNegative, ← div_eq_inv_mul, le_div_iff₀ epsilonPositive]
    nlinarith
  have split : |Real.log (4 * t)| ≤ |Real.log t| + |Real.log 4| := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) inside.1.ne']
    exact (abs_add_le _ _).trans_eq (add_comm _ _)
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg inside.1.le _))]
  calc
    _ ≤ (epsilon⁻¹ * t ^ (-epsilon) + |Real.log 4|) * t ^ p := by
      exact mul_le_mul_of_nonneg_right (split.trans (add_le_add logarithm le_rfl))
        (Real.rpow_nonneg inside.1.le _)
    _ = _ := by
      rw [add_mul, mul_assoc, ← Real.rpow_add inside.1]
      rw [show -epsilon + p = p - epsilon by ring]

private theorem b_log_weighted_integrable (c : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun t : ℝ => Real.sqrt t * |Real.log (4 * t)| * ‖sourceRawDerivative c t‖) (Ioc 0 q) := by
  let coefficient : ℝ := ‖ForcingPrimitive.leadingCoefficient c * (star c.value - 1)‖
  obtain ⟨B, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn (b_regular_slope_continuous c)
  have singular := (weighted_log_power_integrable (c.value.re - 3 / 2)
    (by linarith [c.rightHalf])).const_mul coefficient
  have regular := (weighted_log_power_integrable (1 / 2) (by norm_num)).const_mul B
  apply (singular.add regular).mono'
    ((Real.continuous_sqrt.measurable.mul (by fun_prop)).mul
      (source_slope_measurable c).norm).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [Real.norm_of_nonneg (by positivity), b_slope_synthesis c t inside.1]
  have weightedPower : Real.sqrt t * ‖(t : ℂ) ^ (star c.value - 2)‖ =
      t ^ (c.value.re - 3 / 2) := by
    rw [Real.sqrt_eq_rpow, Complex.norm_cpow_eq_rpow_re_of_pos inside.1, ← Real.rpow_add inside.1]
    congr 1
    norm_num [sub_re, star_def, conj_re]
    ring
  have regularBound := bounded t (Ioc_subset_Icc_self inside)
  calc
    _ ≤ Real.sqrt t * |Real.log (4 * t)| *
        (‖(ForcingPrimitive.leadingCoefficient c * (star c.value - 1)) *
          (t : ℂ) ^ (star c.value - 2)‖ + ‖bRegularSlope c t‖) := by
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ Real.sqrt t * |Real.log (4 * t)| *
        (coefficient * ‖(t : ℂ) ^ (star c.value - 2)‖ + B) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl regularBound) (by positivity)
    _ = _ := by
      rw [mul_add]
      change _ = coefficient * (|Real.log (4 * t)| * t ^ (c.value.re - 3 / 2)) +
        B * (|Real.log (4 * t)| * t ^ (1 / 2 : ℝ))
      rw [Real.sqrt_eq_rpow]
      have source := weightedPower
      rw [Real.sqrt_eq_rpow] at source
      rw [← source]
      ring

private theorem return_log_weighted_integrable (c : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun t : ℝ => Real.sqrt t * |Real.log (4 * t)| * ‖burnolRieszReturnRawDerivative c t‖)
      (Ioc 0 q) := by
  obtain ⟨B, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (burnolRieszReturnRawDerivative_continuous c).continuousOn
  apply ((weighted_log_power_integrable (1 / 2) (by norm_num)).const_mul B).mono'
    ((Real.continuous_sqrt.measurable.mul
      (by fun_prop : Measurable (fun t : ℝ => |Real.log (4 * t)|))).mul
      (burnolRieszReturnRawDerivative_continuous c).measurable.norm).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
  simp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (by positivity), Real.sqrt_eq_rpow]
  have bound := bounded t (Ioc_subset_Icc_self inside)
  calc
    _ ≤ t ^ (1 / 2 : ℝ) * |Real.log (4 * t)| * B :=
      mul_le_mul_of_nonneg_left bound
        (mul_nonneg (Real.rpow_nonneg inside.1.le _) (abs_nonneg _))
    _ = _ := by ring

end
end OriginalGamma.Source.FourierLogDomain
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
