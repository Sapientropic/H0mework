import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CenteredCountingDualSupport

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.FirstBandNormalization

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource OriginalPaPhysicalGreen
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction

def normalPlus (upper : ℝ) (seed : BurnolL2) : BurnolL2 :=
  ∫ a : ℝ in Ioc 0 upper, ContinuousChannels.channel 1 a seed

private theorem channel_scaling (seed : BurnolL2) (t a : ℝ) (positive : 0 < t) (apos : 0 < a) :
    ContinuousChannels.channel 1 (t * a) (burnolMultiplicativeDilation (-Real.log 2) seed) =
      (Real.sqrt t : ℂ)⁻¹ • burnolMultiplicativeDilation (Real.log (t / 2))
        (ContinuousChannels.channel 1 a seed) := by
  simp only [ContinuousChannels.channel, one_mul, map_smul, smul_smul,
    burnolMultiplicativeDilation_add, Real.sqrt_mul positive.le,
    Real.log_mul positive.ne' apos.ne', Real.log_div positive.ne' (by norm_num : (2 : ℝ) ≠ 0),
    Complex.ofReal_mul, mul_inv_rev]
  congr 1
  · ring
  · congr 1
    ring

/-- The complete strong integral is rescaled before any restriction or mean is taken. -/
theorem scaling (seed : BurnolL2) (t : ℝ) (positive : 0 < t) :
    normalPlus t (burnolMultiplicativeDilation (-Real.log 2) seed) =
      (Real.sqrt t : ℂ) • burnolMultiplicativeDilation (Real.log (t / 2)) (normalPlus 1 seed) := by
  let expanded := burnolMultiplicativeDilation (-Real.log 2) seed
  have change : t • (∫ a : ℝ in Ioc 0 1, ContinuousChannels.channel 1 (t * a) expanded) =
      normalPlus t expanded := by
    have original := intervalIntegral.smul_integral_comp_mul_left
      (f := fun a => ContinuousChannels.channel 1 a expanded) (a := 0) (b := 1) t
    simpa only [mul_zero, mul_one, intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le positive.le, normalPlus] using original
  rw [← change]
  have rescaled : (∫ a : ℝ in Ioc 0 1, ContinuousChannels.channel 1 (t * a) expanded) =
      (Real.sqrt t : ℂ)⁻¹ • burnolMultiplicativeDilation (Real.log (t / 2)) (normalPlus 1 seed) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun a inside => channel_scaling seed t a positive inside.1),
      integral_smul]
    congr 1
    exact (burnolMultiplicativeDilation (Real.log (t / 2))).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (ContinuousChannels.channel_integrable 1 1 seed)
  rw [rescaled, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  have coefficient : (t : ℂ) * (Real.sqrt t : ℂ)⁻¹ = (Real.sqrt t : ℂ) := by
    have nonzero : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr positive).ne'
    have square : (Real.sqrt t : ℂ) ^ 2 = (t : ℂ) := by exact_mod_cast Real.sq_sqrt positive.le
    field_simp
    linear_combination -square
  convert! congrArg (fun scalar : ℂ => scalar •
    burnolMultiplicativeDilation (Real.log (t / 2)) (normalPlus 1 seed)) coefficient using 1

theorem shifted_scaling (state : M) (t : ℝ) (positive : 0 < t) :
    normalPlus t (burnolMultiplicativeDilation (-Real.log 2) (E (state : Hq))) =
      (Real.sqrt t : ℂ) • burnolMultiplicativeDilation (Real.log (t / 2)) (normalPlus 1 (E (state : Hq))) :=
  scaling _ t positive

private theorem source_one (seed : BurnolL2) : DualSource.source 1 seed = -normalPlus 1 seed := by
  simp only [DualSource.source, Finset.Ico_self, Finset.sum_empty, zero_sub, normalPlus, Nat.cast_one]

theorem one_support (state : M) (even : reflectRestricted q (state : Hq) = state) :
    normalPlus 1 (E (state : Hq)) = E (R (normalPlus 1 (E (state : Hq)))) := by
  have generated := CenteredCountingDualSupport.source_support state even 1 (by decide)
  rw [source_one, map_neg, map_neg] at generated
  exact neg_injective generated

private theorem dilation_support (value : BurnolL2) (supported : value = E (R value))
    (h : ℝ) (nonnegative : 0 ≤ h) :
    burnolMultiplicativeDilation h value = E (R (burnolMultiplicativeDilation h value)) := by
  have cut := originalPhysicalCutoff_coeFn q value
  have fixed : originalPhysicalCutoff q value = value := supported.symm
  rw [fixed] at cut
  have scale : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp h * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) (Real.exp_ne_zero h))
  symm
  apply OriginalRieszFiniteColumns.cutoff_eq_self_of_ae_zero
  filter_upwards [burnolMultiplicativeDilation_coeFn h value, scale.ae cut] with x dilation source
  intro outside
  have moved : Real.exp h * x ∉ symmetricInterval q := by
    intro inside
    have large : q < |x| := lt_of_not_ge (fun hx => outside (abs_le.mp hx))
    have bound := abs_le.mpr inside
    rw [abs_mul, abs_of_pos (Real.exp_pos h)] at bound
    nlinarith [Real.one_le_exp_iff.mpr nonnegative, abs_nonneg x]
  rw [dilation, burnolL2RawNormalizedDilation, source, indicator_of_notMem moved, mul_zero]

theorem shifted_support (state : M) (even : reflectRestricted q (state : Hq) = state)
    (t : ℝ) (large : 2 ≤ t) :
    normalPlus t (burnolMultiplicativeDilation (-Real.log 2) (E (state : Hq))) =
      E (R (normalPlus t (burnolMultiplicativeDilation (-Real.log 2) (E (state : Hq))))) := by
  have positive : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) large
  rw [shifted_scaling state t positive]
  have generated := dilation_support _ (one_support state even) (Real.log (t / 2))
    (Real.log_nonneg (by linarith : 1 ≤ t / 2))
  simpa only [map_smul] using congrArg ((Real.sqrt t : ℂ) • ·) generated

theorem shifted_integrable (state : M) (even : reflectRestricted q (state : Hq) = state)
    (t : ℝ) (large : 2 ≤ t) :
    Integrable (normalPlus t (burnolMultiplicativeDilation (-Real.log 2) (E (state : Hq))) : ℝ → ℂ) := by
  rw [shifted_support state even t large]
  exact (burnolQuarterZeroExtensionRaw_integrable _).congr (burnolQuarterZeroExtension_coe _).symm

private theorem supported_integral (value : BurnolL2) (supported : value = E (R value)) :
    inner ℂ (E (intervalConstant q)) value = ∫ x : ℝ, value x := by
  have paired := ContinuousLinearMap.adjoint_inner_left R value (intervalConstant q)
  change inner ℂ (E (intervalConstant q)) value = _ at paired
  have integralRead : (∫ x : ℝ, value x) = ∫ x : ℝ in symmetricInterval q, R value x := by
    calc
      _ = ∫ x : ℝ, E (R value) x := congrArg (fun seed : BurnolL2 => ∫ x : ℝ, seed x) supported
      _ = _ := by rw [integral_congr_ae (burnolQuarterZeroExtension_coe (R value)),
        integral_indicator (measurableSet_symmetricInterval q)]
  rw [paired, integralRead, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [intervalConstant_coeFn q] with x constant
  rw [constant]
  simp only [RCLike.inner_apply, map_one, mul_one]

theorem one_integral (state : M) (even : reflectRestricted q (state : Hq) = state) :
    (∫ x : ℝ, normalPlus 1 (E (state : Hq)) x) = -inner ℂ SmallScaleLog.logL2 (state : Hq) := by
  have source := CountingDual.source_pairing 1 (E (intervalConstant q)) (E (state : Hq))
  have window : R (FiniteForcing.source 1 (E (intervalConstant q))) = SmallScaleLog.logL2 := by
    have actual := WindowCounting.constant_source 1 (by decide)
    simpa only [WindowCounting.windowSource, WindowCounting.harmonicCoefficient, Finset.Ico_self, Finset.sum_empty, Nat.cast_one,
      Real.log_one, Complex.ofReal_zero, sub_self, zero_smul, zero_add] using actual
  have paired := ContinuousLinearMap.adjoint_inner_right R
    (FiniteForcing.source 1 (E (intervalConstant q))) (state : Hq)
  change inner ℂ (FiniteForcing.source 1 (E (intervalConstant q))) (E (state : Hq)) = _ at paired
  rw [paired, window] at source
  rw [source_one, inner_neg_right, supported_integral _ (one_support state even)] at source
  linear_combination source

private theorem dilation_integral (value : BurnolL2) (h : ℝ) :
    (∫ x : ℝ, burnolMultiplicativeDilation h value x) =
      (Real.exp (-h / 2) : ℂ) * ∫ x : ℝ, value x := by
  rw [integral_congr_ae (burnolMultiplicativeDilation_coeFn h value)]
  unfold burnolL2RawNormalizedDilation
  rw [integral_const_mul, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr (Real.exp_pos h)),
    Complex.real_smul, Complex.ofReal_inv, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Real.exp_neg, ← Real.exp_add]
  congr 2
  ring

/-- The total mean is inherited from the complete N=1 source; contraction does not reset it. -/
theorem shifted_integral (state : M) (even : reflectRestricted q (state : Hq) = state)
    (t : ℝ) (large : 2 ≤ t) :
    (∫ x : ℝ, normalPlus t (burnolMultiplicativeDilation (-Real.log 2) (E (state : Hq))) x) =
      -(Real.sqrt 2 : ℂ) * inner ℂ SmallScaleLog.logL2 (state : Hq) := by
  have positive : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) large
  rw [shifted_scaling state t positive,
    integral_congr_ae (Lp.coeFn_smul (Real.sqrt t : ℂ)
      (burnolMultiplicativeDilation (Real.log (t / 2)) (normalPlus 1 (E (state : Hq)))))]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, dilation_integral, one_integral state even, ← mul_assoc]
  have root_exp (a : ℝ) (apos : 0 < a) : Real.sqrt a = Real.exp (Real.log a / 2) := by
    rw [Real.exp_half, Real.exp_log apos]
  have coefficient : Real.sqrt t * Real.exp (-(Real.log (t / 2)) / 2) = Real.sqrt 2 := by
    rw [root_exp t positive, root_exp 2 (by norm_num), ← Real.exp_add,
      Real.log_div positive.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [← Complex.ofReal_mul, coefficient]
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.FirstBandNormalization
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
