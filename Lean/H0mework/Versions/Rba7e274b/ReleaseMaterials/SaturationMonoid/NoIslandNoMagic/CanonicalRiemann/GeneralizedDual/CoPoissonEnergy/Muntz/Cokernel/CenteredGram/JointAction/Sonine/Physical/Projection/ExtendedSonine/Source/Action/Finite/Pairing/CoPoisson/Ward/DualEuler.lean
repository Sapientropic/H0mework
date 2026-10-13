import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualLanding
import H0mework.Versions.V2.Arithmetic.RieszResponse.ResponseRead

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.DualEuler

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace SchwartzMap
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)

private def read (test : SchwartzMap ℝ ℂ) : BurnolL2 →L[ℂ] ℂ :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp
    (Lp.toTemperedDistributionCLM ℂ volume 2)

private def eulerRead (test : SchwartzMap ℝ ℂ) : BurnolL2 →L[ℂ] ℂ :=
  ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp GapEuler.euler).comp
    (Lp.toTemperedDistributionCLM ℂ volume 2)

/-- The original inverse and both original source Ward equations are consumed first. -/
theorem original_source_tested (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    GapEuler.euler (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) test =
      (star coordinate.value - 1 / 2) *
        (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
          TemperedDistribution ℝ ℂ) test +
      Kernel.A coordinate * (burnolQuarterZeroExtension (Response.u : BurnolQuarterIntervalL2) :
        TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * (burnolQuarterZeroExtension (Response.v : BurnolQuarterIntervalL2) :
        TemperedDistribution ℝ ℂ) test - Kernel.beta coordinate * GapEuler.edge q test := by
  change eulerRead test _ = (star coordinate.value - 1 / 2) * read test _ +
    Kernel.A coordinate * read test _ - Kernel.beta coordinate * read test _ - _
  have source := congrArg (fun T : TemperedDistribution ℝ ℂ => T test) (Euler.source_euler coordinate)
  change eulerRead test _ = read test (burnolQuarterZeroExtension
    (Euler.sourceEuler coordinate : BurnolQuarterIntervalL2)) - Kernel.beta coordinate * GapEuler.edge q test at source
  rw [Euler.sourceEuler_eq] at source
  simpa only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, map_sub, map_add, map_smul,
    sub_apply, add_apply, smul_apply, smul_eq_mul] using source

def edgeChannel (a : ℝ) (test : SchwartzMap ℝ ℂ) : ℂ :=
  (Real.sqrt a : ℂ)⁻¹ * GapEuler.edge q (coPoissonSchwartzEnergyTranslation (-Real.log a) test)

def edgeProgramme (N : ℕ) (test : SchwartzMap ℝ ℂ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, edgeChannel (n : ℝ) test) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), edgeChannel a test

private theorem channel_read (a : ℝ) (value : BurnolL2) (test : SchwartzMap ℝ ℂ) :
    read test (ContinuousChannels.channel 1 a value) =
      (Real.sqrt a : ℂ)⁻¹ * read (coPoissonSchwartzEnergyTranslation (-Real.log a) test) value := by
  simp only [ContinuousChannels.channel, one_mul, map_smul]
  exact congrArg ((Real.sqrt a : ℂ)⁻¹ * ·) (OriginalRieszFiniteResponse.original_read value test (Real.log a))

private theorem channel_euler_read (a : ℝ) (value : BurnolL2) (test : SchwartzMap ℝ ℂ) :
    eulerRead test (ContinuousChannels.channel 1 a value) =
      (Real.sqrt a : ℂ)⁻¹ * eulerRead (coPoissonSchwartzEnergyTranslation (-Real.log a) test) value := by
  simp only [ContinuousChannels.channel, one_mul, map_smul]
  exact congrArg ((Real.sqrt a : ℂ)⁻¹ * ·) (OriginalRieszFiniteResponse.original_euler_action value test (Real.log a))

theorem channel_source (coordinate : BurnolCompletedMellinCoordinate) (a : ℝ) (test : SchwartzMap ℝ ℂ) :
    GapEuler.euler (ContinuousChannels.channel 1 a (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test =
      (ContinuousChannels.channel 1 a (burnolQuarterZeroExtension
        (Euler.sourceEuler coordinate : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * edgeChannel a test := by
  change eulerRead test _ = read test _ - _
  rw [channel_euler_read, channel_read]
  have source := congrArg (fun T : TemperedDistribution ℝ ℂ =>
    T (coPoissonSchwartzEnergyTranslation (-Real.log a) test)) (Euler.source_euler coordinate)
  change eulerRead _ _ = read _ _ - Kernel.beta coordinate * GapEuler.edge q
    (coPoissonSchwartzEnergyTranslation (-Real.log a) test) at source
  rw [source, edgeChannel]
  ring

private theorem edgeChannel_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (upper : ℝ) (test : SchwartzMap ℝ ℂ) : IntegrableOn (fun a => edgeChannel a test) (Ioc 0 upper) := by
  let value := OriginalRieszFiniteSource.edgePrimitive coordinate
  have identity (a : ℝ) : edgeChannel a test =
      eulerRead test (ContinuousChannels.channel 1 a value) +
        (star coordinate.value - 1 / 2) * read test (ContinuousChannels.channel 1 a value) := by
    rw [channel_euler_read, channel_read]
    have original := congrArg (fun T : TemperedDistribution ℝ ℂ =>
      T (coPoissonSchwartzEnergyTranslation (-Real.log a) test))
      (OriginalRieszFiniteSource.edgePrimitive_euler coordinate)
    change eulerRead _ value + (star coordinate.value - 1 / 2) * read _ value = _ at original
    unfold edgeChannel
    rw [← original]
    ring
  have integral := ContinuousChannels.channel_integrable 1 upper value
  exact (((eulerRead test).integrable_comp integral).add
    (((read test).integrable_comp integral).const_mul (star coordinate.value - 1 / 2))).congr
      (Eventually.of_forall (fun a => (identity a).symm))

private theorem dual_read (N : ℕ) (value : BurnolL2) (functional : BurnolL2 →L[ℂ] ℂ) :
    functional (DualSource.source N value) =
      (∑ n ∈ Finset.Ico 1 N, functional (ContinuousChannels.channel 1 (n : ℝ) value)) -
        ∫ a : ℝ in Ioc 0 (N : ℝ), functional (ContinuousChannels.channel 1 a value) := by
  rw [DualSource.source, map_sub, map_sum,
    ← functional.integral_comp_comm (ContinuousChannels.channel_integrable 1 N value)]

/-- The same finite cutoff transports the complete source and its complete endpoint contact. -/
theorem finite_source (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (test : SchwartzMap ℝ ℂ) :
    GapEuler.euler (DualSource.source N (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test =
      (DualSource.source N (burnolQuarterZeroExtension
        (Euler.sourceEuler coordinate : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * edgeProgramme N test := by
  change eulerRead test _ = read test _ - _
  rw [dual_read, dual_read]
  have equation (a : ℝ) : eulerRead test (ContinuousChannels.channel 1 a
      (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) =
      read test (ContinuousChannels.channel 1 a (burnolQuarterZeroExtension
        (Euler.sourceEuler coordinate : BurnolQuarterIntervalL2))) - Kernel.beta coordinate * edgeChannel a test :=
    channel_source coordinate a test
  simp_rw [equation]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    integral_sub ((read test).integrable_comp (ContinuousChannels.channel_integrable 1 N _))
      ((edgeChannel_integrable coordinate N test).const_mul (Kernel.beta coordinate)), integral_const_mul]
  unfold edgeProgramme
  ring

private theorem inverse_translation (a : ℝ) (positive : 0 < a) (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    coPoissonSchwartzEnergyTranslation (-Real.log a) test x =
      (Real.sqrt a : ℂ)⁻¹ * test (x / a) := by
  have half (h : ℝ) : (Real.exp h : ℂ) ^ (1 / 2 : ℂ) = (Real.exp (h / 2) : ℂ) := by
    calc
      _ = ((Real.exp h ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
        symm
        convert Complex.ofReal_cpow (Real.exp_pos h).le (1 / 2 : ℝ) using 1
        norm_num
      _ = _ := by
        rw [Real.rpow_def_of_pos (Real.exp_pos h), Real.log_exp]
        exact congrArg (fun x : ℝ => (Real.exp x : ℂ)) (by ring : h * (1 / 2) = h / 2)
  have squareRoot : Real.sqrt a = Real.exp (Real.log a / 2) := by
    rw [Real.exp_half, Real.exp_log positive]
  change (Real.exp (-Real.log a) : ℂ) ^ (1 / 2 : ℂ) * test (Real.exp (-Real.log a) * x) = _
  rw [half, neg_div, Real.exp_neg, ← squareRoot, Complex.ofReal_inv,
    Real.exp_neg, Real.exp_log positive]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

/-- This is the original mean-corrected edge after the exact reverse half-density action. -/
theorem edgeChannel_raw (a : ℝ) (positive : 0 < a) (test : SchwartzMap ℝ ℂ) :
    edgeChannel a test = ((q / a : ℝ) : ℂ) * (test (q / a) + test (-q / a)) -
      ∫ x : ℝ in Ioc (-q / a) (q / a), test x := by
  rw [edgeChannel, Translator.ForcingCutoff.edge_pairing,
    inverse_translation a positive test q, inverse_translation a positive test (-q)]
  have integrated : (∫ x : ℝ in Ioc (-q) q, coPoissonSchwartzEnergyTranslation (-Real.log a) test x) =
      (Real.sqrt a : ℂ)⁻¹ * (a : ℂ) * ∫ x : ℝ in Ioc (-q / a) (q / a), test x := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun x _ => inverse_translation a positive test x),
      integral_const_mul, ← intervalIntegral.integral_of_le (by norm_num : -q ≤ q),
      intervalIntegral.integral_comp_div _ positive.ne',
      intervalIntegral.integral_of_le (div_le_div_of_nonneg_right (by norm_num : -q ≤ q) positive.le),
      Complex.real_smul]
    ring
  have square : (Real.sqrt a : ℂ) ^ 2 = (a : ℂ) := by
    exact_mod_cast Real.sq_sqrt positive.le
  rw [integrated, Complex.ofReal_div]
  calc
    _ = ((Real.sqrt a : ℂ)⁻¹) ^ 2 *
        ((q : ℂ) * (test (q / a) + test (-q / a)) -
          (a : ℂ) * ∫ x : ℝ in Ioc (-q / a) (q / a), test x) := by push_cast; ring
    _ = (a : ℂ)⁻¹ *
        ((q : ℂ) * (test (q / a) + test (-q / a)) -
          (a : ℂ) * ∫ x : ℝ in Ioc (-q / a) (q / a), test x) := by rw [inv_pow, square]
    _ = _ := by
      rw [mul_sub, inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr positive.ne')]
      push_cast
      ring

theorem edgeChannel_derivative (a : ℝ) (positive : 0 < a) (test : SchwartzMap ℝ ℂ) :
    edgeChannel a test = ∫ x : ℝ in Ioc (-q / a) (q / a), (x : ℂ) * deriv test x := by
  rw [edgeChannel_raw a positive test]
  have first : IntervalIntegrable (fun x : ℝ => test x) volume (-q / a) (q / a) :=
    test.continuous.intervalIntegrable _ _
  have second : IntervalIntegrable (fun x : ℝ => (x : ℂ) * deriv test x) volume (-q / a) (q / a) :=
    (Complex.continuous_ofReal.mul (SchwartzMap.derivCLM ℂ ℂ test).continuous).intervalIntegrable _ _
  have source := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -q / a) (b := q / a)
    (fun x _ => by simpa using Complex.ofRealCLM.hasDerivAt.mul (test.hasDerivAt x))
    (first.add second)
  have ordered : -q / a ≤ q / a := div_le_div_of_nonneg_right (by norm_num) positive.le
  rw [intervalIntegral.integral_add first second,
    intervalIntegral.integral_of_le ordered, intervalIntegral.integral_of_le ordered] at source
  dsimp only [Pi.mul_apply, Complex.ofRealCLM_apply] at source
  push_cast at source ⊢
  linear_combination -source

private def cone (test : SchwartzMap ℝ ℂ) (point : ℝ × ℝ) : ℂ :=
  if point.1 * |point.2| ≤ q then (point.2 : ℂ) * deriv test point.2 else 0

private theorem cone_measurable (test : SchwartzMap ℝ ℂ) : Measurable (cone test) := by
  unfold cone
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    (Complex.measurable_ofReal.comp measurable_snd |>.mul
      ((SchwartzMap.derivCLM ℂ ℂ test).continuous.measurable.comp measurable_snd)) measurable_const

private theorem cone_section {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℝ) (nonzero : x ≠ 0) (value : E) :
    (fun a : ℝ => if a * |x| ≤ q then value else 0) =ᵐ[volume.restrict (Ioi 0)]
      (Ioc 0 (q / |x|)).indicator (fun _ : ℝ => value) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a positive
  have incidence : a * |x| ≤ q ↔ a ∈ Ioc 0 (q / |x|) := by
    rw [mem_Ioc, and_iff_right (show 0 < a from positive), le_div_iff₀ (abs_pos.mpr nonzero)]
  by_cases inside : a ∈ Ioc 0 (q / |x|)
  · rw [if_pos (incidence.mpr inside), indicator_of_mem inside]
  · rw [if_neg (fun member => inside (incidence.mp member)), indicator_of_notMem inside]

private theorem cone_section_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℝ) (nonzero : x ≠ 0) (value : E) :
    IntegrableOn (fun a : ℝ => if a * |x| ≤ q then value else 0) (Ioi 0) := by
  have original : Integrable ((Ioc 0 (q / |x|)).indicator (fun _ : ℝ => value))
      (volume.restrict (Ioi 0)) := by
    rw [integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self]
    exact integrableOn_const (by simp)
  exact original.congr (cone_section x nonzero value).symm

private theorem cone_section_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (x : ℝ) (nonzero : x ≠ 0) (value : E) :
    (∫ a : ℝ in Ioi 0, if a * |x| ≤ q then value else 0) = (q / |x|) • value := by
  rw [integral_congr_ae (cone_section x nonzero value), integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self,
    setIntegral_const]
  rw [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by positivity)]

private theorem cone_norm_integral (test : SchwartzMap ℝ ℂ) (x : ℝ) (nonzero : x ≠ 0) :
    (∫ a : ℝ in Ioi 0, ‖cone test (a, x)‖) = q * ‖deriv test x‖ := by
  have same : (fun a : ℝ => ‖cone test (a, x)‖) =
      fun a => if a * |x| ≤ q then ‖(x : ℂ) * deriv test x‖ else 0 := by
    funext a
    unfold cone
    split_ifs <;> simp
  rw [same, cone_section_integral x nonzero, smul_eq_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  field_simp

private theorem cone_integrable (test : SchwartzMap ℝ ℂ) :
    Integrable (cone test) ((volume.restrict (Ioi 0)).prod volume) := by
  apply (integrable_prod_iff' (cone_measurable test).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
    exact cone_section_integrable x nonzero ((x : ℂ) * deriv test x)
  · apply ((SchwartzMap.derivCLM ℂ ℂ test).integrable.norm.const_mul q).congr
    filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
    exact (cone_norm_integral test x nonzero).symm

private theorem edgeChannel_cone (a : ℝ) (positive : 0 < a) (test : SchwartzMap ℝ ℂ) :
    edgeChannel a test = ∫ x : ℝ, cone test (a, x) := by
  rw [edgeChannel_derivative a positive test, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  have incidence : x ∈ Icc (-q / a) (q / a) ↔ a * |x| ≤ q := by
    rw [neg_div, mem_Icc, ← abs_le, le_div_iff₀ positive, mul_comm]
  by_cases inside : x ∈ Icc (-q / a) (q / a)
  · rw [indicator_of_mem inside, cone, if_pos (incidence.mp inside)]
  · rw [indicator_of_notMem inside, cone, if_neg (fun member => inside (incidence.mpr member))]

/-- Both endpoint atoms and the original interval contact are integrated together. -/
theorem edgeChannel_full_integrable (test : SchwartzMap ℝ ℂ) :
    IntegrableOn (fun a : ℝ => edgeChannel a test) (Ioi 0) := by
  apply (cone_integrable test).integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a positive
  exact (edgeChannel_cone a positive test).symm

private theorem cone_scale_integral (test : SchwartzMap ℝ ℂ) (x : ℝ) (nonzero : x ≠ 0) :
    (∫ a : ℝ in Ioi 0, cone test (a, x)) =
      if 0 < x then (q : ℂ) * deriv test x else -(q : ℂ) * deriv test x := by
  change (∫ a : ℝ in Ioi 0, if a * |x| ≤ q then (x : ℂ) * deriv test x else 0) = _
  rw [cone_section_integral x nonzero, Complex.real_smul]
  by_cases positive : 0 < x
  · rw [if_pos positive, abs_of_pos positive]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr nonzero]
  · rw [if_neg positive, abs_of_neg (lt_of_le_of_ne (le_of_not_gt positive) nonzero)]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr nonzero]

/-- The complete continuous reverse edge generates its original-point atom.
The integer comb remains in edgeProgramme and is not erased by this calculation. -/
theorem edgeChannel_full_integral (test : SchwartzMap ℝ ℂ) :
    (∫ a : ℝ in Ioi 0, edgeChannel a test) = -(2 * (q : ℂ)) * test 0 := by
  classical
  have integrable : Integrable (fun x : ℝ => deriv test x) :=
    (SchwartzMap.derivCLM ℂ ℂ test).integrable
  have right : (∫ x : ℝ in Ioi 0, deriv test x) = -test 0 := by
    simpa using integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x _ => test.hasDerivAt x) integrable.integrableOn
      (test.tendsto_cocompact.mono_left atTop_le_cocompact)
  have left : (∫ x : ℝ in Iic 0, deriv test x) = test 0 := by
    simpa using integral_Iic_of_hasDerivAt_of_tendsto'
      (fun x _ => test.hasDerivAt x) integrable.integrableOn
      (test.tendsto_cocompact.mono_left atBot_le_cocompact)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun a positive => edgeChannel_cone a positive test),
    integral_integral_swap (f := fun a x => cone test (a, x)) (cone_integrable test)]
  have same : (fun x : ℝ => ∫ a : ℝ in Ioi 0, cone test (a, x)) =ᵐ[volume]
      (Ioi 0).piecewise (fun x => (q : ℂ) * deriv test x) (fun x => -(q : ℂ) * deriv test x) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
    exact cone_scale_integral test x nonzero
  rw [integral_congr_ae same,
    integral_piecewise measurableSet_Ioi (integrable.const_mul (q : ℂ)).integrableOn
      (integrable.const_mul (-(q : ℂ))).integrableOn,
    compl_Ioi, integral_const_mul, integral_const_mul, right, left]
  ring

theorem edgeChannel_continuous_limit (test : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => ∫ a : ℝ in Ioc 0 (N : ℝ), edgeChannel a test) atTop
      (𝓝 (-(2 * (q : ℂ)) * test 0)) := by
  have source := intervalIntegral_tendsto_integral_Ioi 0 (edgeChannel_full_integrable test)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  rw [edgeChannel_full_integral] at source
  exact source.congr' (Eventually.of_forall (fun N => intervalIntegral.integral_of_le (Nat.cast_nonneg N)))

private theorem sourceEuler_dual_read (coordinate : BurnolCompletedMellinCoordinate)
    (N : ℕ) (test : SchwartzMap ℝ ℂ) :
    read test (DualSource.source N (burnolQuarterZeroExtension
      (Euler.sourceEuler coordinate : BurnolQuarterIntervalL2))) =
      (star coordinate.value - 1 / 2) * read test (DualSource.source N (burnolQuarterZeroExtension
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) +
      Kernel.A coordinate * read test (DualSource.source N (burnolQuarterZeroExtension
        (Response.u : BurnolQuarterIntervalL2))) -
      Kernel.beta coordinate * read test (DualSource.source N (burnolQuarterZeroExtension
        (Response.v : BurnolQuarterIntervalL2))) := by
  simp_rw [CountingDual.dual_eq_adjoint]
  rw [Euler.sourceEuler_eq]
  simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
    map_sub, map_add, map_smul, smul_eq_mul]

/-- The original dual limit reads the complete independent forcing and the accumulating comb.
No separate L² realization or vanishing contact is supplied. -/
theorem original_weak_limit (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ =>
      Kernel.A coordinate * (DualSource.source N (burnolQuarterZeroExtension
        (Response.u : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * (DualSource.source N (burnolQuarterZeroExtension
        (Response.v : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * (∑ n ∈ Finset.Ico 1 N, edgeChannel (n : ℝ) test)) atTop
      (𝓝 (GapEuler.euler (CountingDual.value coordinate : TemperedDistribution ℝ ℂ) test -
        (star coordinate.value - 1 / 2) * (CountingDual.value coordinate : TemperedDistribution ℝ ℂ) test +
        (2 * (q : ℂ)) * Kernel.beta coordinate * test 0)) := by
  change Tendsto (fun N : ℕ => Kernel.A coordinate * read test (DualSource.source N
      (burnolQuarterZeroExtension (Response.u : BurnolQuarterIntervalL2))) -
    Kernel.beta coordinate * read test (DualSource.source N
      (burnolQuarterZeroExtension (Response.v : BurnolQuarterIntervalL2))) -
    Kernel.beta coordinate * (∑ n ∈ Finset.Ico 1 N, edgeChannel (n : ℝ) test)) atTop
    (𝓝 (eulerRead test (CountingDual.value coordinate) -
      (star coordinate.value - 1 / 2) * read test (CountingDual.value coordinate) +
      (2 * (q : ℂ)) * Kernel.beta coordinate * test 0))
  have actual := ((eulerRead test).continuous.tendsto (CountingDual.value coordinate)).comp
    (CountingDual.original_dual_tendsto coordinate)
  have state := ((read test).continuous.tendsto (CountingDual.value coordinate)).comp
    (CountingDual.original_dual_tendsto coordinate)
  have entire := (actual.sub (state.const_mul (star coordinate.value - 1 / 2))).sub
    ((edgeChannel_continuous_limit test).const_mul (Kernel.beta coordinate))
  have same (N : ℕ) := finite_source coordinate N test
  change ∀ N : ℕ, eulerRead test (DualSource.source N _) =
    read test (DualSource.source N _) - Kernel.beta coordinate * edgeProgramme N test at same
  simp_rw [sourceEuler_dual_read] at same
  have inputs : (fun N : ℕ => eulerRead test (DualSource.source N (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) -
      (star coordinate.value - 1 / 2) * read test (DualSource.source N (burnolQuarterZeroExtension
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) -
      Kernel.beta coordinate * ∫ a : ℝ in Ioc 0 (N : ℝ), edgeChannel a test) =
      (fun N : ℕ => Kernel.A coordinate * read test (DualSource.source N (burnolQuarterZeroExtension
        (Response.u : BurnolQuarterIntervalL2))) -
      Kernel.beta coordinate * read test (DualSource.source N (burnolQuarterZeroExtension
        (Response.v : BurnolQuarterIntervalL2))) -
      Kernel.beta coordinate * (∑ n ∈ Finset.Ico 1 N, edgeChannel (n : ℝ) test)) := by
    funext N
    rw [same N]
    unfold edgeProgramme
    ring
  dsimp only [Function.comp_def] at entire
  rw [inputs] at entire
  have output : eulerRead test (CountingDual.value coordinate) -
      (star coordinate.value - 1 / 2) * read test (CountingDual.value coordinate) -
      Kernel.beta coordinate * (-(2 * (q : ℂ)) * test 0) =
      eulerRead test (CountingDual.value coordinate) -
      (star coordinate.value - 1 / 2) * read test (CountingDual.value coordinate) +
      (2 * (q : ℂ)) * Kernel.beta coordinate * test 0 := by ring
  rw [output] at entire
  exact entire

end
end OriginalRieszFinitePairing.CoPoisson.Ward.DualEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
