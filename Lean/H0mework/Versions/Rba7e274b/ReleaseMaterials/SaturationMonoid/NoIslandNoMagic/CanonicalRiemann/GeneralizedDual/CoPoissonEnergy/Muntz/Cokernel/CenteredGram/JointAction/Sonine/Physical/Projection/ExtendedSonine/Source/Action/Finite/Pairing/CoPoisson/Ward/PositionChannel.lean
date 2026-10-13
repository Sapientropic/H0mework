import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionEuler
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionCountingLimit

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.PositionChannel

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace SchwartzMap
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)

def eulerCotest (test : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  -(1 / 2 : ℂ) • test - SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) (SchwartzMap.derivCLM ℂ ℂ test)

theorem eulerCotest_apply (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    eulerCotest test x = -(1 / 2 : ℂ) * test x - (x : ℂ) * deriv test x := by
  have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [eulerCotest, sub_apply, smul_apply, SchwartzMap.smulLeftCLM_apply growth,
    SchwartzMap.derivCLM_apply, smul_eq_mul]

theorem euler_read (value : TemperedDistribution ℝ ℂ) (test : SchwartzMap ℝ ℂ) :
    GapEuler.euler value test = value (eulerCotest test) := by
  rw [Dilation.euler_test]
  simp only [eulerCotest, map_sub, map_smul, smul_eq_mul]

private theorem eulerCotest_action (test : SchwartzMap ℝ ℂ) (h : ℝ) :
    coPoissonSchwartzEnergyTranslation h (eulerCotest test) =
      eulerCotest (coPoissonSchwartzEnergyTranslation h test) := by
  ext x
  have derivative := (test.hasDerivAt (Real.exp h * x)).scomp x
    ((hasDerivAt_id x).const_mul (Real.exp h))
  have normalized := derivative.const_mul ((Real.exp h : ℂ) ^ (1 / 2 : ℂ))
  have sourceDerivative : deriv (coPoissonSchwartzEnergyTranslation h test) x =
      (Real.exp h : ℂ) ^ (1 / 2 : ℂ) * ((Real.exp h : ℂ) * deriv test (Real.exp h * x)) := by
    change deriv (fun y : ℝ => (Real.exp h : ℂ) ^ (1 / 2 : ℂ) * test (Real.exp h * y)) x = _
    simpa only [Complex.real_smul, id_eq, Function.comp_apply, mul_one] using normalized.deriv
  rw [eulerCotest_apply, sourceDerivative]
  change (Real.exp h : ℂ) ^ (1 / 2 : ℂ) * eulerCotest test (Real.exp h * x) = _
  rw [eulerCotest_apply]
  change _ = -(1 / 2 : ℂ) * ((Real.exp h : ℂ) ^ (1 / 2 : ℂ) * test (Real.exp h * x)) - _
  push_cast
  ring

def read (coordinate : BurnolCompletedMellinCoordinate) (a : ℝ) (test : SchwartzMap ℝ ℂ) : ℂ :=
  (Real.sqrt a : ℂ)⁻¹ * PositionEuler.source coordinate (coPoissonSchwartzEnergyTranslation (-Real.log a) test)

private def l2Read (test : SchwartzMap ℝ ℂ) : BurnolL2 →L[ℂ] ℂ :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp (Lp.toTemperedDistributionCLM ℂ volume 2)

private theorem l2_channel_read (a : ℝ) (value : BurnolL2) (test : SchwartzMap ℝ ℂ) :
    (ContinuousChannels.channel 1 a value : TemperedDistribution ℝ ℂ) test =
      (Real.sqrt a : ℂ)⁻¹ * (value : TemperedDistribution ℝ ℂ)
        (coPoissonSchwartzEnergyTranslation (-Real.log a) test) := by
  change l2Read test (ContinuousChannels.channel 1 a value) = _
  simp only [ContinuousChannels.channel, one_mul, map_smul, smul_eq_mul]
  exact congrArg ((Real.sqrt a : ℂ)⁻¹ * ·) (OriginalRieszFiniteResponse.original_read value test (Real.log a))

/-- The original L¹ position Euler equation is consumed on each actual reverse channel. -/
theorem original_euler (coordinate : BurnolCompletedMellinCoordinate) (a : ℝ) (test : SchwartzMap ℝ ℂ) :
    read coordinate a (eulerCotest test) = -(star coordinate.value - 1 / 2) * read coordinate a test +
      Kernel.A coordinate * (ContinuousChannels.channel 1 a (burnolQuarterZeroExtension
        (Response.v : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * (ContinuousChannels.channel 1 a (burnolQuarterZeroExtension
        (Response.u : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test +
      Kernel.A coordinate * DualEuler.edgeChannel a test := by
  rw [read, eulerCotest_action, ← euler_read, PositionEuler.original_euler]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  rw [l2_channel_read, l2_channel_read, read, DualEuler.edgeChannel]
  ring

theorem source_raw_read (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    PositionEuler.source coordinate test = ∫ x : ℝ, PositionCounting.seedRaw coordinate x * test x := by
  rw [PositionEuler.source, Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(memLp_one_iff_integrable.mpr (PositionEuler.seed_integrable coordinate)).coeFn_toLp] with x same
  rw [same]
  simp only [smul_eq_mul, mul_comm]

private theorem inverse_translation (a : ℝ) (positive : 0 < a) (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    coPoissonSchwartzEnergyTranslation (-Real.log a) test x = (Real.sqrt a : ℂ)⁻¹ * test (x / a) := by
  have half (h : ℝ) : (Real.exp h : ℂ) ^ (1 / 2 : ℂ) = (Real.exp (h / 2) : ℂ) := by
    calc
      _ = ((Real.exp h ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
        symm
        convert Complex.ofReal_cpow (Real.exp_pos h).le (1 / 2 : ℝ) using 1
        norm_num
      _ = _ := by
        rw [Real.rpow_def_of_pos (Real.exp_pos h), Real.log_exp]
        exact congrArg (fun x : ℝ => (Real.exp x : ℂ)) (by ring : h * (1 / 2) = h / 2)
  have squareRoot : Real.sqrt a = Real.exp (Real.log a / 2) := by rw [Real.exp_half, Real.exp_log positive]
  change (Real.exp (-Real.log a) : ℂ) ^ (1 / 2 : ℂ) * test (Real.exp (-Real.log a) * x) = _
  rw [half, neg_div, Real.exp_neg, ← squareRoot, Complex.ofReal_inv, Real.exp_neg, Real.exp_log positive]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

theorem raw_read (coordinate : BurnolCompletedMellinCoordinate) (a : ℝ) (positive : 0 < a)
    (test : SchwartzMap ℝ ℂ) :
    read coordinate a test = ∫ x : ℝ, PositionCounting.seedRaw coordinate (a * x) * test x := by
  rw [read, source_raw_read]
  have translate : (∫ x : ℝ, PositionCounting.seedRaw coordinate x *
      coPoissonSchwartzEnergyTranslation (-Real.log a) test x) =
      (Real.sqrt a : ℂ)⁻¹ * ∫ x : ℝ, PositionCounting.seedRaw coordinate x * test (x / a) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [inverse_translation a positive test x]
    ring
  have scaled := Measure.integral_comp_mul_left
    (fun x : ℝ => PositionCounting.seedRaw coordinate x * test (x / a)) a
  simp only [mul_div_cancel_left₀ _ positive.ne', abs_inv, abs_of_pos positive, Complex.real_smul,
    Complex.ofReal_inv] at scaled
  rw [translate, ← mul_assoc, ← pow_two, inv_pow]
  have square : (Real.sqrt a : ℂ) ^ 2 = (a : ℂ) := by exact_mod_cast Real.sq_sqrt positive.le
  rw [square]
  exact scaled.symm

private def regularBound (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  ‖GapEuler.gapMean q coordinate‖ + PositionCounting.returnBound coordinate

private theorem regular_nonnegative (coordinate : BurnolCompletedMellinCoordinate) : 0 ≤ regularBound coordinate :=
  add_nonneg (norm_nonneg _) (PositionCounting.return_bound_nonnegative coordinate)

private theorem seed_bound (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x ≠ 0) :
    ‖PositionCounting.seedRaw coordinate x‖ ≤ (1 / 2 : ℝ) * |x| ^ (-coordinate.value.re) + regularBound coordinate := by
  by_cases inside : |x| ≤ q
  · rw [PositionCounting.seedRaw, if_pos inside, positionSource]
    have bound : ‖(1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value) -
        GapEuler.gapMean q coordinate - burnolRieszReturnRaw coordinate |x|‖ ≤
        (‖(1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value)‖ +
          ‖GapEuler.gapMean q coordinate‖) + ‖burnolRieszReturnRaw coordinate |x|‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le
        ((1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value)) (GapEuler.gapMean q coordinate)) le_rfl)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr nonzero)] at bound
    simp only [neg_re, star_def, conj_re] at bound
    have returned := PositionCounting.return_bound coordinate |x| ⟨abs_nonneg x, inside⟩
    norm_num at bound
    unfold regularBound
    simp only [star_def]
    linarith
  · rw [PositionCounting.seedRaw, if_neg inside, norm_zero]
    exact add_nonneg (by positivity) (regular_nonnegative coordinate)

private theorem weighted_test_integrable (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => (|x| ^ (-coordinate.value.re) + 1) * ‖test x‖) := by
  have power : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ ((-coordinate.value.re : ℝ) : ℂ)) volume (-1) 1 :=
    intervalIntegral.intervalIntegrable_cpow' (by simp only [ofReal_re]; linarith [coordinate.belowOne])
  have localPower : IntegrableOn (fun x : ℝ => |x| ^ (-coordinate.value.re)) (symmetricInterval 1) := by
    apply ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp power.norm).congr
    filter_upwards with x
    simp only [Complex.norm_cpow_real, Complex.norm_real, Real.norm_eq_abs]
  have head := (integrable_indicator_iff (measurableSet_symmetricInterval 1)).mpr localPower
  have product := head.mul_bdd test.continuous.norm.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [norm_norm] using SchwartzMap.norm_le_seminorm ℝ test x))
  have powerMeasured : Measurable (fun x : ℝ => |x| ^ (-coordinate.value.re)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x outside
    have nonzero : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using outside
    exact (continuous_abs.continuousAt.rpow_const (Or.inl (abs_pos.mpr nonzero).ne')).continuousWithinAt
  apply (product.add (test.integrable.norm.const_mul 2)).mono'
    ((powerMeasured.add measurable_const).mul test.continuous.norm.measurable).aestronglyMeasurable
  filter_upwards with x
  change ‖(|x| ^ (-coordinate.value.re) + 1) * ‖test x‖‖ ≤
    (symmetricInterval 1).indicator (fun x : ℝ => |x| ^ (-coordinate.value.re)) x * ‖test x‖ + 2 * ‖test x‖
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases inside : x ∈ symmetricInterval 1
  · rw [indicator_of_mem inside]
    nlinarith [norm_nonneg (test x)]
  · rw [indicator_of_notMem inside]
    have large : 1 ≤ |x| := (lt_of_not_ge (fun h => inside (abs_le.mp h))).le
    have powerBound := Real.rpow_le_one_of_one_le_of_nonpos large
      (by linarith [coordinate.rightHalf] : -coordinate.value.re ≤ 0)
    nlinarith [norm_nonneg (test x)]

private def scaleBound (coordinate : BurnolCompletedMellinCoordinate) (a : ℝ) : ℝ :=
  (1 / 2 : ℝ) * a ^ (-coordinate.value.re) + regularBound coordinate

private theorem scale_integrable (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    IntegrableOn (scaleBound coordinate) (Ioc 0 (N : ℝ)) := by
  have power : IntervalIntegrable (fun a : ℝ => a ^ (-coordinate.value.re)) volume 0 (N : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith [coordinate.belowOne])
  have actual := power.def'
  rw [uIoc_of_le (Nat.cast_nonneg N)] at actual
  exact (actual.const_mul (1 / 2)).add (integrableOn_const (by simp))

/-- Full positive scales are absolutely integrable after the actual Schwartz test is applied. -/
theorem joint_integrable (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (test : SchwartzMap ℝ ℂ) :
    Integrable (fun point : ℝ × ℝ => PositionCounting.seedRaw coordinate (point.1 * point.2) * test point.2)
      ((volume.restrict (Ioc 0 (N : ℝ))).prod volume) := by
  apply ((scale_integrable coordinate N).mul_prod (weighted_test_integrable coordinate test)).mono'
    (((PositionCounting.seed_measurable coordinate).comp (by fun_prop)).mul
      (test.continuous.measurable.comp measurable_snd)).aestronglyMeasurable
  have located : ∀ᵐ point : ℝ × ℝ ∂((volume.restrict (Ioc 0 (N : ℝ))).prod volume),
      point.1 ∈ Ioc 0 (N : ℝ) ∧ point.2 ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_Ioc.preimage measurable_fst).inter
      ((measurableSet_singleton (0 : ℝ)).compl.preimage measurable_snd))).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
    filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
    exact ⟨inside, nonzero⟩
  filter_upwards [located] with point located
  have positive : 0 < point.1 := located.1.1
  have nonzero : point.2 ≠ 0 := located.2
  have bound := seed_bound coordinate (point.1 * point.2) (mul_ne_zero positive.ne' nonzero)
  rw [abs_mul, abs_of_pos positive, Real.mul_rpow positive.le (abs_nonneg point.2)] at bound
  change ‖PositionCounting.seedRaw coordinate (point.1 * point.2) * test point.2‖ ≤ _
  rw [norm_mul]
  have enlarged : ‖PositionCounting.seedRaw coordinate (point.1 * point.2)‖ ≤
      scaleBound coordinate point.1 * (|point.2| ^ (-coordinate.value.re) + 1) := by
    unfold scaleBound
    nlinarith [regular_nonnegative coordinate, Real.rpow_nonneg positive.le (-coordinate.value.re),
      Real.rpow_nonneg (abs_nonneg point.2) (-coordinate.value.re)]
  exact (mul_le_mul_of_nonneg_right enlarged (norm_nonneg _)).trans_eq (by ring)

theorem channel_product_integrable (coordinate : BurnolCompletedMellinCoordinate) (a : ℝ)
    (positive : 0 < a) (test : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => PositionCounting.seedRaw coordinate (a * x) * test x) := by
  have scaled := (integrable_comp_mul_left_iff (PositionCounting.seedRaw coordinate) positive.ne').mpr
    (PositionEuler.seed_integrable coordinate)
  exact scaled.mul_bdd test.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => SchwartzMap.norm_le_seminorm ℝ test x))

theorem read_integrable (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (test : SchwartzMap ℝ ℂ) :
    IntegrableOn (fun a => read coordinate a test) (Ioc 0 (N : ℝ)) := by
  apply (joint_integrable coordinate N test).integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a located
  exact (raw_read coordinate a located.1 test).symm

/-- Actual weighted Fubini identifies the original finite raw with its whole scalar programme. -/
theorem raw_programme (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, PositionCounting.raw coordinate N x * test x) =
      (∑ n ∈ Finset.Ico 1 N, read coordinate (n : ℝ) test) -
      ∫ a : ℝ in Ioc 0 (N : ℝ), read coordinate a test := by
  have term (n : ℕ) (inside : n ∈ Finset.Ico 1 N) :
      Integrable (fun x : ℝ => PositionCounting.seedRaw coordinate ((n : ℝ) * x) * test x) :=
    channel_product_integrable coordinate n (by exact_mod_cast (Finset.mem_Ico.mp inside).1) test
  have joint := joint_integrable coordinate N test
  calc
    _ = ∫ x : ℝ, (∑ n ∈ Finset.Ico 1 N, PositionCounting.seedRaw coordinate ((n : ℝ) * x) * test x) -
        ∫ a : ℝ in Ioc 0 (N : ℝ), PositionCounting.seedRaw coordinate (a * x) * test x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [PositionCounting.raw, sub_mul, Finset.sum_mul, integral_mul_const]
    _ = (∑ n ∈ Finset.Ico 1 N, ∫ x : ℝ, PositionCounting.seedRaw coordinate ((n : ℝ) * x) * test x) -
        ∫ a : ℝ in Ioc 0 (N : ℝ), ∫ x : ℝ, PositionCounting.seedRaw coordinate (a * x) * test x := by
      rw [integral_sub (integrable_finsetSum _ term) joint.integral_prod_right,
        integral_finsetSum _ term, ← integral_integral_swap joint]
    _ = _ := by
      congr 1
      · exact Finset.sum_congr rfl (fun n inside => (raw_read coordinate n
          (by exact_mod_cast (Finset.mem_Ico.mp inside).1) test).symm)
      · apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with a located
        exact (raw_read coordinate a located.1 test).symm

private theorem l2_programme (N : ℕ) (value : BurnolL2) (test : SchwartzMap ℝ ℂ) :
    (DualSource.source N value : TemperedDistribution ℝ ℂ) test =
      (∑ n ∈ Finset.Ico 1 N, (ContinuousChannels.channel 1 (n : ℝ) value : TemperedDistribution ℝ ℂ) test) -
      ∫ a : ℝ in Ioc 0 (N : ℝ), (ContinuousChannels.channel 1 a value : TemperedDistribution ℝ ℂ) test := by
  change l2Read test (DualSource.source N value) = _
  rw [DualSource.source, map_sub, map_sum,
    ← (l2Read test).integral_comp_comm (ContinuousChannels.channel_integrable 1 N value)]
  rfl

/-- Complete same-N scalar Euler, generated from the original a source before taking any limit. -/
theorem finite_euler (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, PositionCounting.raw coordinate N x * eulerCotest test x) =
      -(star coordinate.value - 1 / 2) * (∫ x : ℝ, PositionCounting.raw coordinate N x * test x) +
      Kernel.A coordinate * (DualSource.source N (burnolQuarterZeroExtension
        (Response.v : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * (DualSource.source N (burnolQuarterZeroExtension
        (Response.u : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test +
      Kernel.A coordinate * DualEuler.edgeProgramme N test := by
  have first := (read_integrable coordinate N test).const_mul (-(star coordinate.value - 1 / 2))
  have second := ((l2Read test).integrable_comp (ContinuousChannels.channel_integrable 1 N
    (burnolQuarterZeroExtension (Response.v : BurnolQuarterIntervalL2)))).const_mul (Kernel.A coordinate)
  have third := ((l2Read test).integrable_comp (ContinuousChannels.channel_integrable 1 N
    (burnolQuarterZeroExtension (Response.u : BurnolQuarterIntervalL2)))).const_mul (Kernel.beta coordinate)
  have fourth := ((DualEuler.edgeChannel_full_integrable test).mono_set
    (show Ioc (0 : ℝ) (N : ℝ) ⊆ Ioi 0 from Ioc_subset_Ioi_self)).const_mul (Kernel.A coordinate)
  rw [raw_programme, raw_programme, l2_programme, l2_programme]
  simp_rw [original_euler]
  change (∑ n ∈ Finset.Ico 1 N, (-(star coordinate.value - 1 / 2) * read coordinate (n : ℝ) test +
      Kernel.A coordinate * l2Read test (ContinuousChannels.channel 1 (n : ℝ) (burnolQuarterZeroExtension
        (Response.v : BurnolQuarterIntervalL2))) -
      Kernel.beta coordinate * l2Read test (ContinuousChannels.channel 1 (n : ℝ) (burnolQuarterZeroExtension
        (Response.u : BurnolQuarterIntervalL2))) + Kernel.A coordinate * DualEuler.edgeChannel (n : ℝ) test)) -
    (∫ a : ℝ in Ioc 0 (N : ℝ), -(star coordinate.value - 1 / 2) * read coordinate a test +
      Kernel.A coordinate * l2Read test (ContinuousChannels.channel 1 a (burnolQuarterZeroExtension
        (Response.v : BurnolQuarterIntervalL2))) -
      Kernel.beta coordinate * l2Read test (ContinuousChannels.channel 1 a (burnolQuarterZeroExtension
        (Response.u : BurnolQuarterIntervalL2))) + Kernel.A coordinate * DualEuler.edgeChannel a test) = _
  have split₁ := integral_add ((first.add second).sub third) fourth
  have split₂ := integral_sub (first.add second) third
  have split₃ := integral_add first second
  simp only [Pi.add_apply, Pi.sub_apply] at split₁ split₂
  rw [split₁, split₂, split₃]
  simp only [integral_const_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, DualEuler.edgeProgramme]
  have actualRead (value : BurnolL2) : l2Read test value = (value : TemperedDistribution ℝ ℂ) test := rfl
  simp_rw [actualRead]
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.PositionChannel
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
