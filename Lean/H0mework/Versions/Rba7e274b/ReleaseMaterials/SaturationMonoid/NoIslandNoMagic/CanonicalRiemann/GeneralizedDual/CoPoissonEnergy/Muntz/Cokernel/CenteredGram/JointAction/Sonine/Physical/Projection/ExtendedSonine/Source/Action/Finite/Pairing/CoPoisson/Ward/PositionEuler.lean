import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionOrigin
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionCounting
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualEuler

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.PositionEuler

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace SchwartzMap
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

private def evenSeed (f : ℝ → ℂ) (x : ℝ) : ℂ := if |x| ≤ q then f |x| else 0

private theorem evenSeed_split (f : ℝ → ℂ) :
    evenSeed f =ᵐ[volume] fun x => (Ioc 0 q).indicator f x + (Ioc 0 q).indicator f (-x) := by
  filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
  unfold evenSeed
  by_cases positive : 0 < x
  · rw [abs_of_pos positive, indicator_of_notMem (show -x ∉ Ioc 0 q by intro h; linarith [h.1]), add_zero]
    by_cases inside : x ≤ q
    · rw [if_pos inside, indicator_of_mem (show x ∈ Ioc 0 q from ⟨positive, inside⟩)]
    · rw [if_neg inside, indicator_of_notMem (fun h => inside h.2)]
  · have negative : x < 0 := lt_of_le_of_ne (le_of_not_gt positive) nonzero
    rw [abs_of_neg negative, indicator_of_notMem (show x ∉ Ioc 0 q by intro h; linarith [h.1]), zero_add]
    by_cases inside : -x ≤ q
    · rw [if_pos inside, indicator_of_mem (show -x ∈ Ioc 0 q from ⟨by linarith, inside⟩)]
    · rw [if_neg inside, indicator_of_notMem (fun h => inside h.2)]

private theorem evenSeed_integrable (f : ℝ → ℂ) (integrable : IntegrableOn f (Ioc 0 q)) :
    Integrable (evenSeed f) := by
  have positive := (integrable_indicator_iff measurableSet_Ioc).mpr integrable
  have negative := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable positive
  exact (positive.add negative).congr (evenSeed_split f).symm

private theorem test_product_integrable (f : ℝ → ℂ) (integrable : Integrable f)
    (test : SchwartzMap ℝ ℂ) : Integrable (fun x => f x * test x) :=
  integrable.mul_bdd test.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => SchwartzMap.norm_le_seminorm ℝ test x))

private theorem positive_product_integrable (f : ℝ → ℂ) (integrable : IntegrableOn f (Ioc 0 q))
    (test : SchwartzMap ℝ ℂ) :
    IntegrableOn (fun x => f x * (test x + test (-x))) (Ioc 0 q) :=
  integrable.mul_continuousOn_of_subset
    (test.continuous.add (test.continuous.comp continuous_neg)).continuousOn
    measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self

private theorem evenSeed_integral (f : ℝ → ℂ) (integrable : IntegrableOn f (Ioc 0 q))
    (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, evenSeed f x * test x) = ∫ x : ℝ in Ioc 0 q, f x * (test x + test (-x)) := by
  let p := (Ioc 0 q).indicator f
  have positive : Integrable p := (integrable_indicator_iff measurableSet_Ioc).mpr integrable
  have negative := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable positive
  have pTest := test_product_integrable p positive test
  have nTest := test_product_integrable (fun x => p (-x)) negative test
  have split : (∫ x : ℝ, evenSeed f x * test x) =
      (∫ x : ℝ, p x * test x) + ∫ x : ℝ, p (-x) * test x := by
    rw [← integral_add pTest nTest]
    apply integral_congr_ae
    filter_upwards [evenSeed_split f] with x source
    rw [source]
    ring
  have reflection := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp measurableEmbedding_neg
    (fun x : ℝ => p x * test (-x))
  simp only [neg_neg] at reflection
  rw [split, reflection]
  have forward : (∫ x : ℝ, p x * test x) = ∫ x : ℝ in Ioc 0 q, f x * test x := by
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with x
    exact (indicator_mul_left (Ioc 0 q) f (fun x => test x)).symm
  have backward : (∫ x : ℝ, p x * test (-x)) = ∫ x : ℝ in Ioc 0 q, f x * test (-x) := by
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with x
    exact (indicator_mul_left (Ioc 0 q) f (fun x => test (-x))).symm
  rw [forward, backward, ← integral_add (f := fun x : ℝ => f x * test x)
    (g := fun x : ℝ => f x * test (-x))
    (integrable.mul_continuousOn_of_subset test.continuous.continuousOn measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self)
    (integrable.mul_continuousOn_of_subset (test.continuous.comp continuous_neg).continuousOn
      measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self)]
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem seed_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable (PositionCounting.seedRaw coordinate) :=
  evenSeed_integrable _ (PositionSource.integrable coordinate)

/-- This source is the original even compact L¹ a, not an L² realization. -/
def source (coordinate : BurnolCompletedMellinCoordinate) : TemperedDistribution ℝ ℂ :=
  Lp.toTemperedDistributionCLM ℂ volume 1
    ((memLp_one_iff_integrable.mpr (seed_integrable coordinate)).toLp (PositionCounting.seedRaw coordinate))

theorem source_read (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    source coordinate test =
      ∫ x : ℝ in Ioc 0 q, positionSource coordinate x * (test x + test (-x)) := by
  unfold source
  rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
  have raw := (memLp_one_iff_integrable.mpr (seed_integrable coordinate)).coeFn_toLp
  calc
    _ = ∫ x : ℝ, PositionCounting.seedRaw coordinate x * test x := by
      apply integral_congr_ae
      filter_upwards [raw] with x same
      rw [same]
      simp only [smul_eq_mul, mul_comm]
    _ = _ := evenSeed_integral _ (PositionSource.integrable coordinate) test

private theorem extension_read (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw) (even : ∀ x, raw (-x) = raw x)
    (integrable : IntegrableOn raw (Ioc 0 q)) (test : SchwartzMap ℝ ℂ) :
    (burnolQuarterZeroExtension state : TemperedDistribution ℝ ℂ) test =
      ∫ x : ℝ in Ioc 0 q, raw x * (test x + test (-x)) := by
  rw [Translator.ForcingCutoff.zeroExtension_pairing state raw represents test,
    ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  rw [← evenSeed_integral raw integrable test]
  apply integral_congr_ae
  filter_upwards with x
  have incidence : x ∈ Icc (-q) q ↔ |x| ≤ q := abs_le.symm
  have absolute : raw |x| = raw x := by
    rcases le_total 0 x with positive | negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative, even]
  by_cases inside : x ∈ Icc (-q) q
  · rw [indicator_of_mem inside, evenSeed, if_pos (incidence.mp inside), absolute]
  · rw [indicator_of_notMem inside, evenSeed, if_neg (fun h => inside (incidence.mpr h)), zero_mul]

private def powerRead (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ x : ℝ in Ioc 0 q, (1 / 2 : ℂ) * (x : ℂ) ^ (-star coordinate.value) * (test x + test (-x))

private def constantRead (test : SchwartzMap ℝ ℂ) : ℂ :=
  (burnolQuarterZeroExtension (intervalConstant q) : TemperedDistribution ℝ ℂ) test

private theorem power_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-star coordinate.value)) volume 0 q := by
  apply intervalIntegral.intervalIntegrable_cpow'
  simp only [neg_re, star_def, conj_re]
  linarith [coordinate.belowOne]

private theorem source_split (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    source coordinate test = powerRead coordinate test -
      GapEuler.gapMean q coordinate * constantRead test -
      (burnolQuarterZeroExtension (Constructor.returnState coordinate : BurnolQuarterIntervalL2) :
        TemperedDistribution ℝ ℂ) test := by
  have p : IntegrableOn (fun x : ℝ => (1 / 2 : ℂ) * (x : ℂ) ^ (-star coordinate.value)) (Ioc 0 q) :=
    (power_integrable coordinate).1.const_mul (1 / 2 : ℂ)
  have c : IntegrableOn (fun _ : ℝ => GapEuler.gapMean q coordinate) (Ioc 0 q) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have r : IntegrableOn (burnolRieszReturnRaw coordinate) (Ioc 0 q) :=
    (burnolRieszReturnRaw_continuous coordinate).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have multiplier : ContinuousOn (fun x : ℝ => test x + test (-x)) (Icc 0 q) :=
    (test.continuous.add (test.continuous.comp continuous_neg)).continuousOn
  have cRead : constantRead test = ∫ x : ℝ in Ioc 0 q, test x + test (-x) := by
    unfold constantRead
    have original := extension_read (intervalConstant q) (fun _ => (1 : ℂ)) (intervalConstant_coeFn q)
      (fun _ => rfl) (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self) test
    simpa only [one_mul] using original
  rw [source_read, extension_read _ _ (Constructor.returnState_read coordinate)
      (return_raw_even coordinate) r test, cRead]
  have first := p.mul_continuousOn_of_subset multiplier measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  have second := c.mul_continuousOn_of_subset multiplier measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  have third := r.mul_continuousOn_of_subset multiplier measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  change (∫ x : ℝ in Ioc 0 q, ((1 / 2 : ℂ) * (x : ℂ) ^ (-star coordinate.value) -
      GapEuler.gapMean q coordinate - burnolRieszReturnRaw coordinate x) * (test x + test (-x))) = _
  simp_rw [sub_mul]
  have firstSplit := integral_sub first second
  have fullSplit := integral_sub (first.sub second) third
  simp only [Pi.sub_apply] at firstSplit fullSplit
  rw [fullSplit, firstSplit, integral_const_mul]
  rfl

private def eulerCotest (test : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  -(1 / 2 : ℂ) • test - SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
    (SchwartzMap.derivCLM ℂ ℂ test)

private theorem eulerCotest_apply (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    eulerCotest test x = -(1 / 2 : ℂ) * test x - (x : ℂ) * deriv test x := by
  have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [eulerCotest, sub_apply, smul_apply, SchwartzMap.smulLeftCLM_apply growth,
    SchwartzMap.derivCLM_apply, smul_eq_mul]

private theorem euler_read (value : TemperedDistribution ℝ ℂ) (test : SchwartzMap ℝ ℂ) :
    GapEuler.euler value test = value (eulerCotest test) := by
  rw [Dilation.euler_test]
  simp only [eulerCotest, map_sub, map_smul, smul_eq_mul]

private theorem symmetric_derivative (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => test y + test (-y)) (deriv test x - deriv test (-x)) x := by
  have reflected := (test.hasDerivAt (-x)).scomp x (hasDerivAt_id x).neg
  convert! (test.hasDerivAt x).add reflected using 1
  simp only [Complex.real_smul, ofReal_neg, ofReal_one, neg_one_mul, sub_eq_add_neg]

private theorem weighted_power (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0 < x) :
    (x : ℂ) ^ (-star coordinate.value) * (x : ℂ) = (x : ℂ) ^ (1 - star coordinate.value) := by
  rw [show 1 - star coordinate.value = -star coordinate.value + 1 by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'), cpow_one]

private theorem power_euler (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    powerRead coordinate (eulerCotest test) =
      -(star coordinate.value - 1 / 2) * powerRead coordinate test -
      (1 / 2 : ℂ) * (q : ℂ) ^ (1 - star coordinate.value) * (test q + test (-q)) := by
  let P : ℝ → ℂ := fun x => (x : ℂ) ^ (-star coordinate.value) * (test x + test (-x))
  let Q : ℝ → ℂ := fun x => (x : ℂ) ^ (1 - star coordinate.value) * (deriv test x - deriv test (-x))
  have testContinuous : Continuous (fun x : ℝ => test x + test (-x)) :=
    test.continuous.add (test.continuous.comp continuous_neg)
  have slopeContinuous : Continuous (fun x : ℝ => deriv test x - deriv test (-x)) :=
    (SchwartzMap.derivCLM ℂ ℂ test).continuous.sub
      ((SchwartzMap.derivCLM ℂ ℂ test).continuous.comp continuous_neg)
  have intP : IntervalIntegrable P volume 0 q :=
    (power_integrable coordinate).mul_continuousOn testContinuous.continuousOn
  have intQ : IntervalIntegrable Q volume 0 q :=
    ((PositionOrigin.weighted_power_continuous coordinate).mul slopeContinuous).intervalIntegrable _ _
  have primitive : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (1 - star coordinate.value) *
      (test x + test (-x))) (Icc 0 q) :=
    ((PositionOrigin.weighted_power_continuous coordinate).mul testContinuous).continuousOn
  have derivative (x : ℝ) (inside : x ∈ Ioo 0 q) :
      HasDerivAt (fun x : ℝ => (x : ℂ) ^ (1 - star coordinate.value) * (test x + test (-x)))
        ((1 - star coordinate.value) * P x + Q x) x := by
    have power := (Complex.hasStrictDerivAt_cpow_const (c := 1 - star coordinate.value)
      (Complex.ofReal_mem_slitPlane.mpr inside.1)).hasDerivAt.comp_ofReal
    convert! power.mul (symmetric_derivative test x) using 1
    rw [show 1 - star coordinate.value - 1 = -star coordinate.value by ring]
    dsimp only [P, Q]
    ring
  have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ q) primitive derivative
    ((intP.const_mul (1 - star coordinate.value)).add intQ)
  rw [intervalIntegral.integral_add (intP.const_mul (1 - star coordinate.value)) intQ,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q), ofReal_zero,
    zero_cpow (PositionOrigin.power_exponent_nonzero coordinate), zero_mul, sub_zero] at actual
  have original : powerRead coordinate test = (1 / 2 : ℂ) * ∫ x : ℝ in Ioc 0 q, P x := by
    rw [powerRead, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [P]
    ring
  have cotest : powerRead coordinate (eulerCotest test) =
      -(1 / 4 : ℂ) * (∫ x : ℝ in Ioc 0 q, P x) - (1 / 2 : ℂ) * ∫ x : ℝ in Ioc 0 q, Q x := by
    unfold powerRead
    have input : ∀ x ∈ Ioc 0 q,
        (1 / 2 : ℂ) * (x : ℂ) ^ (-star coordinate.value) *
          (eulerCotest test x + eulerCotest test (-x)) = -(1 / 4 : ℂ) * P x - (1 / 2 : ℂ) * Q x := by
      intro x inside
      rw [eulerCotest_apply, eulerCotest_apply]
      dsimp only [P, Q]
      rw [← weighted_power coordinate x inside.1, ofReal_neg]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc input,
      integral_sub (intP.1.const_mul (-(1 / 4 : ℂ))) (intQ.1.const_mul (1 / 2 : ℂ)),
      integral_const_mul, integral_const_mul]
  rw [cotest, original]
  linear_combination -actual / 2

private theorem constant_read (test : SchwartzMap ℝ ℂ) :
    constantRead test = ∫ x : ℝ in Ioc (-q) q, test x := by
  unfold constantRead
  simpa only [one_mul] using Translator.ForcingCutoff.zeroExtension_pairing
    (intervalConstant q) (fun _ => (1 : ℂ)) (intervalConstant_coeFn q) test

private theorem constant_euler (test : SchwartzMap ℝ ℂ) :
    constantRead (eulerCotest test) = -(1 / 2 : ℂ) * constantRead test - GapEuler.edge q test := by
  have edge := DualEuler.edgeChannel_derivative 1 (by norm_num) test
  simp only [DualEuler.edgeChannel, Real.sqrt_one, ofReal_one, inv_one, Real.log_one, neg_zero,
    coPoissonSchwartzEnergyTranslation_zero, one_mul, div_one] at edge
  rw [constant_read, constant_read, edge,
    setIntegral_congr_fun measurableSet_Ioc (fun x _ => eulerCotest_apply test x),
    integral_sub (f := fun x : ℝ => -(1 / 2 : ℂ) * test x)
      (g := fun x : ℝ => (x : ℂ) * deriv test x)
      ((test.continuous.const_mul (-(1 / 2 : ℂ))).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((Complex.continuous_ofReal.mul (SchwartzMap.derivCLM ℂ ℂ test).continuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self),
    integral_const_mul]

private theorem original_return_equation (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (burnolQuarterZeroExtension (Constructor.returnState coordinate : BurnolQuarterIntervalL2) :
      TemperedDistribution ℝ ℂ) =
      -(star coordinate.value - 1 / 2) •
        (burnolQuarterZeroExtension (Constructor.returnState coordinate : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) -
      Kernel.A coordinate • (burnolQuarterZeroExtension (Response.v : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) +
      Kernel.beta coordinate • (burnolQuarterZeroExtension (Response.u : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) -
      burnolRieszReturnRaw coordinate q • GapEuler.edge q := by
  rw [Euler.return_euler, Euler.returnEuler_eq]
  change Lp.toTemperedDistributionCLM ℂ volume 2 (burnolQuarterZeroExtension _) - _ = _
  simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, map_add, map_sub, map_smul]
  rfl

/-- The original position source supplies the complementary full Euler equation,
including its actual endpoint and the complete mean-corrected edge. -/
theorem original_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (source coordinate) =
      -(star coordinate.value - 1 / 2) • source coordinate +
      Kernel.A coordinate • (burnolQuarterZeroExtension (Response.v : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) -
      Kernel.beta coordinate • (burnolQuarterZeroExtension (Response.u : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) +
      Kernel.A coordinate • GapEuler.edge q := by
  ext test
  rw [euler_read, source_split, power_euler, constant_euler, ← euler_read,
    original_return_equation]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
  rw [source_split]
  have edge : GapEuler.edge q test = (q : ℂ) * (test q + test (-q)) - constantRead test := by
    rw [Translator.ForcingCutoff.edge_pairing, constant_read]
  have power : (1 / 2 : ℂ) * (q : ℂ) ^ (1 - star coordinate.value) =
      (q : ℂ) * ((1 - star coordinate.value) * GapEuler.gapMean q coordinate) := by
    rw [GapEuler.gapMean_primitive q (by norm_num), ← weighted_power coordinate q (by norm_num)]
    ring
  rw [edge, power, Kernel.A]
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.PositionEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
