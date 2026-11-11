import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.JointLogConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KLogVectorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KappaConductorSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Abel.Gaussian.ClozelBurnolBoundaryGaussianHeatTest

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.KappaConductor
open Complex Filter FourierTransform MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalGamma.Source.JointLogConductor
noncomputable section
local notation "q" => (1 / 4 : ℝ)

open private heatLogCut heat_log_paired_source_limit kernel_clock_integrable kernel_clock_norm_payment kernel_clock_payment offDiagonalHeat sourceHeat sourceHeatCotest source_heat_cotest_inverse source_heat_cotest_physical source_heat_inverse_frequency tailWeight tail_weight_memLp from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KappaConductorSource
private theorem source_heat_actual_pairing (time : ℝ) (positive : 0 < time)
    (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    inner ℂ ((sourceHeatCotest time positive test).toLp 2 volume) value =
      ∫ x : ℝ, star ((𝓕⁻ test) x) * ((Real.exp (-(time * x ^ 2)) : ℝ) : ℂ) * (𝓕⁻ value) x := by
  have paired := Lp.inner_fourier_eq (𝓕⁻ ((sourceHeatCotest time positive test).toLp 2 volume)) (𝓕⁻ value)
  rw [fourier_fourierInv_eq, fourier_fourierInv_eq] at paired
  rw [paired, SchwartzMap.toLp_fourierInv_eq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(𝓕⁻ (sourceHeatCotest time positive test)).coeFn_toLp 2 volume] with x actual
  rw [actual, source_heat_cotest_inverse, SchwartzMap.pairing_apply_apply,
    source_heat_inverse_frequency, RCLike.inner_apply, starRingEnd_apply]
  change (𝓕⁻ value) x * star (((Real.exp (-(time * x ^ 2)) : ℝ) : ℂ) * (𝓕⁻ test) x) = _
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

private theorem source_kernel_tail_bound (delta x y : ℝ) (positive : 0 < delta)
    (bounded : |x| ≤ 4) (apart : delta ≤ |x - y|) :
    |x - y|⁻¹ ≤ (1 + 5 / delta) * tailWeight y := by
  have distance : 0 < |x - y| := positive.trans_le apart
  have yBound : |y| ≤ 4 + |x - y| := by
    have triangle := abs_add_le x (y - x)
    have reverse : |y - x| = |x - y| := abs_sub_comm _ _
    rw [reverse, add_sub_cancel] at triangle
    exact triangle.trans (by linarith)
  have paid : 1 + |y| ≤ (1 + 5 / delta) * |x - y| := by
    have ratio : 5 ≤ (5 / delta) * |x - y| := by
      calc
        5 = (5 / delta) * delta := by field_simp
        _ ≤ (5 / delta) * |x - y| := by gcongr
    linarith
  unfold tailWeight
  have comparison : 1 / |x - y| ≤ (1 + 5 / delta) / (1 + |y|) :=
    (div_le_div_iff₀ distance (by positivity : 0 < 1 + |y|)).mpr (by simpa only [one_mul] using paid)
  simpa only [one_div, div_eq_mul_inv, one_mul] using comparison

private def sourceTriple (test : SchwartzMap ℝ ℂ) (value : BurnolL2) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  star (test p.1.1) * value p.1.2 * (p.2 : ℂ)⁻¹ * offDiagonalHeat p.2 (p.1.1 - p.1.2)

private theorem source_triple_measured (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    AEStronglyMeasurable (sourceTriple test value) ((volume.prod volume).prod (volume.restrict (Ioi 0))) := by
  have coefficient : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      star (test p.1.1) * (p.2 : ℂ)⁻¹ * offDiagonalHeat p.2 (p.1.1 - p.1.2)) := by
    unfold offDiagonalHeat
    fun_prop
  have field : AEStronglyMeasurable (fun p : (ℝ × ℝ) × ℝ => value p.1.2)
      ((volume.prod volume).prod (volume.restrict (Ioi 0))) :=
    (Lp.aestronglyMeasurable value).comp_snd.comp_fst
  apply (coefficient.aestronglyMeasurable.mul field).congr
  filter_upwards with p
  unfold sourceTriple
  simp only [Pi.mul_apply]
  ring

private def sourceFrequencyTriple (test : SchwartzMap ℝ ℂ) (value : BurnolL2) (p : ℝ × ℝ) : ℂ :=
  star ((𝓕⁻ test) p.2) * (𝓕⁻ value) p.2 * (p.1 : ℂ)⁻¹ *
    (((Real.exp (-p.1) : ℝ) : ℂ) - ((Real.exp (-(p.2 ^ 2 * p.1)) : ℝ) : ℂ))

private theorem source_frequency_triple_integrable (N : ℕ) (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    Integrable (sourceFrequencyTriple test value)
      ((volume.restrict (Ioc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1))).prod volume) := by
  let lower : ℝ := 1 / ((N : ℝ) + 1)
  let upper : ℝ := (N : ℝ) + 1
  have lPos : 0 < lower := by dsimp [lower]; positivity
  have uPos : 0 < upper := by dsimp [upper]; positivity
  have native : LocallyIntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 0) :=
    continuous_const.locallyIntegrable.locallyIntegrableOn (Ioi 0)
  have timeInt : IntegrableOn (fun time : ℝ => 2 * time⁻¹) (Ioc lower upper) := by
    have whole := (Frullani.intervalIntegrable_inv_smul native lPos uPos).1
    simpa only [IntegrableOn, smul_eq_mul, mul_one] using whole.const_mul 2
  have frequencyInt : Integrable (fun x : ℝ => ‖(𝓕⁻ test) x‖ * ‖(𝓕⁻ value) x‖) :=
    ((𝓕⁻ test).memLp 2 volume).norm.integrable_mul (Lp.memLp (𝓕⁻ value)).norm
  have budget := timeInt.mul_prod frequencyInt
  have coefficient : Measurable (fun p : ℝ × ℝ => star ((𝓕⁻ test) p.2) * (p.1 : ℂ)⁻¹ *
      (((Real.exp (-p.1) : ℝ) : ℂ) - ((Real.exp (-(p.2 ^ 2 * p.1)) : ℝ) : ℂ))) := by fun_prop
  have measured : AEStronglyMeasurable (sourceFrequencyTriple test value)
      ((volume.restrict (Ioc lower upper)).prod volume) := by
    apply (coefficient.aestronglyMeasurable.mul (Lp.aestronglyMeasurable (𝓕⁻ value)).comp_snd).congr
    filter_upwards with p
    simp only [sourceFrequencyTriple, Pi.mul_apply]
    ring
  apply budget.mono' measured
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)] with p interval
  have positive : 0 < p.1 := lPos.trans interval.1
  have difference : ‖((Real.exp (-p.1) : ℝ) : ℂ) - ((Real.exp (-(p.2 ^ 2 * p.1)) : ℝ) : ℂ)‖ ≤ 2 := by
    calc
      _ ≤ ‖((Real.exp (-p.1) : ℝ) : ℂ)‖ + ‖((Real.exp (-(p.2 ^ 2 * p.1)) : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ = Real.exp (-p.1) + Real.exp (-(p.2 ^ 2 * p.1)) := by
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ 2 := by
        have first := Real.exp_le_one_iff.mpr (neg_nonpos.mpr positive.le)
        have second := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (sq_nonneg p.2) positive.le))
        linarith
  simp only [sourceFrequencyTriple, norm_mul, norm_star, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  calc
    _ ≤ ‖(𝓕⁻ test) p.2‖ * ‖(𝓕⁻ value) p.2‖ * p.1⁻¹ * 2 := by gcongr
    _ = _ := by ring

private theorem source_cut_frequency_clock (N : ℕ) (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    (∫ frequency : ℝ, star ((𝓕⁻ test) frequency) * (heatLogCut N frequency : ℂ) * (𝓕⁻ value) frequency) =
      (1 / 2 : ℂ) * ∫ time : ℝ in Ioc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1),
        ∫ frequency : ℝ, sourceFrequencyTriple test value (time, frequency) := by
  let lower : ℝ := 1 / ((N : ℝ) + 1)
  let upper : ℝ := (N : ℝ) + 1
  have direction : lower ≤ upper := by
    have source : 1 ≤ upper := by dsimp [upper]; have nonnegative := Nat.cast_nonneg (α := ℝ) N; linarith
    have inverse : lower ≤ 1 := by simpa only [lower, upper, div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) source
    exact inverse.trans source
  have oneRead (frequency : ℝ) :
      star ((𝓕⁻ test) frequency) * (heatLogCut N frequency : ℂ) * (𝓕⁻ value) frequency =
        (1 / 2 : ℂ) * ∫ time : ℝ in Ioc lower upper, sourceFrequencyTriple test value (time, frequency) := by
    unfold heatLogCut
    rw [Complex.ofReal_mul, intervalIntegral.integral_of_le direction, ← integral_complex_ofReal]
    calc
      _ = (1 / 2 : ℂ) * ∫ time : ℝ in Ioc lower upper,
          star ((𝓕⁻ test) frequency) * ((time⁻¹ * (Real.exp (-time) - Real.exp (-(frequency ^ 2 * time))) : ℝ) : ℂ) *
            (𝓕⁻ value) frequency := by
        rw [integral_mul_const, integral_const_mul]
        push_cast
        ring
      _ = _ := by
        apply congrArg ((1 / 2 : ℂ) * ·)
        apply integral_congr_ae
        filter_upwards with time
        simp only [sourceFrequencyTriple, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sub]
        ring
  rw [integral_congr_ae (Eventually.of_forall oneRead), integral_const_mul]
  apply congrArg ((1 / 2 : ℂ) * ·)
  exact (integral_integral_swap (f := fun time frequency : ℝ => sourceFrequencyTriple test value (time, frequency))
    (μ := volume.restrict (Ioc lower upper)) (ν := volume) (source_frequency_triple_integrable N test value)).symm

private theorem source_inverse_pairing (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    inner ℂ (test.toLp 2 volume) value = ∫ x : ℝ, star ((𝓕⁻ test) x) * (𝓕⁻ value) x := by
  have paired := Lp.inner_fourier_eq (𝓕⁻ (test.toLp 2 volume)) (𝓕⁻ value)
  rw [fourier_fourierInv_eq, fourier_fourierInv_eq] at paired
  rw [paired, SchwartzMap.toLp_fourierInv_eq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(𝓕⁻ test).coeFn_toLp 2 volume] with x native
  rw [native, RCLike.inner_apply, starRingEnd_apply]
  ring

private theorem source_inverse_product_integrable (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    Integrable (fun x : ℝ => star ((𝓕⁻ test) x) * (𝓕⁻ value) x) := by
  apply (L2.integrable_inner (𝕜 := ℂ) ((𝓕⁻ test).toLp 2 volume) (𝓕⁻ value)).congr
  filter_upwards [(𝓕⁻ test).coeFn_toLp 2 volume] with x native
  rw [native, RCLike.inner_apply, starRingEnd_apply]
  ring

private theorem source_heat_product_integrable (time : ℝ) (positive : 0 < time)
    (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    Integrable (fun x : ℝ => star ((𝓕⁻ test) x) * ((Real.exp (-(time * x ^ 2)) : ℝ) : ℂ) * (𝓕⁻ value) x) := by
  apply (L2.integrable_inner (𝕜 := ℂ) ((𝓕⁻ (sourceHeatCotest time positive test)).toLp 2 volume) (𝓕⁻ value)).congr
  filter_upwards [(𝓕⁻ (sourceHeatCotest time positive test)).coeFn_toLp 2 volume] with x native
  rw [native, source_heat_cotest_inverse, SchwartzMap.pairing_apply_apply,
    source_heat_inverse_frequency, RCLike.inner_apply, starRingEnd_apply]
  change (𝓕⁻ value) x * star (((Real.exp (-(time * x ^ 2)) : ℝ) : ℂ) * (𝓕⁻ test) x) = _
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

private theorem source_frequency_clock_point (time : ℝ) (positive : 0 < time)
    (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    (∫ frequency : ℝ, sourceFrequencyTriple test value (time, frequency)) =
      (time : ℂ)⁻¹ * (((Real.exp (-time) : ℝ) : ℂ) * inner ℂ (test.toLp 2 volume) value -
        inner ℂ ((sourceHeatCotest time positive test).toLp 2 volume) value) := by
  have shape : (fun frequency : ℝ => sourceFrequencyTriple test value (time, frequency)) =
      fun frequency : ℝ => (time : ℂ)⁻¹ *
        (((Real.exp (-time) : ℝ) : ℂ) * (star ((𝓕⁻ test) frequency) * (𝓕⁻ value) frequency) -
          star ((𝓕⁻ test) frequency) * ((Real.exp (-(time * frequency ^ 2)) : ℝ) : ℂ) * (𝓕⁻ value) frequency) := by
    funext frequency
    unfold sourceFrequencyTriple
    rw [mul_comm (frequency ^ 2) time]
    ring
  rw [shape, integral_const_mul, integral_sub ((source_inverse_product_integrable test value).const_mul _)
      (source_heat_product_integrable time positive test value), integral_const_mul,
    ← source_inverse_pairing, ← source_heat_actual_pairing]

private theorem full_half_fold (f : ℝ → ℂ) (whole : Integrable f) :
    (∫ t : ℝ in symmetricInterval q, f t) = ∫ t : ℝ in Ioc 0 q, f t + f (-t) := by
  have first := whole.integrableOn (s := Ioc (-q) 0)
  have second := whole.integrableOn (s := Ioc 0 q)
  have flipped : IntegrableOn (fun t : ℝ => f (-t)) (Ioc 0 q) := by
    simpa only [Function.comp_def] using (negMeasurePreserving.integrable_comp_of_integrable whole).integrableOn (s := Ioc 0 q)
  have split := setIntegral_union (Ioc_disjoint_Ioc_of_le (a := -q) (b := (0 : ℝ))
    (c := 0) (d := q) le_rfl) measurableSet_Ioc first second
  rw [Ioc_union_Ioc_eq_Ioc (by norm_num : -q ≤ (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ q)] at split
  have reflected : (∫ t : ℝ in Ioc (-q) 0, f t) = ∫ t : ℝ in Ioc 0 q, f (-t) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : -q ≤ (0 : ℝ)),
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q)]
    simpa only [neg_zero] using (intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := q)).symm
  change (∫ t : ℝ in Icc (-q) q, f t) = _
  rw [integral_Icc_eq_integral_Ioc, split, reflected, integral_add second flipped]
  ring

private theorem compact_profile_pairing (value head : BurnolL2) (coefficient profile : ℝ → ℂ)
    (valueRead : (value : ℝ → ℂ) =ᵐ[volume] coefficient) (headRead : (head : ℝ → ℂ) =ᵐ[volume] profile)
    (even : ∀ t, profile (-t) = profile t) (outside : ∀ t, q < |t| → profile t = 0) :
    inner ℂ value head = ∫ t : ℝ in Ioc 0 q, profile t * (star (coefficient t) + star (coefficient (-t))) := by
  let h : ℝ → ℂ := fun t => profile t * star (coefficient t)
  have actual : (fun t : ℝ => inner ℂ (value t) (head t)) =ᵐ[volume] h := by
    filter_upwards [valueRead, headRead] with t valueAt headAt
    simp only [h, valueAt, headAt, RCLike.inner_apply, starRingEnd_apply]
  have whole : Integrable h := (L2.integrable_inner (𝕜 := ℂ) value head).congr actual
  have cutoff : (∫ t : ℝ in symmetricInterval q, h t) = ∫ t : ℝ, h t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t notInside => by
      have large : q < |t| := lt_of_not_ge (fun small => notInside (abs_le.mp small))
      simp only [h, outside t large, zero_mul])
  rw [L2.inner_def, integral_congr_ae actual, ← cutoff, full_half_fold h whole]
  apply integral_congr_ae
  filter_upwards with t
  simp only [h, even, mul_add]

end
end OriginalGamma.Source.KappaConductor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
