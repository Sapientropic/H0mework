import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusTemperedSource
import H0mework.Arithmetic.RieszForcing.Pulse
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusLocalNormalization
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource
open scoped Topology InnerProductSpace BigOperators
namespace T
export OriginalWholeDebtRJointMobiusTemperedSource
  (actual_source_growth forwardDistribution actual_forward_distribution actual_fourier_response_realization)
end T
namespace U
export OriginalWholeDebtRJointMobiusUnitSource (sourceRaw)
end U
namespace D
export OriginalWholeDebtRJointMobiusRActionSource (sourceInput)
end D
open private source_measurable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusTailGrowthSource
local notation "q" => (1 / 4 : ℝ)

def sourceKernel (test : SchwartzMap ℝ ℂ) (u : ℝ) : ℂ := ∑' n : ℕ+, test ((n : ℝ) * u)
def sourceKernelAction (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ u : ℝ, U.sourceRaw c u * sourceKernel test u

private def term (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) (n : ℕ+) (u : ℝ) : ℂ :=
  U.sourceRaw c u * test ((n : ℝ) * u)
private def outputTerm (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) (n : ℕ+) (x : ℝ) : ℂ :=
  (((n : ℕ) : ℂ)⁻¹) * U.sourceRaw c (x / (n : ℕ)) * test x

private theorem term_bound (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ)
    (C : ℝ) (nonnegative : 0 ≤ C) (bound : ∀ u : ℝ, ‖U.sourceRaw c u‖ ≤ C * (1 + |u|))
    (n : ℕ+) (u : ℝ) :
    ‖term c test n u‖ ≤ (4 * C * SchwartzMap.seminorm ℂ 4 0 test) * ((n : ℝ) ^ 4)⁻¹ * (1 + u ^ 2)⁻¹ := by
  have S : 0 ≤ SchwartzMap.seminorm ℂ 4 0 test := apply_nonneg _ _
  by_cases small : |u| ≤ (4 : ℝ)
  · unfold term
    rw [OriginalWholeDebtRJointMobiusUnitSource.actual_source_zero_window c small, zero_mul, norm_zero]
    positivity
  have large : (4 : ℝ) < |u| := lt_of_not_ge small
  have np : (0 : ℝ) < n := by exact_mod_cast n.pos
  have up : 0 < |u| := by linarith
  have decay := SchwartzMap.norm_pow_mul_le_seminorm ℂ test 4 ((n : ℝ) * u)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos np, mul_pow] at decay
  have testBound : ‖test ((n : ℝ) * u)‖ ≤ SchwartzMap.seminorm ℂ 4 0 test / ((n : ℝ) ^ 4 * |u| ^ 4) := by
    apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) ^ 4 * |u| ^ 4)).mpr
    nlinarith
  have ratio : (1 + |u|) / |u| ^ 4 ≤ 4 / (1 + u ^ 2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < |u| ^ 4) (by positivity : 0 < 1 + u ^ 2)).mpr
    have first : 1 + |u| ≤ 2 * |u| := by linarith
    have second : 1 + |u| ^ 2 ≤ 2 * |u| ^ 2 := by nlinarith
    have product := mul_le_mul first second (by positivity : 0 ≤ 1 + |u| ^ 2) (by positivity : 0 ≤ 2 * |u|)
    have power : |u| ^ 3 ≤ |u| ^ 4 := pow_le_pow_right₀ (by linarith : 1 ≤ |u|) (by decide : 3 ≤ 4)
    nlinarith [sq_abs u]
  unfold term
  rw [norm_mul]
  calc
    _ ≤ (C * (1 + |u|)) * (SchwartzMap.seminorm ℂ 4 0 test / ((n : ℝ) ^ 4 * |u| ^ 4)) :=
      mul_le_mul (bound u) testBound (norm_nonneg _) (by positivity)
    _ = (C * SchwartzMap.seminorm ℂ 4 0 test / (n : ℝ) ^ 4) * ((1 + |u|) / |u| ^ 4) := by ring
    _ ≤ (C * SchwartzMap.seminorm ℂ 4 0 test / (n : ℝ) ^ 4) * (4 / (1 + u ^ 2)) :=
      mul_le_mul_of_nonneg_left ratio (by positivity)
    _ = _ := by ring

private theorem term_integrable (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) (n : ℕ+) :
    Integrable (term c test n) volume := by
  obtain ⟨C, nonnegative, bound⟩ := T.actual_source_growth c
  have measured : AEStronglyMeasurable (term c test n) volume :=
    (source_measurable c).mul ((test.continuous.comp (by fun_prop)).aestronglyMeasurable)
  exact (integrable_inv_one_add_sq.const_mul
    ((4 * C * SchwartzMap.seminorm ℂ 4 0 test) * ((n : ℝ) ^ 4)⁻¹)).mono' measured
      (Eventually.of_forall (term_bound c test C nonnegative bound n))

private theorem term_integrals_summable (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ+ => ∫ u : ℝ, ‖term c test n u‖) := by
  obtain ⟨C, nonnegative, bound⟩ := T.actual_source_growth c
  let B := (4 * C * SchwartzMap.seminorm ℂ 4 0 test) * (∫ u : ℝ, (1 + u ^ 2)⁻¹)
  have comparison (n : ℕ+) : (∫ u : ℝ, ‖term c test n u‖) ≤ B * ((n : ℝ) ^ 4)⁻¹ := by
    have actual := integral_mono_ae (term_integrable c test n).norm
      (integrable_inv_one_add_sq.const_mul ((4 * C * SchwartzMap.seminorm ℂ 4 0 test) * ((n : ℝ) ^ 4)⁻¹))
      (Eventually.of_forall (term_bound c test C nonnegative bound n))
    rw [integral_const_mul] at actual
    dsimp only [B]
    nlinarith
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun u => norm_nonneg _)) comparison
  exact (((Real.summable_nat_pow_inv.mpr (by decide : 1 < 4)).comp_injective PNat.coe_injective).mul_left B)

private theorem output_scale (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) (n : ℕ+) :
    outputTerm c test n = fun x : ℝ => (((n : ℕ) : ℂ)⁻¹) * term c test n (x / (n : ℕ)) := by
  funext x
  have np : (n : ℝ) ≠ 0 := by exact_mod_cast n.ne_zero
  have argument : (n : ℝ) * (x / (n : ℕ)) = x := by field_simp
  unfold outputTerm term
  rw [argument]
  ring

private theorem output_integrable (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) (n : ℕ+) :
    Integrable (outputTerm c test n) volume := by
  rw [output_scale]
  exact ((term_integrable c test n).comp_div (by exact_mod_cast n.ne_zero)).const_mul _

private theorem output_integral (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) (n : ℕ+) :
    (∫ x : ℝ, outputTerm c test n x) = ∫ u : ℝ, term c test n u := by
  have np : (0 : ℝ) < n := by exact_mod_cast n.pos
  have nz : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  rw [output_scale, integral_const_mul, Measure.integral_comp_div, abs_of_pos np]
  simp only [Complex.real_smul, Complex.ofReal_natCast]
  rw [← mul_assoc, inv_mul_cancel₀ nz, one_mul]

private theorem output_norm_integral (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) (n : ℕ+) :
    (∫ x : ℝ, ‖outputTerm c test n x‖) = ∫ u : ℝ, ‖term c test n u‖ := by
  have np : (0 : ℝ) < n := by exact_mod_cast n.pos
  rw [output_scale]
  simp only [norm_mul, norm_inv, Complex.norm_natCast]
  rw [integral_const_mul, Measure.integral_comp_div (fun u : ℝ => ‖term c test n u‖) (n : ℝ), abs_of_pos np]
  simp only [smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ np.ne', one_mul]

/-- The complete original raw source itself generates the kernel action; no reciprocal mean integral is assumed. -/
theorem actual_source_kernel_action (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    sourceKernelAction c test = T.forwardDistribution c test := by
  have inputSum := term_integrals_summable c test
  have outputSum : Summable (fun n : ℕ+ => ∫ x : ℝ, ‖outputTerm c test n x‖) :=
    inputSum.congr (fun n => (output_norm_integral c test n).symm)
  rw [T.actual_forward_distribution]
  calc
    _ = ∫ u : ℝ, ∑' n : ℕ+, term c test n u := by
      unfold sourceKernelAction sourceKernel term
      apply integral_congr_ae
      filter_upwards with u
      exact (tsum_mul_left : (∑' n : ℕ+, U.sourceRaw c u * test ((n : ℝ) * u)) =
        U.sourceRaw c u * (∑' n : ℕ+, test ((n : ℝ) * u))).symm
    _ = ∑' n : ℕ+, ∫ u : ℝ, term c test n u :=
      (integral_tsum_of_summable_integral_norm (term_integrable c test) inputSum).symm
    _ = ∑' n : ℕ+, ∫ x : ℝ, outputTerm c test n x := tsum_congr (fun n => (output_integral c test n).symm)
    _ = ∫ x : ℝ, ∑' n : ℕ+, outputTerm c test n x :=
      integral_tsum_of_summable_integral_norm (output_integrable c test) outputSum
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      unfold outputTerm burnolInnerGapForward
      calc
        _ = (∑' n : ℕ+, (((n : ℕ) : ℂ)⁻¹) * U.sourceRaw c (x / (n : ℕ))) * test x := tsum_mul_right
        _ = _ := mul_comm _ _

private abbrev pulse := OriginalRieszSource.Translator.WeakInterval.pulse 7

def normalizationTest : SchwartzMap ℝ ℂ :=
  ((pulse.hasCompactSupport_normed (μ := volume)).comp_left (g := Complex.ofReal) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp pulse.contDiff_normed)

private theorem normalization_test_unit : (∫ x : ℝ, normalizationTest x) = 1 := by
  change (∫ x : ℝ, (pulse.normed volume x : ℂ)) = 1
  rw [integral_complex_ofReal, pulse.integral_normed, Complex.ofReal_one]
private theorem normalization_test_support {x : ℝ} (outside : q < |x|) : normalizationTest x = 0 := by
  change (pulse.normed volume x : ℂ) = 0
  rw [ContDiffBump.normed_def, pulse.zero_of_le_dist]
  · simp
  · change (1 / ((7 : ℝ) + 1)) ≤ dist x 0
    rw [Real.dist_eq, sub_zero]
    linarith

/-- A fixed actual unit-mass low-frequency source test calculates this normalization. -/
def calculatedNormalization (c : BurnolCompletedMellinCoordinate) : ℂ := sourceKernelAction c (𝓕 normalizationTest)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "gapMean" => burnolConstantGapCoefficient q (D.sourceInput observation nontrivial half)

private theorem actual_band_mean (test : SchwartzMap ℝ ℂ)
    (supported : ∀ x : ℝ, q < |x| → test x = 0) :
    sourceKernelAction c (𝓕 test) = gapMean * (∫ x : ℝ, test x) := by
  rw [actual_source_kernel_action]
  change (𝓕 (T.forwardDistribution c)) test = _
  rw [T.actual_fourier_response_realization]
  change ((D.sourceInput observation nontrivial half : BurnolL2) : TemperedDistribution ℝ ℂ) test = _
  rw [Lp.toTemperedDistribution_apply]
  simp only [smul_eq_mul]
  have gap := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (burnolAmbientGap_ae (D.sourceInput observation nontrivial half))
  calc
    _ = ∫ x : ℝ, test x * gapMean := by
      apply integral_congr_ae
      filter_upwards [gap] with x actual
      by_cases inside : x ∈ symmetricInterval q
      · rw [actual inside]
        rfl
      · have outside : q < |x| := lt_of_not_ge (fun small => inside (abs_le.mp small))
        rw [supported x outside, zero_mul, zero_mul]
    _ = _ := by rw [integral_mul_const]; ring

/-- The true Fourier q-mean is the output of the same complete source calculation. -/
theorem actual_normalization_read : calculatedNormalization c = gapMean := by
  unfold calculatedNormalization
  rw [actual_band_mean observation nontrivial half normalizationTest (fun x outside => normalization_test_support outside),
    normalization_test_unit, mul_one]

/-- Every actual low-frequency measurement reads that generated normalization; it is not constructor data. -/
theorem actual_q_normalization (test : SchwartzMap ℝ ℂ)
    (supported : ∀ x : ℝ, q < |x| → test x = 0) :
    (∫ u : ℝ, U.sourceRaw c u * (∑' n : ℕ+, (𝓕 test) ((n : ℝ) * u))) =
      calculatedNormalization c * (∫ x : ℝ, test x) := by
  change sourceKernelAction c (𝓕 test) = _
  rw [actual_band_mean observation nontrivial half test supported, actual_normalization_read observation nontrivial half]

end OriginalWholeDebtRJointMobiusLocalNormalization
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
