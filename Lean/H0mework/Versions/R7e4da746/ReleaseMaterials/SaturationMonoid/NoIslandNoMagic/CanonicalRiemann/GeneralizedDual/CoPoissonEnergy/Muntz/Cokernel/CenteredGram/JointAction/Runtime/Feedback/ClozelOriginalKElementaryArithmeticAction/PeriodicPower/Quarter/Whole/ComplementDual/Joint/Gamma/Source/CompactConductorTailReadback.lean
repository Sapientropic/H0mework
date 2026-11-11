import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CompactConductorExterior
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFourier
import H0mework.Arithmetic.TruncatedFourier.IntegralKernel
import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.CompactConductorTailReadback
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace ENNReal
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.CompactConductorExterior
open OriginalGamma.Source.FiniteLogCounting
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "μq" => (volume.restrict (symmetricInterval q))
local instance : IsFiniteMeasure μq := by
  change IsFiniteMeasure (volume.restrict (Icc (-q) q))
  infer_instance

def halfStieltjes (r : Hq) (x : ℝ) : ℂ :=
  ∫ t : ℝ in Ioc 0 q, ((x / (x ^ 2 - t ^ 2) : ℝ) : ℂ) * r t

private theorem quarter_integrable (r : Hq) : IntegrableOn (r : ℝ → ℂ) (Ioc 0 q) := by
  have whole : IntegrableOn (r : ℝ → ℂ) (symmetricInterval q) :=
    (Lp.memLp r).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact whole.mono_set (fun t ht => ⟨by linarith [ht.1], ht.2⟩)

private theorem exterior_kernel_bound (x t : ℝ) (outside : q < x) (inside : t ∈ Ioc 0 q) :
    ‖((x / (x ^ 2 - t ^ 2) : ℝ) : ℂ)‖ ≤ (x - q)⁻¹ := by
  have first : 0 < x - t := by linarith [inside.2]
  have second : 0 < x + t := by linarith [inside.1]
  have lower : 0 < x - q := sub_pos.mpr outside
  have denominator : x ^ 2 - t ^ 2 ≠ 0 := by
    rw [show x ^ 2 - t ^ 2 = (x - t) * (x + t) by ring]
    exact mul_ne_zero first.ne' second.ne'
  have partialFraction : x / (x ^ 2 - t ^ 2) = ((x - t)⁻¹ + (x + t)⁻¹) / 2 := by
    field_simp [denominator, first.ne', second.ne']
    ring
  have firstBound : (x - t)⁻¹ ≤ (x - q)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le lower (by linarith [inside.2] : x - q ≤ x - t)
  have secondBound : (x + t)⁻¹ ≤ (x - q)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le lower (by linarith [inside.1] : x - q ≤ x + t)
  rw [Complex.norm_real, Real.norm_eq_abs, partialFraction, abs_of_nonneg (by positivity)]
  linarith

theorem original_half_stieltjes_continuous (r : Hq) : ContinuousOn (halfStieltjes r) (Ioi q) := by
  intro x outside
  change q < x at outside
  apply ContinuousAt.continuousWithinAt
  let lower : ℝ := (x + q) / 2
  have lowerQ : q < lower := by dsimp [lower]; linarith
  have lowerX : lower < x := by dsimp [lower]; linarith
  let bound : ℝ → ℝ := fun t => (lower - q)⁻¹ * ‖r t‖
  have measured : ∀ᶠ y : ℝ in 𝓝 x, AEStronglyMeasurable
      (fun t : ℝ => ((y / (y ^ 2 - t ^ 2) : ℝ) : ℂ) * r t) (volume.restrict (Ioc 0 q)) := by
    filter_upwards with y
    exact (by fun_prop : Measurable (fun t : ℝ => ((y / (y ^ 2 - t ^ 2) : ℝ) : ℂ))).aestronglyMeasurable.mul
      ((quarter_integrable r).aestronglyMeasurable)
  have budget : ∀ᶠ y : ℝ in 𝓝 x, ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 q),
      ‖((y / (y ^ 2 - t ^ 2) : ℝ) : ℂ) * r t‖ ≤ bound t := by
    filter_upwards [Ioi_mem_nhds lowerX] with y above
    change lower < y at above
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
    rw [norm_mul]
    have source := exterior_kernel_bound y t (lowerQ.trans above) inside
    have compare : (y - q)⁻¹ ≤ (lower - q)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr lowerQ) (by linarith : lower - q ≤ y - q)
    exact mul_le_mul_of_nonneg_right (source.trans compare) (norm_nonneg _)
  have int : Integrable bound (volume.restrict (Ioc 0 q)) := (quarter_integrable r).norm.const_mul _
  have point : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 q),
      ContinuousAt (fun y : ℝ => ((y / (y ^ 2 - t ^ 2) : ℝ) : ℂ) * r t) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
    have denominator : x ^ 2 - t ^ 2 ≠ 0 := by
      rw [show x ^ 2 - t ^ 2 = (x - t) * (x + t) by ring]
      exact mul_ne_zero (by linarith [inside.2] : x - t ≠ 0) (by linarith [inside.1] : x + t ≠ 0)
    apply ContinuousAt.mul_const
    exact Complex.continuous_ofReal.continuousAt.comp
      (continuous_id.continuousAt.div ((continuous_id.pow 2).sub continuous_const).continuousAt denominator)
  exact continuousAt_of_dominated measured budget int point

private theorem stieltjes_test_integrable (r : Hq) (g : ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g)
    (compact : HasCompactSupport g) (support : tsupport g ⊆ Ioi q) :
    Integrable (fun x : ℝ => g x • halfStieltjes r x) := by
  have continuous : ContinuousOn (fun x : ℝ => g x • halfStieltjes r x) (tsupport g) :=
    smooth.continuous.continuousOn.smul ((original_half_stieltjes_continuous r).mono support)
  have paid : IntegrableOn (fun x : ℝ => g x • halfStieltjes r x) (tsupport g) (volume : Measure ℝ) :=
    continuous.integrableOn_compact compact
  apply (integrableOn_iff_integrable_of_support_subset (s := tsupport g) ?_).mp paid
  intro x active
  apply subset_tsupport g
  intro zero
  apply active
  change g x • halfStieltjes r x = 0
  rw [zero, zero_smul]

private theorem gamma_field_positive_ae (r : Hq) (gamma : BurnolL2)
    (source : ∀ test : SchwartzMap ℝ ℂ, tsupport test ⊆ Ioi q →
      inner ℂ (test.toLp 2 volume) gamma = -∫ x : ℝ, star (test x) * halfStieltjes r x) :
    ∀ᵐ x : ℝ ∂volume, q < x → gamma x = -halfStieltjes r x := by
  have localGamma := ((Lp.memLp gamma).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).locallyIntegrableOn (Ioi q)
  have localSource : LocallyIntegrableOn (halfStieltjes r) (Ioi q) (volume : Measure ℝ) :=
    (original_half_stieltjes_continuous r).locallyIntegrableOn measurableSet_Ioi
  have vanished := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero (localGamma.add localSource) ?_
  · filter_upwards [vanished] with x source
    intro outside
    have zero := source outside
    exact eq_neg_of_add_eq_zero_left zero
  · intro g smooth compact support
    have complexCompact : HasCompactSupport (Complex.ofRealCLM ∘ g) := compact.comp_left rfl
    let test : SchwartzMap ℝ ℂ := complexCompact.toSchwartzMap (Complex.ofRealCLM.contDiff.comp smooth)
    have testSupport : tsupport test ⊆ Ioi q := (tsupport_comp_subset (g := Complex.ofRealCLM) rfl g).trans support
    have sourceRead := source test testSupport
    have gammaRead : inner ℂ (test.toLp 2 volume) gamma = ∫ x : ℝ, (g x : ℂ) * gamma x := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [test.coeFn_toLp 2 volume] with x actual
      rw [actual, RCLike.inner_apply, starRingEnd_apply]
      change gamma x * star (g x : ℂ) = (g x : ℂ) * gamma x
      rw [Complex.star_def, Complex.conj_ofReal, mul_comm]
    have targetRead : (∫ x : ℝ, star (test x) * halfStieltjes r x) =
        ∫ x : ℝ, g x • halfStieltjes r x := by
      apply integral_congr_ae
      filter_upwards with x
      change star (g x : ℂ) * halfStieltjes r x = _
      rw [Complex.star_def, Complex.conj_ofReal, Complex.real_smul]
    rw [gammaRead, targetRead] at sourceRead
    have first : Integrable (fun x : ℝ => g x • gamma x) :=
      ((Lp.memLp gamma).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable_smul_left_of_hasCompactSupport
        smooth.continuous compact
    have second := stieltjes_test_integrable r g smooth compact support
    simp_rw [Pi.add_apply, smul_add]
    rw [integral_add first second]
    simpa only [Complex.real_smul] using add_eq_zero_iff_eq_neg.mpr sourceRead

private theorem log_pair_even (value logarithm : BurnolL2) (even : reflectL2 value = value)
    (source : LogPair value logarithm) : reflectL2 logarithm = logarithm := by
  have pulled := negMeasurePreserving.quasiMeasurePreserving.ae source
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving logarithm negMeasurePreserving,
    Lp.coeFn_compMeasurePreserving value negMeasurePreserving, source, pulled]
    with x logAt valueAt sourceAt pulledAt
  change reflectL2 logarithm x = logarithm (-x) at logAt
  change reflectL2 value x = value (-x) at valueAt
  rw [even] at valueAt
  change logarithm x = (Real.log |x| : ℂ) * value x at sourceAt
  change logarithm (-x) = (Real.log |-x| : ℂ) * value (-x) at pulledAt
  rw [logAt, pulledAt, abs_neg, ← valueAt, ← sourceAt]

private theorem reflect_fourier (value : BurnolL2) :
    reflectL2 (fourierL2 value) = fourierL2 (reflectL2 value) := by
  calc
    _ = fourierL2 (fourierL2 (fourierL2 value)) := (fourierL2_fourierL2 (fourierL2 value)).symm
    _ = _ := congrArg fourierL2 (fourierL2_fourierL2 value)

private theorem gamma_even_from_actual_logs (value posLog fLog : BurnolL2)
    (even : reflectL2 value = value) (position : LogPair value posLog)
    (frequency : LogPair (fourierL2 value) fLog) :
    reflectL2 (posLog + fourierL2 fLog) = posLog + fourierL2 fLog := by
  have first := log_pair_even value posLog even position
  have sourceEven : reflectL2 (fourierL2 value) = fourierL2 value := by rw [reflect_fourier, even]
  have second := log_pair_even (fourierL2 value) fLog sourceEven frequency
  rw [map_add, reflect_fourier, first, second]

private theorem gamma_field_absolute_exterior (r : Hq) (gamma : BurnolL2)
    (even : reflectL2 gamma = gamma)
    (source : ∀ᵐ x : ℝ ∂volume, q < x → gamma x = -halfStieltjes r x) :
    ∀ᵐ x : ℝ ∂volume, q < |x| → gamma x = -halfStieltjes r |x| := by
  have pulled := negMeasurePreserving.quasiMeasurePreserving.ae source
  filter_upwards [source, pulled, Lp.coeFn_compMeasurePreserving gamma negMeasurePreserving]
    with x positive negative reflected
  change reflectL2 gamma x = gamma (-x) at reflected
  rw [even] at reflected
  intro outside
  by_cases nonnegative : 0 ≤ x
  · rw [abs_of_nonneg nonnegative] at outside ⊢
    exact positive outside
  · rw [abs_of_neg (lt_of_not_ge nonnegative)] at outside ⊢
    exact reflected.trans (negative outside)

end
end OriginalGamma.Source.CompactConductorTailReadback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
