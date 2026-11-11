import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorGapReciprocal
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.ConductorFaithfulness

open BurnolPhysicalState Filter MeasureTheory Set
open OriginalGamma.Source.RelativeConductorGapReadback
open scoped InnerProductSpace Topology

open private integral_inverse_tail from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorGapReciprocal

open private actual_gap_kernel_domain from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaGapLocalSource

local notation "q" => (1/4 : ℝ)
local notation "edge" => (1/8 : ℝ)
local notation "I" => Ioo (0:ℝ) 4
local notation "T" => burnolTateReciprocalL2

private def windowTerm (g : ℝ → ℂ) (n : Nat) (x t : ℝ) : ℂ :=
  (t^(2*n) / (1-(x*t)^2)) • g t

private def windowRead (g : ℝ → ℂ) (n : Nat) (x : ℝ) : ℂ :=
  ∫ t in I, windowTerm g n x t

private theorem window_denom {x t : ℝ} (inside : x ∈ Icc (0:ℝ) edge) (ht : t ∈ I) :
    (3/4 : ℝ) ≤ 1-(x*t)^2 := by
  have nonnegative : 0 ≤ x*t := mul_nonneg inside.1 ht.1.le
  have half : x*t ≤ (1/2 : ℝ) := by
    calc
      x*t ≤ edge*4 := mul_le_mul inside.2 ht.2.le ht.1.le (by norm_num)
      _ = 1/2 := by norm_num
  nlinarith [mul_nonneg (sub_nonneg.mpr half) (show 0 ≤ 1/2+x*t by linarith)]

private theorem window_domain (g : ℝ → ℂ) (domain : IntegrableOn g I) (n : Nat)
    {x : ℝ} (inside : x ∈ Icc (0:ℝ) edge) :
    IntegrableOn (windowTerm g n x) I ∧
      ‖windowRead g n x‖ ≤ (2 * (4:ℝ)^(2*n)) * (∫ t in I, ‖g t‖) := by
  let budget := 2 * (4:ℝ)^(2*n)
  have major := domain.norm.const_mul budget
  have bound : ∀ᵐ t : ℝ ∂volume.restrict I, ‖windowTerm g n x t‖ ≤ budget * ‖g t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have denom := window_denom inside ht
    have positive : 0 < 1-(x*t)^2 := (by norm_num : (0:ℝ)<3/4).trans_le denom
    have numerator := pow_le_pow_left₀ ht.1.le ht.2.le (2*n)
    have paid : t^(2*n) / (1-(x*t)^2) ≤ budget := by
      apply (div_le_iff₀ positive).mpr
      have step := mul_le_mul_of_nonneg_left denom (show 0 ≤ budget by dsimp [budget]; positivity)
      dsimp only [budget] at step ⊢
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 4) (2*n)]
    rw [windowTerm, norm_smul, Real.norm_of_nonneg (div_nonneg (pow_nonneg ht.1.le _) positive.le)]
    exact mul_le_mul_of_nonneg_right paid (norm_nonneg _)
  have scalar : Measurable (fun t : ℝ => t^(2*n) / (1-(x*t)^2)) := by fun_prop
  refine ⟨major.mono' (scalar.aestronglyMeasurable.smul domain.aestronglyMeasurable) bound, ?_⟩
  have paid := norm_integral_le_of_norm_le major bound
  rwa [integral_const_mul] at paid

private theorem window_step (g : ℝ → ℂ) (domain : IntegrableOn g I) (n : Nat)
    {x : ℝ} (inside : x ∈ Icc (0:ℝ) edge) :
    windowRead g n x = windowRead g n 0 + x^2 • windowRead g (n+1) x := by
  have origin := (window_domain g domain n (show (0:ℝ) ∈ Icc 0 edge by norm_num)).1
  have next := (window_domain g domain (n+1) inside).1
  unfold windowRead
  have scaled : IntegrableOn (fun t => x^2 • windowTerm g (n+1) x t) I :=
    (Integrable.smul (x^2) next).congr (Eventually.of_forall fun _ => rfl)
  rw [← integral_smul, ← integral_add origin scaled]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have denom : 1-(x*t)^2 ≠ 0 := (lt_of_lt_of_le (by norm_num : (0:ℝ) < 3/4)
    (window_denom inside ht)).ne'
  simp only [windowTerm, zero_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one, smul_smul,
    ← add_smul]
  congr 1
  rw [show 2*(n+1) = 2*n+2 by omega, pow_add]
  apply (div_eq_iff denom).mpr
  rw [add_mul, mul_assoc, div_mul_cancel₀ _ denom]
  ring

private theorem origin_zero_of_window_zero (g : ℝ → ℂ) (domain : IntegrableOn g I) (n : Nat)
    (silent : ∀ᵐ x : ℝ ∂volume, x ∈ Ioo (0:ℝ) edge → windowRead g n x = 0) :
    windowRead g n 0 = 0 := by
  by_contra live
  let budget := (2 * (4:ℝ)^(2*(n+1))) * (∫ t in I, ‖g t‖)
  have nonnegative : 0 ≤ budget := by
    dsimp only [budget]
    exact mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  have positive := norm_pos_iff.mpr live
  let r := min edge (‖windowRead g n 0‖/(budget+1))
  have rPos : 0 < r := lt_min (by norm_num) (div_pos positive (by linarith))
  have nonnull : (volume : Measure ℝ) (Ioo 0 r) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]
    exact (ENNReal.ofReal_pos.mpr rPos).ne'
  obtain ⟨x, hx, quiet⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae nonnull
    (ae_restrict_of_ae (s := Ioo 0 r) silent)
  have xSmall : x < edge := hx.2.trans_le (min_le_left _ _)
  have near : x ∈ Icc (0:ℝ) edge := ⟨hx.1.le, xSmall.le⟩
  have recurrence := window_step g domain n near
  rw [quiet ⟨hx.1,xSmall⟩] at recurrence
  have relation : windowRead g n 0 = -(x^2 • windowRead g (n+1) x) :=
    eq_neg_of_add_eq_zero_left recurrence.symm
  have charge : ‖windowRead g n 0‖ ≤ x^2*budget := by
    rw [relation, norm_neg, norm_smul, Real.norm_of_nonneg (sq_nonneg x)]
    exact mul_le_mul_of_nonneg_left (window_domain g domain (n+1) near).2 (sq_nonneg x)
  have small : x*(budget+1) < ‖windowRead g n 0‖ :=
    (lt_div_iff₀ (by linarith)).mp (hx.2.trans_le (min_le_right _ _))
  have square : x^2 ≤ x := by
    nlinarith [mul_nonneg hx.1.le (show 0 ≤ 1-x by linarith)]
  have monotone := mul_le_mul_of_nonneg_left (show budget ≤ budget+1 by linarith) hx.1.le
  exact (not_lt_of_ge charge) ((mul_le_mul_of_nonneg_right square nonnegative).trans_lt
    (monotone.trans_lt small))

private theorem compact_moments (g : ℝ → ℂ) (domain : IntegrableOn g I)
    (silent : ∀ᵐ x : ℝ ∂volume, x ∈ Ioo (0:ℝ) edge → windowRead g 0 x = 0) (n : Nat) :
    (∫ t in I, t^(2*n) • g t) = 0 := by
  have all (j : Nat) : ∀ᵐ x : ℝ ∂volume, x ∈ Ioo (0:ℝ) edge → windowRead g j x = 0 := by
    induction j with
    | zero => exact silent
    | succ j prior =>
      have origin := origin_zero_of_window_zero g domain j prior
      filter_upwards [prior] with x read hx
      have recurrence := window_step g domain j ⟨hx.1.le,hx.2.le⟩
      rw [read hx, origin, zero_add] at recurrence
      exact (smul_eq_zero.mp recurrence.symm).resolve_left (pow_ne_zero _ hx.1.ne')
  simpa only [windowRead, windowTerm, zero_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one]
    using origin_zero_of_window_zero g domain n (all n)

private theorem window_smul_integrable (g : ℝ → ℂ) (domain : IntegrableOn g I) (test : ℝ → ℝ)
    (continuous : Continuous test) : IntegrableOn (fun t => test t • g t) I := by
  obtain ⟨bound, leBound⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 4)).bddAbove_image
    continuous.norm.continuousOn
  apply (domain.norm.const_mul bound).mono'
    (continuous.aestronglyMeasurable.smul domain.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  change ‖test t • g t‖ ≤ bound * ‖g t‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (leBound ⟨t, ⟨ht.1.le,ht.2.le⟩, rfl⟩) (norm_nonneg _)

private theorem polynomial_read_zero (g : ℝ → ℂ) (domain : IntegrableOn g I)
    (moments : ∀ n : Nat, (∫ t in I, t^(2*n) • g t) = 0) (p : Polynomial ℝ) :
    (∫ t in I, p.eval (t^2) • g t) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [Polynomial.eval_add, add_smul]
    have pInt : IntegrableOn (fun t => p.eval (t^2) • g t) I :=
      window_smul_integrable g domain _ (p.continuous.comp (continuous_id.pow 2))
    have rInt : IntegrableOn (fun t => r.eval (t^2) • g t) I :=
      window_smul_integrable g domain _ (r.continuous.comp (continuous_id.pow 2))
    rw [integral_add pInt rInt, hp, hr, add_zero]
  | monomial n a =>
    simp only [Polynomial.eval_monomial, ← pow_mul, mul_smul, integral_smul, moments, smul_zero]

private theorem compact_field_zero (g : ℝ → ℂ) (domain : IntegrableOn g I)
    (moments : ∀ n : Nat, (∫ t in I, t^(2*n) • g t) = 0) :
    ∀ᵐ t : ℝ ∂volume, t ∈ I → g t = 0 := by
  apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (locallyIntegrableOn_of_locallyIntegrable_restrict domain.locallyIntegrable)
  intro test smooth _ support
  have restricted : (∫ t : ℝ, test t • g t) = ∫ t in I, test t • g t := by
    rw [← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ I
    · rw [indicator_of_mem ht]
    · have vanished : test t = 0 := by
        by_contra live
        exact ht (support (subset_tsupport _ live))
      rw [indicator_of_notMem ht, vanished, zero_smul]
  rw [restricted]
  by_contra live
  let value := ∫ t in I, test t • g t
  let mass := ∫ t in I, ‖g t‖
  have massNonnegative : 0 ≤ mass := integral_nonneg fun _ => norm_nonneg _
  let delta := ‖value‖/(1+mass)
  have deltaPositive : 0 < delta := div_pos (norm_pos_iff.mpr live) (by linarith)
  obtain ⟨poly, near⟩ := exists_polynomial_near_of_continuousOn (0:ℝ) 16
    (fun t => test (Real.sqrt t)) (smooth.continuous.comp Real.continuous_sqrt).continuousOn delta deltaPositive
  have polynomialZero := polynomial_read_zero g domain moments poly
  have testInt := window_smul_integrable g domain test smooth.continuous
  have polynomialInt : IntegrableOn (fun t => poly.eval (t^2) • g t) I :=
    window_smul_integrable g domain _ (poly.continuous.comp (continuous_id.pow 2))
  have bound : ∀ᵐ t : ℝ ∂volume.restrict I,
      ‖test t • g t - poly.eval (t^2) • g t‖ ≤ delta * ‖g t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have inside : t^2 ∈ Icc (0:ℝ) 16 := ⟨sq_nonneg _, by nlinarith [ht.1, ht.2]⟩
    have difference := near (t^2) inside
    rw [Real.sqrt_sq ht.1.le] at difference
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, abs_sub_comm]
    exact mul_le_mul_of_nonneg_right difference.le (norm_nonneg _)
  have paid := norm_integral_le_of_norm_le (domain.norm.const_mul delta) bound
  rw [integral_sub testInt polynomialInt, polynomialZero, sub_zero, integral_const_mul] at paid
  have smaller := mul_lt_mul_of_pos_left (show mass < 1+mass by linarith) deltaPositive
  have full : delta*(1+mass) = ‖value‖ := div_mul_cancel₀ _ (by linarith)
  rw [full] at smaller
  exact (not_lt_of_ge paid) smaller

/-- The original weak conductor has zero kernel on the even position-gap field. -/
theorem zero_of_even_position_gap_conductor (w : BurnolL2) (even : reflectL2 w = w)
    (gap : w ∈ locallyConstantFace q) (silent : GammaPair w 0) : w = 0 := by
  let g : ℝ → ℂ := T w
  obtain ⟨empty, quiet⟩ := zero_conductor_reciprocal w even gap silent
  have finite : IsFiniteMeasure ((volume : Measure ℝ).restrict I) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have domain : IntegrableOn g I :=
    ((Lp.memLp (T w)).mono_measure Measure.restrict_le_self).integrable (by norm_num)
  have read : ∀ᵐ x : ℝ ∂volume, x ∈ Ioo (0:ℝ) edge → windowRead g 0 x = 0 := by
    simpa only [windowRead, windowTerm, reciprocalGapRead, Nat.mul_zero, pow_zero, one_div, g] using quiet
  have gone := compact_field_zero g domain (compact_moments g domain read)
  let tail (y : ℝ) := ‖w y‖ * y⁻¹
  have tailDomain : IntegrableOn tail (Ioi q) := by
    apply ((actual_gap_kernel_domain w empty 0 (by norm_num)).1.norm.integrableOn (s := Ioi q)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y inside
    have positive : 0 < y := (by norm_num : 0 < q).trans inside
    simp only [tail, zero_sub, abs_neg, abs_of_pos positive, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr positive.le)]
  have tailZero : (∫ y in Ioi q, tail y) = 0 := by
    rw [integral_inverse_tail]
    have zero : (fun t : ℝ => (t^2)⁻¹ • tail t⁻¹) =ᵐ[volume.restrict I] fun _ => 0 := by
      filter_upwards [ae_restrict_of_ae (s := I) gone,
        ae_restrict_of_ae (s := I) (burnolTateReciprocalL2_coeFn w),
        ae_restrict_mem measurableSet_Ioo] with t readAt raw inside
      have actual := readAt inside
      change (T w) t = 0 at actual
      rw [raw, burnolTateReciprocalRaw, abs_of_pos inside.1] at actual
      have original := (mul_eq_zero.mp actual).resolve_left
        (inv_ne_zero (Complex.ofReal_ne_zero.mpr inside.1.ne'))
      simp only [tail, original, norm_zero, zero_mul, smul_zero]
    rw [integral_congr_ae zero, integral_zero]
  have weightedNonnegative : ∀ᵐ y : ℝ ∂volume.restrict (Ioi q), 0 ≤ tail y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y inside
    exact mul_nonneg (norm_nonneg _) (inv_nonneg.mpr ((by norm_num : 0 < q).trans inside).le)
  have outside : ∀ᵐ y : ℝ ∂volume.restrict (Ioi q), w y = 0 := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae weightedNonnegative tailDomain).mp tailZero,
      ae_restrict_mem measurableSet_Ioi] with y erased inside
    exact norm_eq_zero.mp ((mul_eq_zero.mp erased).resolve_right
      (inv_ne_zero ((by norm_num : 0 < q).trans inside).ne'))
  have positive : ∀ᵐ y : ℝ ∂volume, 0 < y → w y = 0 := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp outside, empty, volume.ae_ne q] with y away inside ne hy
    by_cases h : q < y
    · exact away h
    · exact inside (by rw [abs_of_pos hy]; exact lt_of_le_of_ne (le_of_not_gt h) ne)
  have reflected := Lp.coeFn_compMeasurePreserving w negMeasurePreserving
  change (reflectL2 w : ℝ → ℂ) =ᵐ[volume] fun x => w (-x) at reflected
  rw [even] at reflected
  apply Lp.ext
  filter_upwards [positive, negMeasurePreserving.quasiMeasurePreserving.ae positive,
    reflected, volume.ae_ne (0:ℝ), Lp.coeFn_zero (α := ℝ) (E := ℂ) (p := 2) (μ := volume)]
    with x onPos onNeg same nonzero zero
  rw [zero]
  rcases lt_or_gt_of_ne nonzero with left | right
  · exact same.trans (onNeg (neg_pos.mpr left))
  · exact onPos right

end OriginalKFiniteOrderRelease.PositionGapCayley.ConductorFaithfulness
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
