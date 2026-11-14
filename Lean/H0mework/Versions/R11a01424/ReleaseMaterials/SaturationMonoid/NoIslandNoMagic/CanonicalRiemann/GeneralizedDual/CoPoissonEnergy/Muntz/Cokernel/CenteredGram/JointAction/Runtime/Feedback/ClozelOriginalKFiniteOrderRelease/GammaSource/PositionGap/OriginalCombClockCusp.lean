import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.LocalPaAdjointSmear

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.LocalPaSmear

open BurnolPhysicalState Filter MeasureTheory Set
open scoped InnerProductSpace Topology

open private orbit orbit_pair response from
  H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.LocalPaAdjointSmear

local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)
local notation "D" => burnolMultiplicativeDilation
local notation "L" => Real.log (3/2 : ℝ)
local notation "band" => burnolHarmonicStepWaveRaw 1 (3/2)

private theorem counted_before_one {x : ℝ} (positive : 0 < x) (before : x < 1) :
    band x = -(L : ℂ) := by
  have noChannel : burnolHarmonicStepChannels 1 (3/2) x = ∅ := by
    unfold burnolHarmonicStepChannels
    rw [div_one, abs_of_pos positive, Nat.floor_eq_zero.mpr before]
    simp
  simp [burnolHarmonicStepWaveRaw, noChannel]

private theorem counted_after_one {x : ℝ} (after : 1 < x) (before : x < 3/2) :
    band x = 1 - (L : ℂ) := by
  have positive : 0 < x := by linarith
  have lower : ⌊x⌋₊ = 1 := (Nat.floor_eq_iff positive.le).mpr
    ⟨by exact_mod_cast after.le, by norm_num; linarith⟩
  have upper : ⌊x/(3/2:ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr
    ((div_lt_iff₀ (by norm_num)).mpr (by simpa using before))
  have oneChannel : burnolHarmonicStepChannels 1 (3/2) x = {1} := by
    unfold burnolHarmonicStepChannels
    rw [div_one, abs_of_pos positive, lower, upper]
    decide
  simp [burnolHarmonicStepWaveRaw, oneChannel]

private theorem shifted_jump_norm (h : ℝ) (positive : 0 < h) (small : h < 2*L) :
    ∀ᵐ x : ℝ ∂volume.restrict (Ioo (Real.exp (-h/2)) 1),
      2 ≤ ‖(orbit h - seed : BurnolL2) x‖ := by
  have scaleAtLeast : 1 ≤ Real.exp (h/2/2) := by
    rw [Real.one_le_exp_iff]
    positivity
  have beforeSecond : Real.exp (h/2) < 3/2 := by
    rw [← Real.exp_log (by norm_num : 0 < (3/2:ℝ)), Real.exp_lt_exp]
    linarith
  have shiftedRead := burnolPaCombOrbit_coeFn 0 (h/2)
  have seedRead := burnolPaCombApproximation_coeFn 0
  filter_upwards [ae_restrict_of_ae (s := Ioo (Real.exp (-h/2)) 1) shiftedRead,
    ae_restrict_of_ae (s := Ioo (Real.exp (-h/2)) 1) seedRead,
    ae_restrict_of_ae (s := Ioo (Real.exp (-h/2)) 1) (Lp.coeFn_sub (orbit h) seed),
    ae_restrict_mem measurableSet_Ioo] with x shifted native difference inside
  have xpos := (Real.exp_pos (-h/2)).trans inside.1
  have shiftedAfter : 1 < Real.exp (h/2)*x := by
    calc
      1 = Real.exp (h/2)*Real.exp (-h/2) := by rw [← Real.exp_add, show h/2 + -h/2 = 0 by ring, Real.exp_zero]
      _ < _ := mul_lt_mul_of_pos_left inside.1 (Real.exp_pos _)
  have shiftedBefore : Real.exp (h/2)*x < 3/2 :=
    ((mul_lt_mul_of_pos_left inside.2 (Real.exp_pos (h/2))).trans_le (by simpa using beforeSecond.le))
  change orbit h x = _ at shifted
  rw [difference, Pi.sub_apply, shifted, native]
  norm_num only [burnolPaCombOrbitRaw, Nat.cast_zero, zero_add, burnolPaCombSourceWidth,
    show (1 : ℝ) + 1 / ((0 : ℝ) + 2) = 3/2 by norm_num, counted_before_one xpos inside.2,
    counted_after_one shiftedAfter shiftedBefore]
  apply le_trans _ (Complex.re_le_norm _)
  norm_num [Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.neg_im]
  have scale : (Complex.exp ((h:ℂ)/2/2)).re = Real.exp (h/2/2) := by
    have argument : (h:ℂ)/2/2 = ((h/2/2:ℝ):ℂ) := by norm_cast
    rw [argument, ← Complex.ofReal_exp, Complex.ofReal_re]
  rw [scale]
  have positiveSide : 0 ≤ (2:ℝ)*(1-L) := by
    have logBound := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3/2)
    linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr scaleAtLeast) positiveSide]

private theorem field_energy (v : BurnolL2) :
    Integrable (fun x : ℝ => ‖v x‖^2) ∧ ‖v‖^2 = ∫ x : ℝ, ‖v x‖^2 := by
  have normRead : (inner ℂ v v).re = ‖v‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  have complexEnergy := L2.integrable_inner (𝕜 := ℂ) v v
  have realEnergy := Complex.reCLM.integrable_comp complexEnergy
  have represented : (fun x : ℝ => Complex.reCLM (inner ℂ (v x) (v x))) = fun x => ‖v x‖^2 :=
    by
      funext x
      change (inner ℂ (v x) (v x)).re = ‖v x‖^2
      exact (norm_sq_eq_re_inner (𝕜 := ℂ) (v x)).symm
  rw [represented] at realEnergy
  refine ⟨realEnergy, ?_⟩
  calc
    ‖v‖^2 = (inner ℂ v v).re := normRead.symm
    _ = (∫ x : ℝ, inner ℂ (v x) (v x)).re := by rw [L2.inner_def]
    _ = ∫ x : ℝ, ‖v x‖^2 := by
      have realRead := integral_re complexEnergy
      change (∫ x : ℝ, Complex.reCLM (inner ℂ (v x) (v x))) = _ at realRead
      rw [represented] at realRead
      exact realRead.symm

/-- The counted jump at one has a first-order cost in the original dilation field. -/
theorem actual_comb_shift_energy_lower (h : ℝ) (positive : 0 < h) (small : h < 2*L) :
    4*(1-Real.exp (-h/2)) ≤ ‖orbit h-seed‖^2 := by
  let x₀ := Real.exp (-h/2)
  have innerWidth : x₀ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  let v := orbit h-seed
  obtain ⟨integrable, actual⟩ := field_energy v
  have oneConstant : IntegrableOn (fun _ : ℝ => (4 : ℝ)) (Ioo x₀ 1) :=
    (intervalIntegrable_const (μ := volume) (a := x₀) (b := 1) (c := (4:ℝ))).1.mono_set Ioo_subset_Ioc_self
  have pointwise : (fun _ : ℝ => (4:ℝ)) ≤ᵐ[volume.restrict (Ioo x₀ 1)] fun x => ‖v x‖^2 := by
    filter_upwards [shifted_jump_norm h positive small] with x estimate
    have square := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) estimate 2
    norm_num at square
    exact square
  calc
    4*(1-Real.exp (-h/2)) = ∫ x in Ioo x₀ 1, (4:ℝ) := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr innerWidth.le)]
      change 4 * (1-x₀) = (1-x₀)*4
      ring
    _ ≤ ∫ x in Ioo x₀ 1, ‖v x‖^2 :=
      setIntegral_mono_ae_restrict oneConstant integrable.integrableOn pointwise
    _ ≤ ∫ x : ℝ, ‖v x‖^2 :=
      setIntegral_le_integral integrable (Eventually.of_forall fun _ => sq_nonneg _)
    _ = _ := actual.symm

private def correlation (h : ℝ) : ℝ := (response seed h).re

private theorem correlation_even : Function.Even correlation := by
  intro h
  have reversed : response seed (-h) = inner ℂ seed (orbit h) := by
    simp only [response, orbit, neg_neg]
  unfold correlation
  rw [reversed, ← orbit_pair, ← inner_conj_symm seed (orbit h), starRingEnd_apply, Complex.star_def,
    Complex.conj_re]

private theorem correlation_zero : correlation 0 = ‖seed‖^2 := by
  simp only [correlation, response, neg_zero, zero_div, burnolMultiplicativeDilation_zero]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) seed).symm

private theorem correlation_energy (h : ℝ) :
    ‖orbit h-seed‖^2 = 2*(correlation 0-correlation h) := by
  rw [norm_sub_sq (𝕜 := ℂ), orbit_pair, correlation_zero]
  change ‖D (h/2) seed‖^2 - 2*correlation h + ‖seed‖^2 = _
  rw [LinearIsometryEquiv.norm_map]
  ring

/-- The original comb clock autocorrelation has a real cusp at the identity. -/
theorem seed_response_not_differentiable : ¬ DifferentiableAt ℝ (response seed) 0 := by
  intro observed
  have smooth : DifferentiableAt ℝ correlation 0 :=
    Complex.reCLM.differentiableAt.comp 0 observed
  have differentiated : HasDerivAt correlation (deriv correlation 0) 0 := smooth.hasDerivAt
  have atNeg : HasDerivAt correlation (deriv correlation 0) (-(0:ℝ)) := by
    simpa only [neg_zero] using differentiated
  have reflected := atNeg.comp (0:ℝ) ((hasDerivAt_id (0:ℝ)).neg)
  change HasDerivAt (fun t : ℝ => correlation (-t)) (deriv correlation 0 * (-1)) 0 at reflected
  have same : (fun t : ℝ => correlation (-t)) = correlation := funext correlation_even
  rw [same, mul_neg_one] at reflected
  have stationary : deriv correlation 0 = 0 := by
    have equal := differentiated.unique reflected
    linarith
  let lower (h : ℝ) := 4*(1-Real.exp (-h/2))
  let upper (h : ℝ) := 2*(correlation 0-correlation h)
  have lowerDerivative : HasDerivAt lower 2 0 := by
    have composed := (Real.hasDerivAt_exp (-(0:ℝ)/2)).comp 0 (((hasDerivAt_id (0:ℝ)).neg).div_const 2)
    have expDiff : HasDerivAt (fun h : ℝ => Real.exp (-h/2)) (-1/2) 0 := by
      simpa [Function.comp_def] using composed
    have paid := ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub expDiff).const_smul (4:ℝ)
    norm_num [Pi.sub_apply, smul_eq_mul] at paid
    exact paid
  have upperDerivative : HasDerivAt upper 0 0 := by
    rw [stationary] at differentiated
    have paid := ((hasDerivAt_const (0:ℝ) (correlation 0)).sub differentiated).const_smul (2:ℝ)
    norm_num [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at paid
    exact paid
  have increase : (2:ℝ) ≤ 0 := by
    apply le_of_tendsto_of_tendsto lowerDerivative.tendsto_slope_zero_right
      upperDerivative.tendsto_slope_zero_right
    filter_upwards [Ioo_mem_nhdsGT (by positivity : 0 < 2*L)] with h hh
    have inequality : lower h ≤ upper h := by
      change 4*(1-Real.exp (-h/2)) ≤ 2*(correlation 0-correlation h)
      rw [← correlation_energy]
      exact actual_comb_shift_energy_lower h hh.1 hh.2
    have lowZero : lower 0 = 0 := by simp [lower]
    have highZero : upper 0 = 0 := by simp [upper]
    simp only [zero_add, lowZero, highZero, sub_zero, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left inequality (inv_nonneg.mpr hh.1.le)
  norm_num at increase

end OriginalKFiniteOrderRelease.PositionGapCayley.LocalPaSmear
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
