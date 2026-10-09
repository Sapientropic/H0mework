import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaussianComplexIBP
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceClockPhiGaussianSecondIBP
open ProbabilityTheory MeasureTheory Set
open scoped Topology
private abbrev γ := gaussianReal 0 1
private abbrev φ := gaussianPDFReal 0 1
private theorem density_derivative (x:ℝ) : HasDerivAt φ (-x*φ x) x := by
  have hp:HasDerivAt (fun y:ℝ=> -y^2/2) (-x) x:=by
    convert ((hasDerivAt_pow 2 x).neg.div_const 2) using 1 <;> first | rfl | ring
  have h:=hp.exp.const_mul (Real.sqrt (2*Real.pi))⁻¹
  convert! h using 1
  · funext y; simp only [φ,gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
  · simp only [φ,gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]; ring
private theorem density_continuous : Continuous φ :=
  continuous_iff_continuousAt.mpr (fun x=>(density_derivative x).continuousAt)
private theorem density_first : Integrable (fun x:ℝ=>|x| *φ x) volume := by
  have h:Integrable (fun x:ℝ=>|x| *Real.exp (-(1/2:ℝ)*x^2)) volume:=by
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)] using!
      (integrable_mul_exp_neg_mul_sq (by norm_num:0<(1/2:ℝ))).norm
  have hc:=h.const_mul (Real.sqrt (2*Real.pi))⁻¹
  convert! hc using 1
  funext x
  simp only [φ,gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
  rw [show -x^2/2=-(1/2:ℝ)*x^2 by ring]
  ring
private theorem density_second : Integrable (fun x:ℝ=>x^2*φ x) volume := by
  have h:Integrable (fun x:ℝ=>x^2*Real.exp (-(1/2:ℝ)*x^2)) volume:=by
    simpa only [Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq (b:=(1/2:ℝ)) (s:=2) (by norm_num) (by norm_num))
  have hc:=h.const_mul (Real.sqrt (2*Real.pi))⁻¹
  convert! hc using 1
  funext x
  simp only [φ,gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
  rw [show -x^2/2=-(1/2:ℝ)*x^2 by ring]
  ring
private theorem first_density_bounded (f:ℝ→ℂ) (hc:Continuous f) (C:ℝ)
    (hb:∀x,‖f x‖≤C) : Integrable (fun x:ℝ=>(x*φ x) • f x) volume := by
  apply (density_first.mul_const C).mono'
    (((continuous_id.mul density_continuous).smul hc).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(x*φ x) • f x‖≤(|x| *φ x)*C
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
  exact mul_le_mul_of_nonneg_left (hb x) (mul_nonneg (abs_nonneg x) (gaussianPDFReal_nonneg 0 1 x))
private theorem second_density_bounded (f:ℝ→ℂ) (hc:Continuous f) (C:ℝ)
    (hb:∀x,‖f x‖≤C) : Integrable (fun x:ℝ=>((1-x^2)*φ x) • f x) volume := by
  have hp:Integrable (fun x:ℝ=>(1+x^2)*φ x) volume:=by
    have he:(fun x:ℝ=>(1+x^2)*φ x)=(fun x:ℝ=>φ x+x^2*φ x):=by funext x;ring
    rw [he]
    exact (integrable_gaussianPDFReal 0 1).add density_second
  apply (hp.mul_const C).mono'
    (((continuous_const.sub (continuous_id.pow 2)).mul density_continuous).smul hc).aestronglyMeasurable
  filter_upwards [] with x
  change ‖((1-x^2)*φ x) • f x‖≤((1+x^2)*φ x)*C
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
  have hC:0≤C:=(norm_nonneg (f x)).trans (hb x)
  have hab:|1-x^2|≤1+x^2:=by apply abs_le.mpr;constructor <;> nlinarith [sq_nonneg x]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hab (gaussianPDFReal_nonneg 0 1 x))
    (hb x) (norm_nonneg _) (mul_nonneg (by positivity) (gaussianPDFReal_nonneg 0 1 x))

/-- Two actual Gaussian integrations by parts, with the Hermite correction retained. -/
theorem standard_gaussian_complex_second_IBP (h h' h'':ℝ→ℂ) (C C' C'':ℝ)
    (hc:ContDiff ℝ 1 h) (hc':ContDiff ℝ 1 h')
    (hd:∀x,HasDerivAt h (h' x) x) (hd':∀x,HasDerivAt h' (h'' x) x)
    (hb:∀x,‖h x‖≤C) (hb':∀x,‖h' x‖≤C') (hb'':∀x,‖h'' x‖≤C'') :
    (∫x,h'' x ∂γ)=(∫x,((x:ℂ)^2-1)*h x ∂γ) := by
  rw [SourceClockPhiGaussianComplexIBP.standard_gaussian_complex_IBP h' h'' C' C'' hc' hd' hb' hb'']
  have hdφ(x:ℝ):HasDerivAt (fun y:ℝ=>y*φ y) ((1-x^2)*φ x) x:=by
    have h:=(hasDerivAt_id x).mul (density_derivative x)
    have he:(1:ℝ)*φ x+x*(-x*φ x)=(1-x^2)*φ x:=by ring
    simpa only [Pi.mul_apply,id_eq,he] using! h
  have hi:=integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L:=ContinuousLinearMap.lsmul ℝ ℝ) (fun x _=>hdφ x) (fun x _=>hd x)
    (first_density_bounded h' hc'.continuous C' hb')
    (second_density_bounded h hc.continuous C hb)
    (first_density_bounded h hc.continuous C hb)
  rw [integral_gaussianReal_eq_integral_smul (by norm_num:(1:NNReal)≠0),
    integral_gaussianReal_eq_integral_smul (by norm_num:(1:NNReal)≠0)]
  convert! hi using 1
  · apply integral_congr_ae
    filter_upwards [] with x
    simp only [ContinuousLinearMap.lsmul_apply,Complex.real_smul,Complex.ofReal_mul]
    ring
  · rw [←integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [ContinuousLinearMap.lsmul_apply,Complex.real_smul,Complex.ofReal_mul,
      Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
    ring

theorem standard_gaussian_hermite_abs_price :
    (∫x:ℝ,|x^2-1| ∂γ)≤2 := by
  have h2:Integrable (fun x:ℝ=>x^2) γ:=
    (memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq
  have hi:Integrable (fun x:ℝ=>|x^2-1|) γ:=(h2.sub (integrable_const 1)).norm
  have h:=integral_mono hi (h2.add (integrable_const 1))
    (fun x=>by change |x^2-1|≤x^2+1;apply abs_le.mpr;constructor <;> nlinarith [sq_nonneg x])
  change (∫x:ℝ,|x^2-1| ∂γ)≤(∫x:ℝ,x^2+1 ∂γ) at h
  rw [integral_add h2 (integrable_const 1),
    SourceClockPhiGaussianComplexIBP.standard_gaussian_square_moment] at h
  norm_num only [integral_const,probReal_univ,smul_eq_mul,mul_one] at h
  exact h
end LowEnergy.SourceClockPhiGaussianSecondIBP
