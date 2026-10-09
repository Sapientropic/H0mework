import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceClockPhiGaussianComplexIBP
open ProbabilityTheory MeasureTheory Set
open scoped Topology

private theorem density_derivative (x:ℝ):
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x:=by
  have hp:HasDerivAt (fun y:ℝ=> -y^2/2) (-x) x:=by
    convert ((hasDerivAt_pow 2 x).neg.div_const 2) using 1 <;> first | rfl | ring
  have h:=hp.exp.const_mul (Real.sqrt (2*Real.pi))⁻¹
  convert! h using 1
  · funext y
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
  · simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    ring
private theorem density_continuous:Continuous (gaussianPDFReal 0 1):=by
  exact continuous_iff_continuousAt.mpr (fun x=>(density_derivative x).continuousAt)
private theorem density_first_moment:
    Integrable (fun x:ℝ=>|x| *gaussianPDFReal 0 1 x) volume:=by
  have h:Integrable (fun x:ℝ=>|x| *Real.exp (-(1/2:ℝ)*x^2)) volume:=by
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)] using!
      (integrable_mul_exp_neg_mul_sq (by norm_num:0<(1/2:ℝ))).norm
  have hc:=h.const_mul (Real.sqrt (2*Real.pi))⁻¹
  convert! hc using 1
  funext x
  simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
  rw [show -x^2/2=-(1/2:ℝ)*x^2 by ring]
  ring
private theorem density_times_bounded (h:ℝ→ℂ) (hh:Continuous h) (C:ℝ) (hb:∀x:ℝ,‖h x‖≤C):
    Integrable (fun x:ℝ=>gaussianPDFReal 0 1 x • h x) volume:=by
  apply ((integrable_gaussianPDFReal 0 1).mul_const C).mono'
    ((density_continuous.smul hh).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖gaussianPDFReal 0 1 x • h x‖≤gaussianPDFReal 0 1 x*C
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
  exact mul_le_mul_of_nonneg_left (hb x) (gaussianPDFReal_nonneg 0 1 x)
private theorem density_derivative_times_bounded (h:ℝ→ℂ) (hh:Continuous h) (C:ℝ)
    (hb:∀x:ℝ,‖h x‖≤C):
    Integrable (fun x:ℝ=>(-x*gaussianPDFReal 0 1 x) • h x) volume:=by
  apply (density_first_moment.mul_const C).mono'
    (((continuous_id.neg.mul density_continuous).smul hh).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(-x*gaussianPDFReal 0 1 x) • h x‖≤(|x| *gaussianPDFReal 0 1 x)*C
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
  exact mul_le_mul_of_nonneg_left (hb x) (mul_nonneg (abs_nonneg x) (gaussianPDFReal_nonneg 0 1 x))

theorem standard_gaussian_complex_IBP (h h':ℝ→ℂ) (C C':ℝ)
    (hc:ContDiff ℝ 1 h) (hd:∀x:ℝ,HasDerivAt h (h' x) x)
    (hb:∀x:ℝ,‖h x‖≤C) (hb':∀x:ℝ,‖h' x‖≤C'):
    (∫x,h' x ∂gaussianReal 0 1)=(∫x,(x:ℂ)*h x ∂gaussianReal 0 1):=by
  have he:h'=deriv h:=funext (fun x=>(hd x).deriv.symm)
  have hc':Continuous h':=he ▸ hc.continuous_deriv (by norm_num)
  have hi:=integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L:=ContinuousLinearMap.lsmul ℝ ℝ)
    (fun x _=>density_derivative x) (fun x _=>hd x)
    (density_times_bounded h' hc' C' hb')
    (density_derivative_times_bounded h hc.continuous C hb)
    (density_times_bounded h hc.continuous C hb)
  rw [integral_gaussianReal_eq_integral_smul (by norm_num:(1:NNReal)≠0),
    integral_gaussianReal_eq_integral_smul (by norm_num:(1:NNReal)≠0)]
  convert! hi using 1
  rw [←integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ContinuousLinearMap.lsmul_apply,Complex.real_smul,Complex.ofReal_mul,
    Complex.ofReal_neg,neg_mul,neg_neg]
  ring


theorem standard_gaussian_square_moment:
    (∫x:ℝ,x^2 ∂gaussianReal 0 1)=1:=by
  have h:=variance_fun_id_gaussianReal (μ:=0) (v:=1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa only [integral_id_gaussianReal,sub_zero,NNReal.coe_one] using h

theorem standard_gaussian_abs_moment_le_one:
    (∫x:ℝ,|x| ∂gaussianReal 0 1)≤1:=by
  have h1:Integrable (fun x:ℝ=>x) (gaussianReal 0 1):=
    (memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)
  have habs:Integrable (fun x:ℝ=>|x|) (gaussianReal 0 1):=by
    simpa only [Real.norm_eq_abs] using h1.norm
  have h2:Integrable (fun x:ℝ=>x^2) (gaussianReal 0 1):=
    (memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq
  have hb(x:ℝ):2*|x|≤x^2+1:=by
    nlinarith [sq_nonneg (|x|-1),sq_abs x]
  have h:=integral_mono (habs.const_mul 2) (h2.add (integrable_const (1:ℝ))) hb
  rw [integral_const_mul,integral_add' h2 (integrable_const (1:ℝ)),standard_gaussian_square_moment] at h
  simp only [integral_const,probReal_univ,smul_eq_mul,mul_one] at h
  linarith

end LowEnergy.SourceClockPhiGaussianComplexIBP
