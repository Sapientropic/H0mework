import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalQuadrature

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalProfile
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalQuadrature
open scoped Topology ENNReal

def reciprocalProfile (f:SchwartzMap ℝ ℂ) (u:ℝ) : ℂ := (u:ℂ)⁻¹*f u⁻¹
def reciprocalSlope (f:SchwartzMap ℝ ℂ) (u:ℝ) : ℂ :=
  -((u:ℂ)^2)⁻¹*f u⁻¹-((u:ℂ)^3)⁻¹*deriv f u⁻¹

private theorem derivative_outside (f:SchwartzMap ℝ ℂ)
    (outside:∀x:ℝ,(1/2:ℝ)≤|x| → f x=0) (x:ℝ) (large:(1/2:ℝ)< |x|) : deriv f x=0 := by
  have same : (f:ℝ→ℂ)=ᶠ[𝓝 x] (fun _:ℝ=>(0:ℂ)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds large] with y hy
    exact outside y hy.le
  simpa only [deriv_const] using same.deriv_eq

private theorem reciprocal_zero (f:SchwartzMap ℝ ℂ)
    (outside:∀x:ℝ,(1/2:ℝ)≤|x| → f x=0) (u:ℝ) (small:|u|≤1) :
    reciprocalProfile f u=0 ∧ reciprocalSlope f u=0 := by
  by_cases origin:u=0
  · subst u
    simp [reciprocalProfile,reciprocalSlope]
  have positive:0 < |u|:=abs_pos.mpr origin
  have inverse : 1≤|u⁻¹| := by rw [abs_inv];exact (one_le_inv₀ positive).mpr small
  have raw:=outside u⁻¹ (by linarith)
  have slope:=derivative_outside f outside u⁻¹ (by linarith)
  simp only [reciprocalProfile,reciprocalSlope,raw,slope,mul_zero,sub_zero,and_self]

theorem actual_reciprocal_derivative (f:SchwartzMap ℝ ℂ)
    (outside:∀x:ℝ,(1/2:ℝ)≤|x| → f x=0) (u:ℝ) :
    HasDerivAt (reciprocalProfile f) (reciprocalSlope f u) u := by
  by_cases origin:u=0
  · subst u
    have same : reciprocalProfile f=ᶠ[𝓝 0] (fun _:ℝ=>(0:ℂ)) := by
      filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with y close
      exact (reciprocal_zero f outside y (by
        have : |y|<1 := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using close
        exact this.le)).1
    have generated:HasDerivAt (reciprocalProfile f) 0 0 :=
      (hasDerivAt_const (0:ℝ) (0:ℂ)).congr_of_eventuallyEq same
    simpa only [(reciprocal_zero f outside 0 (by norm_num)).2] using generated
  have inverseR := (hasDerivAt_id u).inv origin
  have inverseC := (Complex.ofRealCLM.hasDerivAt (x:=u)).inv (Complex.ofReal_ne_zero.mpr origin)
  have generated:=inverseC.mul ((f.hasDerivAt u⁻¹).scomp u inverseR)
  convert! generated using 1
  simp only [Pi.inv_apply,Complex.ofRealCLM_apply,Complex.ofReal_one,id_eq,Function.comp_apply,Complex.real_smul]
  unfold reciprocalSlope
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr origin]
  ring

theorem actual_reciprocal_slope_continuous (f:SchwartzMap ℝ ℂ)
    (outside:∀x:ℝ,(1/2:ℝ)≤|x| → f x=0) : Continuous (reciprocalSlope f) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases origin:u=0
  · subst u
    have same : reciprocalSlope f=ᶠ[𝓝 0] (fun _:ℝ=>(0:ℂ)) := by
      filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with y close
      exact (reciprocal_zero f outside y (by
        have : |y|<1 := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using close
        exact this.le)).2
    exact continuousAt_const.congr_of_eventuallyEq same
  have inverse:ContinuousAt (fun v:ℝ=>v⁻¹) u:=continuousAt_id.inv₀ origin
  have complex:ContinuousAt (fun v:ℝ=>(v:ℂ)) u:=Complex.continuous_ofReal.continuousAt
  have normless:(u:ℂ)≠0:=Complex.ofReal_ne_zero.mpr origin
  have dcontinuous:Continuous (fun v:ℝ=>deriv f v):=(SchwartzMap.derivCLM ℂ ℂ f).continuous
  exact ((complex.pow 2).inv₀ (pow_ne_zero 2 normless)).neg.mul
    (f.continuous.continuousAt.comp inverse) |>.sub
      (((complex.pow 3).inv₀ (pow_ne_zero 3 normless)).mul (dcontinuous.continuousAt.comp inverse))

theorem actual_origin_growth (f:SchwartzMap ℝ ℂ) (C:NNReal)
    (lip:LipschitzWith C (f:ℝ→ℂ)) (origin:f 0=0) (u:ℝ) : ‖f u‖≤(C:ℝ)*|u| := by
  have bound:=lip.dist_le_mul u 0
  simpa only [origin,dist_zero_right,Real.norm_eq_abs] using bound

theorem actual_reciprocal_bounds (f:SchwartzMap ℝ ℂ) (C:NNReal)
    (lip:LipschitzWith C (f:ℝ→ℂ)) (origin:f 0=0) (u:ℝ) (large:1≤u) :
    ‖reciprocalProfile f u‖≤(C:ℝ)/u^2 ∧ ‖reciprocalSlope f u‖≤2*(C:ℝ)/u^2 := by
  have positive:0<u:=by linarith
  have grow:=actual_origin_growth f C lip origin u⁻¹
  have slope:‖deriv f u⁻¹‖≤(C:ℝ):=norm_deriv_le_of_lipschitz lip
  rw [abs_inv,abs_of_pos positive] at grow
  have inverse:u⁻¹≤1:=(inv_le_one₀ positive).mpr large
  constructor
  · unfold reciprocalProfile
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
    exact (mul_le_mul_of_nonneg_left grow (inv_nonneg.mpr positive.le)).trans_eq (by ring)
  · unfold reciprocalSlope
    calc
      _≤‖-((u:ℂ)^2)⁻¹*f u⁻¹‖+‖((u:ℂ)^3)⁻¹*deriv f u⁻¹‖ := norm_sub_le _ _
      _≤(u^2)⁻¹*((C:ℝ)*u⁻¹)+(u^3)⁻¹*(C:ℝ) := by
        simp only [norm_mul,norm_neg,norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
        exact add_le_add (mul_le_mul_of_nonneg_left grow (by positivity))
          (mul_le_mul_of_nonneg_left slope (by positivity))
      _≤2*(C:ℝ)/u^2 := by
        have denomin:u^2≤u^3:=by nlinarith [sq_nonneg u]
        have invPow:(u^3)⁻¹≤(u^2)⁻¹:=(inv_le_inv₀ (by positivity : 0<u^3) (by positivity : 0<u^2)).mpr denomin
        calc
          _≤(u^2)⁻¹*((C:ℝ)*1)+(u^2)⁻¹*(C:ℝ) := by gcongr
          _=_ := by ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalProfile
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
