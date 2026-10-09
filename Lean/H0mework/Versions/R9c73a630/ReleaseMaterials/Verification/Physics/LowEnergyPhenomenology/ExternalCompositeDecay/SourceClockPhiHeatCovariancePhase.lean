import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace LowEnergy.ClockPhiHeatCovariancePhase
open MeasureTheory Set Filter
open scoped Topology ContDiff
private def numerator(L:ℝ):ℝ:=L*(Real.exp L+1)-2*(Real.exp L-1)
private def numeratorFirst(L:ℝ):ℝ:=(L-1)*Real.exp L+1
private theorem numeratorFirst_derivative(L:ℝ):
    HasDerivAt numeratorFirst (L*Real.exp L) L:=by
  have h:=((hasDerivAt_id L).sub_const 1).mul (Real.hasDerivAt_exp L)
  have hh:=h.add_const 1
  convert! hh using 1
  simp only [id_eq]
  ring
private theorem numeratorFirst_pos(L:ℝ)(hL:0<L):0<numeratorFirst L:=by
  have hm:StrictMonoOn numeratorFirst (Ici (0:ℝ)):=by
    apply strictMonoOn_of_deriv_pos (convex_Ici _) (by unfold numeratorFirst;fun_prop)
    intro x hx
    have hx':0<x:=by simpa only [interior_Ici,mem_Ioi] using hx
    rw [(numeratorFirst_derivative x).deriv]
    exact mul_pos hx' (Real.exp_pos _)
  have h:=hm (by simp) (by simpa only [mem_Ici] using hL.le) hL
  simpa only [numeratorFirst,Real.exp_zero,sub_zero,zero_sub,mul_one,neg_add_cancel] using h
private theorem numerator_derivative(L:ℝ):HasDerivAt numerator (numeratorFirst L) L:=by
  have h:=((hasDerivAt_id L).mul ((Real.hasDerivAt_exp L).add_const 1)).sub
    (((Real.hasDerivAt_exp L).sub_const 1).const_mul 2)
  convert! h using 1
  simp only [id_eq,numeratorFirst]
  ring
private theorem numerator_pos(L:ℝ)(hL:0<L):0<numerator L:=by
  have hm:StrictMonoOn numerator (Ici (0:ℝ)):=by
    apply strictMonoOn_of_deriv_pos (convex_Ici _) (by unfold numerator;fun_prop)
    intro x hx
    have hx':0<x:=by simpa only [interior_Ici,mem_Ioi] using hx
    rw [(numerator_derivative x).deriv]
    exact numeratorFirst_pos x hx'
  have h:=hm (by simp) (by simpa only [mem_Ici] using hL.le) hL
  simpa only [numerator,Real.exp_zero,zero_mul,sub_self,mul_zero] using h

def phaseSpeed(L:ℝ):ℝ:=Real.sqrt (numerator L/(8*L^2*(Real.exp L-1)))
def clockPhase(L:ℝ):ℝ:=∫s in (1:ℝ)..L,phaseSpeed s
private theorem speed_positive(L:ℝ)(hL:0<L):0<numerator L/(8*L^2*(Real.exp L-1)):=by
  have he:0<Real.exp L-1:=sub_pos.mpr ((Real.one_lt_exp_iff).mpr hL)
  exact div_pos (numerator_pos L hL) (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hL)) he)
theorem phaseSpeed_smooth(L:ℝ)(hL:0<L):ContDiffAt ℝ ∞ phaseSpeed L:=by
  have he:Real.exp L-1≠0:=(sub_pos.mpr ((Real.one_lt_exp_iff).mpr hL)).ne'
  have hn:ContDiffAt ℝ ∞ numerator L:=by unfold numerator;fun_prop
  have hd:ContDiffAt ℝ ∞ (fun x:ℝ=>8*x^2*(Real.exp x-1)) L:=by fun_prop
  have hq:ContDiffAt ℝ ∞ (fun x:ℝ=>numerator x/(8*x^2*(Real.exp x-1))) L:=
    hn.div hd (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hL.ne')) he)
  exact hq.sqrt (speed_positive L hL).ne'
theorem phaseSpeed_square(L:ℝ)(hL:0<L):
    phaseSpeed L^2=numerator L/(8*L^2*(Real.exp L-1)):=Real.sq_sqrt (speed_positive L hL).le
private theorem speed_measurable:Measurable phaseSpeed:=by
  unfold phaseSpeed numerator
  fun_prop

theorem clockPhase_derivative(L:ℝ)(hL:0<L):HasDerivAt clockPhase (phaseSpeed L) L:=by
  have hi:IntervalIntegrable phaseSpeed volume 1 L:=by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx':0<x:=(lt_min (by norm_num) hL).trans_le hx.1
    exact (phaseSpeed_smooth x hx').continuousAt.continuousWithinAt
  exact intervalIntegral.integral_hasDerivAt_right hi
    speed_measurable.aestronglyMeasurable.stronglyMeasurableAtFilter
    (phaseSpeed_smooth L hL).continuousAt

theorem clockPhase_smooth(L:ℝ)(hL:0<L):ContDiffAt ℝ ∞ clockPhase L:=by
  have hd:ContDiffOn ℝ ∞ clockPhase (Ioi (0:ℝ)):=by
    apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
    refine ⟨fun x hx=>(clockPhase_derivative x hx).differentiableAt.differentiableWithinAt,?_⟩
    have hs:ContDiffOn ℝ ∞ phaseSpeed (Ioi (0:ℝ)):=fun x hx=>(phaseSpeed_smooth x hx).contDiffWithinAt
    apply hs.congr
    intro x hx
    exact (clockPhase_derivative x hx).deriv
  exact hd.contDiffAt (Ioi_mem_nhds hL)

/-- The rotation adds exactly the source covariance missing from the rank-one clock. -/
theorem actual_rotation_covariance (V t:ℝ)(hV:0<V)(ht:0<t):
    let W:=V+18*t
    let L:=Real.log (W/V)
    ((1/V-1/W)/Real.sqrt L)^2+
      4*L*(1/V-1/W)^2*(phaseSpeed L)^2=(1/2)*((1/V)^2-(1/W)^2):=by
  dsimp only
  have hW:0<V+18*t:=by positivity
  have hR:0<(V+18*t)/V:=div_pos hW hV
  have hL:0<Real.log ((V+18*t)/V):=Real.log_pos ((lt_div_iff₀ hV).mpr (by linarith))
  rw [phaseSpeed_square _ hL,div_pow,Real.sq_sqrt hL.le]
  unfold numerator
  rw [Real.exp_log hR]
  have he:(V+18*t)/V-1≠0:=by
    apply ne_of_gt
    exact sub_pos.mpr ((lt_div_iff₀ hV).mpr (by linarith))
  field_simp [hV.ne',hW.ne',hL.ne',he]
  ring
end LowEnergy.ClockPhiHeatCovariancePhase
