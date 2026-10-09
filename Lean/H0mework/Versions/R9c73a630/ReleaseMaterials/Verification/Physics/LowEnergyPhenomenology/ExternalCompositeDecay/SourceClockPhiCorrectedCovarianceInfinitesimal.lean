import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatComparisonPrice
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace LowEnergy.ClockPhiCorrectedCovarianceInfinitesimal
open Filter Set
open scoped Topology
private theorem clock_jets(V:ℝ)(hV:0<V):
    HasDerivAt (fun t:ℝ=>1/V-1/(V+18*t)) (18/V^2) 0 ∧
    HasDerivAt (fun t:ℝ=>Real.log ((V+18*t)/V)) (18/V) 0 ∧
    HasDerivAt (fun t:ℝ=>(1/V)^2-(1/(V+18*t))^2) (36/V^3) 0:=by
  have hv:HasDerivAt (fun t:ℝ=>V+18*t) 18 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul 18).const_add V
  have hi:=hv.inv (by simpa using hV.ne')
  have hlog:=(hv.div_const V).log (by simp [hV.ne'])
  refine ⟨?_,?_,?_⟩
  · convert! hi.const_sub (1/V) using 1 <;>
      simp only [one_div,Pi.inv_apply,mul_zero,add_zero]
    ring
  · convert! hlog using 1
    simp [hV.ne']
  · convert! (hi.pow 2).const_sub ((1/V)^2) using 1 <;>
      simp only [one_div,Pi.pow_apply,Pi.inv_apply,mul_zero,add_zero]
    norm_num
    field_simp [hV.ne']
    nlinarith [mul_inv_cancel₀ hV.ne']

theorem actual_clock_covariance_first_order_zero(V:ℝ)(hV:0<V):
    Tendsto (fun t:ℝ=>((1/V)^2-(1/(V+18*t))^2-
      2*((1/V-1/(V+18*t))/Real.sqrt (Real.log ((V+18*t)/V)))^2)/t)
      (𝓝[>] 0) (𝓝 0):=by
  obtain ⟨hD,hL,hQ⟩:=clock_jets V hV
  have hd:Tendsto (fun t:ℝ=>(1/V-1/(V+18*t))/t) (𝓝[>] 0) (𝓝 (18/V^2)):=by
    simpa only [zero_add,mul_zero,zero_mul,one_mul,mul_one,add_zero,sub_self,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using hD.tendsto_slope_zero_right
  have hl:Tendsto (fun t:ℝ=>Real.log ((V+18*t)/V)/t) (𝓝[>] 0) (𝓝 (18/V)):=by
    simpa only [zero_add,mul_zero,zero_mul,one_mul,mul_one,add_zero,div_self hV.ne',Real.log_one,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using hL.tendsto_slope_zero_right
  have hq:Tendsto (fun t:ℝ=>((1/V)^2-(1/(V+18*t))^2)/t) (𝓝[>] 0) (𝓝 (36/V^3)):=by
    simpa only [zero_add,mul_zero,zero_mul,one_mul,mul_one,add_zero,sub_self,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using hQ.tendsto_slope_zero_right
  have hn:18/V≠0:=div_ne_zero (by norm_num) hV.ne'
  have hh:=hq.sub (((hd.pow 2).div hl hn).const_mul 2)
  have hv:36/V^3-2*((18/V^2)^2/(18/V))=0:=by field_simp;ring
  rw [hv] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht':0<t:=ht
  have hR:1<(V+18*t)/V:=(lt_div_iff₀ hV).mpr (by nlinarith)
  have hlog:0<Real.log ((V+18*t)/V):=Real.log_pos hR
  simp only [Pi.div_apply,div_pow,Real.sq_sqrt hlog.le]
  field_simp [ht'.ne',hlog.ne']

theorem actual_clock_covariance_first_order_bound(V t:ℝ)(hV:0<V)(ht:0<t):
    0≤((1/V)^2-(1/(V+18*t))^2-
      2*((1/V-1/(V+18*t))/Real.sqrt (Real.log ((V+18*t)/V)))^2)/t ∧
    ((1/V)^2-(1/(V+18*t))^2-
      2*((1/V-1/(V+18*t))/Real.sqrt (Real.log ((V+18*t)/V)))^2)/t≤36/V^3:=by
  have hp:=SourceClockPhiHeatComparisonPrice.clock_comparison_price V t hV ht
  have hW:0<V+18*t:=by positivity
  refine ⟨div_nonneg (by linarith) ht.le,?_⟩
  apply (div_le_iff₀ ht).mpr
  have he:36*t/V^3-((1/V)^2-(1/(V+18*t))^2)=
      324*t^2*(3*V+36*t)/(V^3*(V+18*t)^2):=by
    field_simp
    ring
  have hh:0≤324*t^2*(3*V+36*t)/(V^3*(V+18*t)^2):=by positivity
  rw [←he] at hh
  have hr:36/V^3*t=36*t/V^3:=by ring
  rw [hr]
  nlinarith [sq_nonneg ((1/V-1/(V+18*t))/Real.sqrt (Real.log ((V+18*t)/V)))]
end LowEnergy.ClockPhiCorrectedCovarianceInfinitesimal
