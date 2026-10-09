import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatClockPrice
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceClockPhiHeatHamiltonianCoefficient
open MeasureTheory ProbabilityTheory

theorem actual_heat_exponential_moment (V t q:ℝ) (hV:0<V) (ht:0<t):
    Integrable (fun ξ:ℝ=>Real.exp (q*(-Real.log ((V+18*t)/V)/6+
      Real.sqrt (Real.log ((V+18*t)/V)/9)*ξ))) (gaussianReal 0 1)∧
    (∫ξ:ℝ,Real.exp (q*(-Real.log ((V+18*t)/V)/6+
      Real.sqrt (Real.log ((V+18*t)/V)/9)*ξ)) ∂gaussianReal 0 1)=
      Real.rpow ((V+18*t)/V) (q*(q-3)/18):=by
  have hp:=SourceClockPhiHeatClockPrice.clock_positive_price V t hV ht
  let R:ℝ:=(V+18*t)/V
  let L:ℝ:=Real.log R
  let m:ℝ:= -L/6
  let w:ℝ:=Real.sqrt (L/9)
  have hR:0<R:=div_pos hp.1 hV
  have hL:0<L:=hp.2.1
  have hw:w^2=L/9:=Real.sq_sqrt (by positivity:0≤L/9)
  have hf(ξ:ℝ):Real.exp (q*(m+w*ξ))=Real.exp (q*m)*Real.exp ((q*w)*ξ):=by
    rw [←Real.exp_add]
    congr 1
    ring
  have hi:=integrable_exp_mul_gaussianReal (μ:=0) (v:=1) (q*w)
  change Integrable (fun ξ:ℝ=>Real.exp (q*(m+w*ξ))) (gaussianReal 0 1)∧
    (∫ξ:ℝ,Real.exp (q*(m+w*ξ)) ∂gaussianReal 0 1)=Real.rpow R (q*(q-3)/18)
  constructor
  · simpa only [hf] using hi.const_mul (Real.exp (q*m))
  · simp_rw [hf]
    rw [integral_const_mul]
    have hg:=congrFun (mgf_fun_id_gaussianReal (μ:=0) (v:=1)) (q*w)
    change (∫ξ:ℝ,Real.exp ((q*w)*ξ) ∂gaussianReal 0 1)=_ at hg
    simp only [zero_mul,NNReal.coe_one,one_mul,zero_add] at hg
    rw [hg,←Real.exp_add,Real.rpow_eq_pow,Real.rpow_def_of_pos hR]
    congr 1
    rw [mul_pow,hw]
    dsimp only [m,L]
    ring

end LowEnergy.SourceClockPhiHeatHamiltonianCoefficient
