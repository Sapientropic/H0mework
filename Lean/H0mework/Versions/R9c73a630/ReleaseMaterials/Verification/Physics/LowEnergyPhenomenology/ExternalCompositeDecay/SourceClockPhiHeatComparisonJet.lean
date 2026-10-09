import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatClockPrice
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceClockPhiHeatComparisonJet

private theorem log_derivative (V t:ℝ) (hV:0<V) (ht:0<t):
    HasDerivAt (fun v:ℝ=>Real.log (1+18*t/v)) (-(1/V-1/(V+18*t))) V:=by
  have hW:0<V+18*t:=by positivity
  have hx:0<1+18*t/V:=by positivity
  have h:=(((hasDerivAt_const V (18*t)).div (hasDerivAt_id V) hV.ne').const_add 1).log hx.ne'
  dsimp at h
  convert! h using 1
  field_simp
  ring

theorem clock_mean_derivative (V t:ℝ) (hV:0<V) (ht:0<t):
    HasDerivAt (fun v:ℝ=>-Real.log (1+18*t/v)/6) ((1/V-1/(V+18*t))/6) V:=by
  convert! (log_derivative V t hV ht).neg.div_const 6 using 1
  simp only [neg_neg]

theorem clock_sqrt_variance_derivative (V t:ℝ) (hV:0<V) (ht:0<t):
    HasDerivAt (fun v:ℝ=>Real.sqrt (Real.log (1+18*t/v)/9))
      (-((1/V-1/(V+18*t))/Real.sqrt (Real.log (1+18*t/V)))/6) V:=by
  have hp:=SourceClockPhiHeatClockPrice.clock_positive_price V t hV ht
  have he:1+18*t/V=(V+18*t)/V:=by field_simp
  have hL:0<Real.log (1+18*t/V):=he ▸ hp.2.1
  have h:=((log_derivative V t hV ht).div_const 9).sqrt
    (ne_of_gt (by positivity:0<Real.log (1+18*t/V)/9))
  convert! h using 1
  rw [Real.sqrt_div hL.le]
  norm_num
  field_simp
  ring

theorem clock_noise_parameter_derivative (V t ξ:ℝ) (hV:0<V) (ht:0<t):
    HasDerivAt (fun v:ℝ=>ξ*Real.sqrt (Real.log (1+18*t/v)/9)-Real.log (1+18*t/v)/6)
      (((1/V-1/(V+18*t))-((1/V-1/(V+18*t))/Real.sqrt (Real.log (1+18*t/V)))*ξ)/6) V:=by
  have h:=((clock_sqrt_variance_derivative V t hV ht).const_mul ξ).add
    (clock_mean_derivative V t hV ht)
  convert! h using 1
  · funext v;dsimp;ring
  · ring

end LowEnergy.SourceClockPhiHeatComparisonJet
