import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatClockPrice

set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceClockPhiHeatComparisonPrice

theorem clock_comparison_price (V t:ℝ) (hV:0<V) (ht:0<t):
    ((1/V-1/(V+18*t))/Real.sqrt (Real.log ((V+18*t)/V)))^2+
      (1/2:ℝ)*(1/(V+18*t))^2≤(1/2:ℝ)*(1/V)^2:=by
  have hp:=SourceClockPhiHeatClockPrice.clock_positive_price V t hV ht
  let U:ℝ:=1/V
  let u:ℝ:=1/(V+18*t)
  let L:ℝ:=Real.log ((V+18*t)/V)
  have hU:0<U:=by dsimp [U];positivity
  have hu:0<u:=by dsimp [u];positivity
  have hL:0<L:=hp.2.1
  have hd:0≤U-u:=by
    have h:1/(V+18*t)≤1/V:=one_div_le_one_div_of_le hV (by linarith)
    exact sub_nonneg.mpr h
  have hl:=Real.le_log_one_add_of_nonneg (x:=18*t/V) (by positivity)
  have he:1+18*t/V=(V+18*t)/V:=by field_simp
  have hf:2*(18*t/V)/(18*t/V+2)=2*(U-u)/(U+u):=by
    dsimp [U,u]
    field_simp
    ring
  rw [he,hf] at hl
  have hbase:2*(U-u)≤L*(U+u):=(div_le_iff₀ (add_pos hU hu)).mp hl
  have hpay:=mul_le_mul_of_nonneg_left hbase hd
  have hk:(U-u)^2/L≤(U^2-u^2)/2:=by
    apply (div_le_iff₀ hL).mpr
    nlinarith
  change ((U-u)/Real.sqrt L)^2+(1/2:ℝ)*u^2≤(1/2:ℝ)*U^2
  rw [div_pow,Real.sq_sqrt hL.le]
  linarith

end LowEnergy.SourceClockPhiHeatComparisonPrice
