import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceClockPhiHeatClockPrice

theorem clock_log_cocycle (V s t:ℝ) (hV:0<V) (hs:0≤s) (ht:0≤t):
    Real.log ((V+18*(s+t))/V)=Real.log ((V+18*t)/V)+
      Real.log (((V+18*t)+18*s)/(V+18*t)):=by
  have hW:0<V+18*t:=by positivity
  have hZ:0<V+18*(s+t):=by positivity
  have he:(V+18*t)+18*s=V+18*(s+t):=by ring
  rw [he,Real.log_div hZ.ne' hV.ne',Real.log_div hW.ne' hV.ne',Real.log_div hZ.ne' hW.ne']
  ring

theorem clock_log_payment (V t:ℝ) (hV:0<V) (ht:0≤t):
    18*t≤(V+18*t)*Real.log ((V+18*t)/V):=by
  have hW:0<V+18*t:=by positivity
  have h:=mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos (div_pos hW hV)) hW.le
  have he:(V+18*t)*(1-((V+18*t)/V)⁻¹)=18*t:=by
    field_simp [hV.ne',hW.ne']
    ring
  rw [he] at h
  exact h

theorem clock_positive_price (V t:ℝ) (hV:0<V) (ht:0<t):
    0<V+18*t∧0<Real.log ((V+18*t)/V)∧
      0<(V+18*t)*Real.log ((V+18*t)/V):=by
  have hW:0<V+18*t:=by positivity
  have hp:0<(V+18*t)*Real.log ((V+18*t)/V):=
    (by positivity:0<18*t).trans_le (clock_log_payment V t hV ht.le)
  exact ⟨hW,(mul_pos_iff.mp hp).resolve_right (by intro h;linarith [h.1]) |>.2,hp⟩

theorem clock_A_price (V t:ℝ) (hV:0<V) (ht:0<t):
    3/Real.sqrt ((V+18*t)*Real.log ((V+18*t)/V))≤1/Real.sqrt (2*t):=by
  have hp:=clock_positive_price V t hV ht
  have hPay:=Real.sqrt_le_sqrt (clock_log_payment V t hV ht.le)
  have he:Real.sqrt (18*t)=3*Real.sqrt (2*t):=by
    rw [show 18*t=9*(2*t) by ring,Real.sqrt_mul (by norm_num:0≤(9:ℝ))]
    norm_num
  rw [he] at hPay
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hp.2.2) (Real.sqrt_pos.mpr (by positivity:0<2*t))).mpr
  simpa only [one_mul] using hPay

theorem clock_U_price (V t:ℝ) (hV:0<V) (ht:0<t):
    1/(V+18*t)≤1/(18*t):=by
  apply (div_le_div_iff₀ (by positivity:0<V+18*t) (by positivity:0<18*t)).mpr
  simp only [one_mul]
  linarith

theorem clock_aA_price (V t:ℝ) (hV:0<V) (ht:0<t):
    (1/Real.sqrt (V+18*t))*(3/Real.sqrt ((V+18*t)*Real.log ((V+18*t)/V)))≤1/(6*t):=by
  have hp:=clock_positive_price V t hV ht
  have hW:18*t≤V+18*t:=by linarith
  have hPay:=clock_log_payment V t hV ht.le
  have hprod:(18*t)^2≤(V+18*t)*((V+18*t)*Real.log ((V+18*t)/V)):=by
    calc (18*t)^2=(18*t)*(18*t):=by ring
         _≤(V+18*t)*((V+18*t)*Real.log ((V+18*t)/V)):=
           mul_le_mul hW hPay (by positivity) hp.1.le
  have hroot:=Real.sqrt_le_sqrt hprod
  rw [Real.sqrt_sq (by positivity:0≤18*t),Real.sqrt_mul hp.1.le] at hroot
  have hD:0<Real.sqrt (V+18*t)*Real.sqrt ((V+18*t)*Real.log ((V+18*t)/V)):=
    mul_pos (Real.sqrt_pos.mpr hp.1) (Real.sqrt_pos.mpr hp.2.2)
  have he:(1/Real.sqrt (V+18*t))*(3/Real.sqrt ((V+18*t)*Real.log ((V+18*t)/V)))=
      3/(Real.sqrt (V+18*t)*Real.sqrt ((V+18*t)*Real.log ((V+18*t)/V))):=by
    field_simp
  rw [he]
  apply (div_le_div_iff₀ hD (by positivity:0<6*t)).mpr
  nlinarith

end LowEnergy.SourceClockPhiHeatClockPrice
