import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatClockPrice

set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceClockPhiHeatCoefficientProduct
open SourceClockPhiHeatClockPrice

theorem clock_A_product (V t:ℝ) (hV:0<V) (ht:0<t):
    (3/Real.sqrt ((V+18*t)*Real.log ((V+18*t)/V)))*
      Real.sqrt (Real.log ((V+18*t)/V)/9)=1/Real.sqrt (V+18*t):=by
  have hp:=clock_positive_price V t hV ht
  rw [Real.sqrt_mul hp.1.le,Real.sqrt_div hp.2.1.le]
  norm_num
  field_simp [(Real.sqrt_pos.mpr hp.1).ne', (Real.sqrt_pos.mpr hp.2.1).ne']

theorem clock_UD_product (V t:ℝ) (hV:0<V) (ht:0<t):
    ((1/Real.sqrt (V+18*t))*(3/Real.sqrt ((V+18*t)*Real.log ((V+18*t)/V))))*
      Real.sqrt (Real.log ((V+18*t)/V)/9)=1/(V+18*t):=by
  have hp:=clock_positive_price V t hV ht
  rw [mul_assoc,clock_A_product V t hV ht,one_div_mul_one_div,Real.mul_self_sqrt hp.1.le]

end LowEnergy.SourceClockPhiHeatCoefficientProduct
