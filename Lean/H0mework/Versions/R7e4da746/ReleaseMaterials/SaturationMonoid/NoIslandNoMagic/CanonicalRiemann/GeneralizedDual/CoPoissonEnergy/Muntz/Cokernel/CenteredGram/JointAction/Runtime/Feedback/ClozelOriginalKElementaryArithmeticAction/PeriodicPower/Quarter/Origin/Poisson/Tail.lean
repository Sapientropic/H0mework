import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Fourier
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Tail
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Fourier
open scoped Topology

theorem actual_power_decay (c:BurnolCompletedMellinCoordinate):
    Tendsto (fun r:ℝ=>(r:ℂ)^(-star c.value)) atTop (𝓝 0):=by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have positive:0<c.value.re:=lt_trans (by norm_num) c.rightHalf
  have same:(fun r:ℝ=>‖(r:ℂ)^(-star c.value)‖)=ᶠ[atTop]fun r:ℝ=>r^(-c.value.re):=by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
    simp only [neg_re,star_def,conj_re]
  exact (tendsto_rpow_neg_atTop positive).congr' same.symm

def scaledReturn (c:BurnolCompletedMellinCoordinate) (r:ℝ):ℂ:=
  (r:ℂ)^(1-star c.value)*(∑'k:ℤ,scaledAliasTerm c r k)

theorem actual_scaled_return_bound (c:BurnolCompletedMellinCoordinate) (r:ℝ) (lower:1≤r):
    ‖scaledReturn c r‖≤tailBound c*inverseSquareMass/r:=by
  have positive:0<r:=lt_of_lt_of_le (by norm_num) lower
  have power:‖(r:ℂ)^(1-star c.value)‖≤r:=by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos positive]
    simp only [sub_re,one_re,star_def,conj_re]
    exact (Real.rpow_le_rpow_of_exponent_le lower (by linarith[c.rightHalf]:1-c.value.re≤1)).trans_eq
      (Real.rpow_one r)
  calc
    _=‖(r:ℂ)^(1-star c.value)‖*‖∑'k:ℤ,scaledAliasTerm c r k‖:=norm_mul _ _
    _≤r*(tailBound c/r^2*inverseSquareMass):=
      mul_le_mul power (actual_scaled_alias_sum_bound c r positive) (norm_nonneg _) positive.le
    _=tailBound c*inverseSquareMass/r:=by field_simp

theorem actual_scaled_return_decay (c:BurnolCompletedMellinCoordinate):
    Tendsto (scaledReturn c) atTop (𝓝 0):=by
  apply squeeze_zero_norm' (a:=fun r:ℝ=>tailBound c*inverseSquareMass/r)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
    exact actual_scaled_return_bound c r hr
  · exact tendsto_const_nhds.div_atTop tendsto_id

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Tail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
