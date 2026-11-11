import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.Family
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Weight
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
open private reciprocal_small sqrt_bound power_times_sqrt from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReciprocalTail

def weight (c:BurnolCompletedMellinCoordinate) (u:ℝ) : ℂ := burnolRieszReturnRaw c u⁻¹/(u:ℂ)
def weightedSlope (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℂ :=
 burnolRieszReturnRaw c x+(x:ℂ)*burnolRieszReturnRawDerivative c x

theorem weight_hasDerivAt (c:BurnolCompletedMellinCoordinate) (u:ℝ) (positive:0<u) :
 HasDerivAt (weight c) (-((u:ℂ)⁻¹^2)*weightedSlope c u⁻¹) u := by
 have original:=Complex.ofRealCLM.hasDerivAt.mul (burnolRieszReturnRaw_hasDerivAt c u⁻¹)
 have inverse:=(hasDerivAt_id u).inv positive.ne'
 have actual:=original.scomp u inverse
 convert! actual using 1
 · funext v
   simp only [weight,Function.comp_apply,Pi.mul_apply,Complex.ofReal_inv,Complex.ofRealCLM_apply,div_eq_mul_inv]
   ring
 · simp only [weightedSlope,Complex.real_smul,Complex.ofRealCLM_apply,id_eq]
   push_cast
   simp only [div_eq_mul_inv,inv_pow]
   ring

theorem weight_measurable (c:BurnolCompletedMellinCoordinate) : Measurable (weight c) := by
 unfold weight
 exact ((burnolRieszReturnRaw_continuous c).measurable.comp measurable_inv).div (by fun_prop)

theorem weight_deriv_measurable (c:BurnolCompletedMellinCoordinate) : Measurable (deriv (weight c)) := measurable_deriv _

theorem weight_deriv_continuousOn (c:BurnolCompletedMellinCoordinate) :
 ContinuousOn (deriv (weight c)) (Ioi 0) := by
 have regular:ContinuousOn (fun u:ℝ=>-((u:ℂ)⁻¹^2)*weightedSlope c u⁻¹) (Ioi 0):=by
  intro u positive
  have inverse:ContinuousAt (fun v:ℝ=>v⁻¹) u:=continuousAt_inv₀ positive.ne'
  have factor:ContinuousAt (fun v:ℝ=>((v:ℂ)⁻¹)^2) u:=
   (Complex.continuous_ofReal.continuousAt.inv₀ (Complex.ofReal_ne_zero.mpr positive.ne')).pow 2
  have value:ContinuousAt (fun v:ℝ=>burnolRieszReturnRaw c v⁻¹) u:=
   (burnolRieszReturnRaw_continuous c).continuousAt.comp inverse
  have slope:ContinuousAt (fun v:ℝ=>burnolRieszReturnRawDerivative c v⁻¹) u:=
   (burnolRieszReturnRawDerivative_continuous c).continuousAt.comp inverse
  exact (factor.neg.mul (value.add ((Complex.continuous_ofReal.continuousAt.comp inverse).mul slope))).continuousWithinAt
 exact regular.congr (fun u positive=>(weight_hasDerivAt c u positive).deriv)

def slopeBound (c:BurnolCompletedMellinCoordinate) : ℝ :=
 PositionCounting.returnBound c+q*PositionCounting.returnSlopeBound c

theorem slopeBound_nonnegative (c:BurnolCompletedMellinCoordinate) : 0≤slopeBound c := by
 unfold slopeBound
 positivity [PositionCounting.return_bound_nonnegative c,PositionCounting.return_slope_nonnegative c]

theorem weightedSlope_bound (c:BurnolCompletedMellinCoordinate) (x:ℝ) (inside:x∈Icc 0 q) :
 ‖weightedSlope c x‖≤slopeBound c := by
 calc
  _≤‖burnolRieszReturnRaw c x‖+‖(x:ℂ)*burnolRieszReturnRawDerivative c x‖:=norm_add_le _ _
  _≤PositionCounting.returnBound c+q*PositionCounting.returnSlopeBound c:=by
   apply add_le_add (PositionCounting.return_bound c x inside)
   rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg inside.1]
   exact mul_le_mul inside.2 (PositionCounting.return_slope_bound c x inside) (norm_nonneg _) (by norm_num)
  _=_:=rfl

theorem derivative_bound (c:BurnolCompletedMellinCoordinate) (u:ℝ) (large:4≤u) :
 ‖deriv (weight c) u‖≤slopeBound c*u⁻¹^2 := by
 have positive:0<u:=by linarith
 rw [(weight_hasDerivAt c u positive).deriv,norm_mul,norm_neg,norm_pow,norm_inv,Complex.norm_real,
  Real.norm_eq_abs,abs_of_pos positive]
 exact (mul_le_mul_of_nonneg_left (weightedSlope_bound c u⁻¹
  ⟨(inv_pos.mpr positive).le,reciprocal_small u large⟩) (sq_nonneg _)).trans_eq (by ring)

theorem derivative_weight_bound (c:BurnolCompletedMellinCoordinate) (u:ℝ) (large:4≤u) :
 ‖deriv (weight c) u‖*(Real.sqrt u+2)≤(3*slopeBound c)*u^(-(3/2:ℝ)) := by
 have positive:0<u:=by linarith
 have power:u⁻¹^2*Real.sqrt u=u^(-(3/2:ℝ)):=by
  have inversePower:u⁻¹^2=u^(-2:ℝ):=by
   rw [show (-2:ℝ)= -(2:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,zpow_natCast,inv_pow]
  rw [inversePower,power_times_sqrt u positive,show (-2:ℝ)+1/2= -(3/2:ℝ) by ring]
 calc
  _≤(slopeBound c*u⁻¹^2)*(3*Real.sqrt u):=
   mul_le_mul (derivative_bound c u large) (sqrt_bound u large) (by positivity)
    (mul_nonneg (slopeBound_nonnegative c) (sq_nonneg _))
  _=(3*slopeBound c)*(u⁻¹^2*Real.sqrt u):=by ring
  _=_:=by rw [power]

theorem derivative_weight_integrable (c:BurnolCompletedMellinCoordinate) :
 IntegrableOn (InfiniteWeightedProgram.weight (deriv (weight c))) (Ioi 4) := by
 have dominant:=(integrableOn_Ioi_rpow_of_lt (by norm_num:-(3/2:ℝ)< -1)
  (by norm_num:(0:ℝ)<4)).const_mul (3*slopeBound c)
 apply dominant.mono'
  (((weight_deriv_measurable c).norm.mul (Real.continuous_sqrt.measurable.add_const 2)).aestronglyMeasurable)
 filter_upwards [ae_restrict_mem measurableSet_Ioi] with u large
 change ‖‖deriv (weight c) u‖*(Real.sqrt u+2)‖≤_
 rw [Real.norm_of_nonneg (by positivity)]
 exact derivative_weight_bound c u large.le

theorem head_bound (c:BurnolCompletedMellinCoordinate) (u:ℝ) (large:4≤u) :
 Real.sqrt u*‖weight c u‖≤PositionCounting.returnBound c*u^(-(1/2:ℝ)) := by
 have positive:0<u:=by linarith
 have bound:=PositionCounting.return_bound c u⁻¹
  ⟨(inv_pos.mpr positive).le,reciprocal_small u large⟩
 have power:u⁻¹*Real.sqrt u=u^(-(1/2:ℝ)):=by
  rw [←Real.rpow_neg_one u,power_times_sqrt u positive]
  congr 1
  ring
 rw [weight,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
 calc
  _≤Real.sqrt u*(PositionCounting.returnBound c/u):=mul_le_mul_of_nonneg_left
   (div_le_div_of_nonneg_right bound positive.le) (Real.sqrt_nonneg u)
  _=PositionCounting.returnBound c*(u⁻¹*Real.sqrt u):=by ring
  _=_:=by rw [power]

theorem head_tendsto_zero (c:BurnolCompletedMellinCoordinate) :
 Tendsto (fun u:ℝ=>Real.sqrt u*‖weight c u‖) atTop (𝓝 0) := by
 have dominant:=(tendsto_rpow_neg_atTop (by norm_num:(0:ℝ)<1/2)).const_mul (PositionCounting.returnBound c)
 apply squeeze_zero' (Eventually.of_forall (fun u=>mul_nonneg (Real.sqrt_nonneg u) (norm_nonneg _)))
  ((eventually_ge_atTop (4:ℝ)).mono (fun u large=>head_bound c u large))
 simpa only [mul_zero] using dominant

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Weight
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
