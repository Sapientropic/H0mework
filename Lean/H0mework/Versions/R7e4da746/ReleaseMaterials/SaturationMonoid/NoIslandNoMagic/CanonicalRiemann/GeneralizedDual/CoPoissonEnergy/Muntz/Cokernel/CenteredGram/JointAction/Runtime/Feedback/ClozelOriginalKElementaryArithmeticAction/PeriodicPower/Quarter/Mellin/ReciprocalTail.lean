import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalProfile

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalTail
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalQuadrature OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalProfile
open scoped Topology ENNReal
open private reciprocal_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalProfile
open private channel channel_summable pweight forward_bound forward_reindex from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
open private integral_inverse_weight from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientContinuousMean

private def majorant (B:ℝ) : ℝ→ℝ := (Ioi (1:ℝ)).indicator (fun u=>B/u^2)

private theorem inverse_square (u:ℝ) : u^(-2:ℝ)=(u^2)⁻¹ := by
  rw [show (-2:ℝ)= -(2:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,zpow_natCast]

private theorem majorant_integrable (B:ℝ) : Integrable (majorant B) := by
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  simpa only [IntegrableOn,inverse_square,div_eq_mul_inv] using
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) (by norm_num : (0:ℝ)<1)).const_mul B

private theorem majorant_integral (B:ℝ) : (∫u:ℝ in Ioi 0,majorant B u)=B := by
  rw [majorant,setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (by intro u hu;exact lt_trans (by norm_num : (0:ℝ)<1) hu),
    show (fun u:ℝ=>B/u^2)=(fun u:ℝ=>B*u^(-2:ℝ)) by funext u;rw [inverse_square,div_eq_mul_inv],
    integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) (by norm_num : (0:ℝ)<1)]
  norm_num

private theorem profile_dominant (f:SchwartzMap ℝ ℂ) (C:NNReal)
    (lip:LipschitzWith C (f:ℝ→ℂ)) (origin:f 0=0)
    (outside:∀x:ℝ,(1/2:ℝ)≤|x| → f x=0) (u:ℝ) (positive:0<u) :
    ‖reciprocalProfile f u‖≤majorant C u ∧ ‖reciprocalSlope f u‖≤majorant (2*C) u := by
  by_cases large:1<u
  · simp only [majorant,indicator_apply,mem_Ioi,if_pos large]
    exact actual_reciprocal_bounds f C lip origin u large.le
  · have small:|u|≤1 := by rw [abs_of_pos positive];exact le_of_not_gt large
    have zero:=reciprocal_zero f outside u small
    simp only [majorant,indicator_apply,mem_Ioi,if_neg large,zero.1,zero.2,norm_zero]
    exact ⟨le_rfl,le_rfl⟩

theorem actual_reciprocal_integrability (f:SchwartzMap ℝ ℂ) (C:NNReal)
    (lip:LipschitzWith C (f:ℝ→ℂ)) (origin:f 0=0)
    (outside:∀x:ℝ,(1/2:ℝ)≤|x| → f x=0) :
    IntegrableOn (reciprocalProfile f) (Ioi 0) ∧ IntegrableOn (reciprocalSlope f) (Ioi 0) ∧
      (∫u:ℝ in Ioi 0,‖reciprocalSlope f u‖)≤2*(C:ℝ) := by
  have pcontinuous:Continuous (reciprocalProfile f) := continuous_iff_continuousAt.mpr
    (fun u=>(actual_reciprocal_derivative f outside u).continuousAt)
  have dcontinuous:=actual_reciprocal_slope_continuous f outside
  have pInt:IntegrableOn (reciprocalProfile f) (Ioi 0) := by
    apply (majorant_integrable C).integrableOn.mono' pcontinuous.measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u positive
    exact (profile_dominant f C lip origin outside u positive).1
  have dInt:IntegrableOn (reciprocalSlope f) (Ioi 0) := by
    apply (majorant_integrable (2*C)).integrableOn.mono' dcontinuous.measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u positive
    exact (profile_dominant f C lip origin outside u positive).2
  refine ⟨pInt,dInt,?_⟩
  rw [←majorant_integral (2*C)]
  apply integral_mono_ae dInt.norm (majorant_integrable (2*C)).integrableOn
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u positive
  exact (profile_dominant f C lip origin outside u positive).2

/-- The common tail depends on the generated global modulus, not on cutoff derivatives. -/
theorem actual_complete_direct_tail (f:SchwartzMap ℝ ℂ) (C:NNReal)
    (lip:LipschitzWith C (f:ℝ→ℂ)) (origin:f 0=0)
    (outside:∀u:ℝ,(1/2:ℝ)≤|u| → f u=0) (x:ℝ) (positive:0<x) :
    ‖(∑'n:ℕ,((n+1:ℕ):ℂ)⁻¹*f (x/(n+1:ℕ)))-
      ∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*f u‖≤2*(C:ℝ)/x := by
  have growth:=actual_origin_growth f C lip origin
  have channels:Summable (fun n:ℕ=>((n+1:ℕ):ℂ)⁻¹*f (x/(n+1:ℕ))) :=
    (channel_summable f C growth x).of_norm
  have npositive (n:ℕ) : (0:ℝ)<(n+1:ℕ):=by positivity
  have grid (n:ℕ) : reciprocalProfile f (((n+1:ℕ):ℝ)*x⁻¹)=
      (x:ℂ)*(((n+1:ℕ):ℂ)⁻¹*f (x/(n+1:ℕ))) := by
    unfold reciprocalProfile
    rw [mul_inv_rev,inv_inv,show x*((n+1:ℕ):ℝ)⁻¹=x/(n+1:ℕ) by rw [div_eq_mul_inv]]
    push_cast
    field_simp
  have gridSum:Summable (fun n:ℕ=>reciprocalProfile f (((n+1:ℕ):ℝ)*x⁻¹)) :=
    (channels.mul_left (x:ℂ)).congr (fun n=>(grid n).symm)
  have integrable:=actual_reciprocal_integrability f C lip origin outside
  have bound:=actual_infinite_grid_variation (reciprocalProfile f) (reciprocalSlope f)
    (actual_reciprocal_slope_continuous f outside)
    (fun u _=>actual_reciprocal_derivative f outside u) integrable.1 integrable.2.1
    x⁻¹ (inv_pos.mpr positive) gridSum
  have mean:(∫u:ℝ in Ioi 0,reciprocalProfile f u)=∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*f u :=
    integral_inverse_weight f
  simp_rw [grid] at bound
  rw [tsum_mul_left,Complex.ofReal_inv,←mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne'),one_mul,mean] at bound
  exact bound.trans ((mul_le_mul_of_nonneg_left integrable.2.2 (inv_nonneg.mpr positive.le)).trans_eq (by ring))

/-- The complete Unit has the same uniform modulus as the reciprocal source. -/
theorem actual_unit_norm (f:SchwartzMap ℝ ℂ) (C:NNReal)
    (lip:LipschitzWith C (f:ℝ→ℂ)) (origin:f 0=0)
    (outside:∀u:ℝ,(1/2:ℝ)≤|u| → f u=0) :
    ‖∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*f u‖≤(C:ℝ) := by
  rw [←integral_inverse_weight f]
  have integrable:=(actual_reciprocal_integrability f C lip origin outside).1
  calc
    _≤∫u:ℝ in Ioi 0,‖reciprocalProfile f u‖ := norm_integral_le_integral_norm _
    _≤∫u:ℝ in Ioi 0,majorant C u := by
      apply integral_mono_ae integrable.norm (majorant_integrable C).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u positive
      exact (profile_dominant f C lip origin outside u positive).1
    _=_ := majorant_integral C

/-- The same generated bound controls the entire small-x direct field, including its Unit. -/
theorem actual_complete_direct_head (f:SchwartzMap ℝ ℂ) (C:NNReal)
    (lip:LipschitzWith C (f:ℝ→ℂ)) (origin:f 0=0)
    (outside:∀u:ℝ,(1/2:ℝ)≤|u| → f u=0) (x:ℝ) (positive:0<x) (small:x≤1) :
    ‖(∑'n:ℕ,((n+1:ℕ):ℂ)⁻¹*f (x/(n+1:ℕ)))-
      ∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*f u‖≤(C:ℝ)*((∑'n:ℕ,pweight n)+1) := by
  have bound:‖∑'n:ℕ,((n+1:ℕ):ℂ)⁻¹*f (x/(n+1:ℕ))‖≤
      (C:ℝ)*|x| *(∑'n:ℕ,pweight n) := by
    simpa only [forward_reindex,channel] using
      forward_bound f C (actual_origin_growth f C lip origin) x
  have mass:0≤∑'n:ℕ,pweight n:=tsum_nonneg (fun n=>by unfold pweight;positivity)
  calc
    _≤‖∑'n:ℕ,((n+1:ℕ):ℂ)⁻¹*f (x/(n+1:ℕ))‖+
        ‖∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*f u‖ := norm_sub_le _ _
    _≤(C:ℝ)*|x| *(∑'n:ℕ,pweight n)+(C:ℝ) :=
      add_le_add bound (actual_unit_norm f C lip origin outside)
    _≤(C:ℝ)*1*(∑'n:ℕ,pweight n)+(C:ℝ) := by rw [abs_of_pos positive];gcongr
    _=_ := by ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalTail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
