import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Pair

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Position
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Moment
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Pair
open scoped Topology InnerProductSpace
local notation "q"=>(1/4:ℝ)

theorem actual_exponential_power (h:ℝ) (z:ℂ):
    (Real.exp h:ℂ)^z=Complex.exp ((h:ℂ)*z):=by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ←Complex.ofReal_log (Real.exp_pos h).le,Real.log_exp]

theorem actual_scaled_power (h x:ℝ) (positive:0<x) (z:ℂ):
    ((Real.exp h*x:ℝ):ℂ)^z=Complex.exp ((h:ℂ)*z)*(x:ℂ)^z:=by
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Real.exp_pos h).le positive.le,
    actual_exponential_power]

private theorem power_cancel (c:BurnolCompletedMellinCoordinate) (h x:ℝ) (positive:0<x):
    Complex.exp ((h:ℂ)*star c.value)*((Real.exp h*x:ℝ):ℂ)^(-star c.value)=
      (x:ℂ)^(-star c.value):=by
  rw [actual_scaled_power h x positive,←mul_assoc,←Complex.exp_add,
    show (h:ℂ)*star c.value+(h:ℂ)*(-star c.value)=0 by ring,
    Complex.exp_zero,one_mul]

private theorem normalized_position_bound (c:BurnolCompletedMellinCoordinate) (h x:ℝ)
    (positive:0<x):
    ‖Complex.exp ((h:ℂ)*star c.value)*resolvedRaw c (Real.exp h*x)‖≤
      (1/2:ℝ)*‖(x:ℂ)^(-star c.value)‖:=by
  have moved:0<Real.exp h*x:=mul_pos (Real.exp_pos h) positive
  have maximum:0<max q (Real.exp h*x):=lt_of_lt_of_le moved (le_max_right _ _)
  have comparison:‖((max q (Real.exp h*x):ℝ):ℂ)^(-star c.value)‖≤
      ‖((Real.exp h*x:ℝ):ℂ)^(-star c.value)‖:=by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos maximum,
      Complex.norm_cpow_eq_rpow_re_of_pos moved]
    apply Real.rpow_le_rpow_of_nonpos moved (le_max_right _ _)
    simp only [neg_re,star_def,conj_re]
    linarith [c.rightHalf]
  calc
    _=(1/2:ℝ)*(‖Complex.exp ((h:ℂ)*star c.value)‖*
        ‖((max q (Real.exp h*x):ℝ):ℂ)^(-star c.value)‖):=by
      rw [norm_mul,resolvedRaw,abs_of_pos moved,norm_mul]
      norm_num only [norm_div,norm_one,norm_ofNat]
      ring
    _≤(1/2:ℝ)*(‖Complex.exp ((h:ℂ)*star c.value)‖*
        ‖((Real.exp h*x:ℝ):ℂ)^(-star c.value)‖):=by gcongr
    _=_:=by rw [←norm_mul,power_cancel c h x positive]

theorem actual_position_bound (c:BurnolCompletedMellinCoordinate) (h x:ℝ) (positive:0<x):
    ‖positionReading c h x‖≤(1/2:ℝ)*‖gaussianPower (1-star c.value) x‖:=by
  have bound:=mul_le_mul_of_nonneg_right (normalized_position_bound c h x positive)
    (norm_nonneg (burnolGaussianRaw 1 x))
  simpa only [positionReading,gaussianPower,show (1-star c.value)-1= -star c.value by ring,
    norm_mul,mul_assoc] using bound

theorem actual_position_pointwise (c:BurnolCompletedMellinCoordinate) (x:ℝ) (positive:0<x):
    Tendsto (fun n:ℕ=>positionReading c (n:ℝ) x) atTop
      (𝓝 ((1/2:ℂ)*gaussianPower (1-star c.value) x)):=by
  have growth:Tendsto (fun n:ℕ=>Real.exp (n:ℝ)*x) atTop atTop:=
    (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).atTop_mul_const positive
  have outside:∀ᶠn:ℕ in atTop,q<Real.exp (n:ℝ)*x:=growth.eventually (eventually_gt_atTop q)
  apply tendsto_const_nhds.congr'
  filter_upwards [outside] with n moved
  have movedPositive:0<Real.exp (n:ℝ)*x:=mul_pos (Real.exp_pos _) positive
  change (1/2:ℂ)*gaussianPower (1-star c.value) x=positionReading c (n:ℝ) x
  unfold positionReading resolvedRaw
  rw [abs_of_pos movedPositive,max_eq_right moved.le]
  have cancel:=power_cancel c (n:ℝ) x positive
  unfold gaussianPower
  rw [show (1-star c.value)-1= -star c.value by ring]
  linear_combination -(1/2:ℂ)*burnolGaussianRaw 1 x*cancel

/-- The original resolved tail generates the reciprocal Gamma head through its actual Gaussian limit. -/
theorem actual_position_gaussian_limit (c:BurnolCompletedMellinCoordinate):
    Tendsto (fun n:ℕ=>∫x:ℝ in Ioi 0,positionReading c (n:ℝ) x) atTop
      (𝓝 (Gammaℝ (1-star c.value)/4)):=by
  have strip:0<(1-star c.value).re:=by
    simp only [sub_re,one_re,star_def,conj_re]
    linarith [c.belowOne]
  have limit:Tendsto (fun n:ℕ=>∫x:ℝ in Ioi 0,positionReading c (n:ℝ) x) atTop
      (𝓝 (∫x:ℝ in Ioi 0,(1/2:ℂ)*gaussianPower (1-star c.value) x)):=by
    apply tendsto_integral_of_dominated_convergence
      (fun x:ℝ=>(1/2:ℝ)*‖gaussianPower (1-star c.value) x‖)
    · intro n
      exact (actual_position_integrable c (n:ℝ)).aestronglyMeasurable
    · exact ((actual_gaussian_power_integrable (1-star c.value) strip).norm).const_mul (1/2:ℝ)
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x positive
      exact actual_position_bound c (n:ℝ) x positive
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x positive
      exact actual_position_pointwise c x positive
  rw [integral_const_mul,actual_gaussian_power_integral (1-star c.value) strip] at limit
  convert limit using 1
  congr 1
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Position
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
