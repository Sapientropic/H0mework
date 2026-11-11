import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Consumer
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source
open scoped Topology ENNReal InnerProductSpace FourierTransform
open private unitWeight actual_integral_mellin_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source
open private mellin_source_ae from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource

private theorem unitWeight_integral (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h) :
    (∫t:ℝ in Ioc 0 (2*h),unitWeight c t)=
      (Complex.exp ((1-star c.value)*(h:ℂ))-1)/((1-star c.value)/2) := by
  have nonzero : (1-star c.value:ℂ)≠0 := by
    intro same
    have real : 1-c.value.re=0 := by simpa using congrArg Complex.re same
    linarith [c.belowOne]
  rw [←intervalIntegral.integral_of_le (by linarith : (0:ℝ)≤2*h)]
  unfold unitWeight
  rw [integral_exp_mul_complex (div_ne_zero nonzero (by norm_num : (2:ℂ)≠0))]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,Complex.ofReal_mul,Complex.ofReal_ofNat]
  congr 2
  ring

theorem actual_wave_mellin_zero (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (nonnegative:0≤h) :
    HasMellin (waveDifference c h:ℝ→ℂ) 0
      ((((Real.exp (h/2):ℂ)-Complex.exp ((star c.value-1/2)*(h:ℂ)))/(1-star c.value))*
        companionReciprocalMean c) := by
  let integral:BurnolL2:=∫t:ℝ in Ioc 0 (2*h),drivingOrbit c t
  let scalar:ℂ:=Complex.exp ((star c.value-1/2)*(h:ℂ))/2
  have native:=actual_integral_mellin_zero c zero h
  have scaled:=hasMellin_const_smul native.1 scalar
  rw [native.2,smul_eq_mul] at scaled
  have transported : HasMellin ((scalar • integral:BurnolL2):ℝ→ℂ) 0
      (scalar*((∫t:ℝ in Ioc 0 (2*h),unitWeight c t)*companionReciprocalMean c)) :=
    mellin_source_ae _ _ _ _ (ae_restrict_of_ae (s:=Ioi 0) (Lp.coeFn_smul scalar integral)) scaled
  have same : waveDifference c h=scalar • integral := actual_wave_integral c zero h nonnegative
  rw [←same,unitWeight_integral c h nonnegative] at transported
  have nonzero : (1-star c.value:ℂ)≠0 := by
    intro equality
    have real : 1-c.value.re=0 := by simpa using congrArg Complex.re equality
    linarith [c.belowOne]
  have product : Complex.exp ((star c.value-1/2)*(h:ℂ))*Complex.exp ((1-star c.value)*(h:ℂ))=
      (Real.exp (h/2):ℂ) := by
    rw [←Complex.exp_add,Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have scalarPrice : scalar*((Complex.exp ((1-star c.value)*(h:ℂ))-1)/((1-star c.value)/2))=
      ((Real.exp (h/2):ℂ)-Complex.exp ((star c.value-1/2)*(h:ℂ)))/(1-star c.value) := by
    dsimp only [scalar]
    calc
      _=(Complex.exp ((star c.value-1/2)*(h:ℂ))*
          (Complex.exp ((1-star c.value)*(h:ℂ))-1))/(1-star c.value) := by
        field_simp [nonzero]
      _=(Complex.exp ((star c.value-1/2)*(h:ℂ))*Complex.exp ((1-star c.value)*(h:ℂ))-
          Complex.exp ((star c.value-1/2)*(h:ℂ)))/(1-star c.value) := by congr 1;ring
      _=_ := by rw [product]
  convert! transported using 1
  rw [←mul_assoc,scalarPrice]

/-- Both the source pole and the complete second Unit are retained in the actual forward field. -/
theorem actual_direct_mean (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (nonnegative:0≤h) :
    directMean c h=(((Real.exp (h/2):ℂ)-Complex.exp ((star c.value-1/2)*(h:ℂ)))/(1-star c.value))*
      companionReciprocalMean c := by
  have native:=actual_wave_mellin_zero c zero h nonnegative
  have direct:=mellin_source_ae (directRaw c h) (waveDifference c h:ℝ→ℂ) 0 _
    (ae_restrict_of_ae (s:=Ioi 0) (actual_direct_raw c h).symm) native
  simpa only [mellin,zero_sub,Complex.cpow_neg_one,smul_eq_mul,directMean] using direct.2

theorem actual_difference_complete_unit (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (nonnegative:0≤h) (test:SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (waveDifference c h) test=∫x:ℝ,test x*
      ((∑'n:ℕ,((n+1:ℕ):ℂ)⁻¹*directRaw c h (x/(n+1:ℕ)))-
        (((Real.exp (h/2):ℂ)-Complex.exp ((star c.value-1/2)*(h:ℂ)))/(1-star c.value))*
          companionReciprocalMean c) := by
  rw [actual_difference_forward c zero h nonnegative]
  apply integral_congr_ae
  filter_upwards with x
  rw [actual_direct_field_series,actual_direct_mean c zero h nonnegative]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Consumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
