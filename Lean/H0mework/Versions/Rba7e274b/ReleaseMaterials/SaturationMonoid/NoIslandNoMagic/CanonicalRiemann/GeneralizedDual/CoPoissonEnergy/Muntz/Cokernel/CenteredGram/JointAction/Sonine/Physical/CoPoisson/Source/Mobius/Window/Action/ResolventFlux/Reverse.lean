import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Resolvent
import H0mework.Versions.V2.Arithmetic.RiemannResolvent.CompleteTate
import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.Algebra
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FiniteMobiusResolventFlux
open Complex MeasureTheory Set
open scoped InnerProductSpace

def RplusIntegrand (z : ℂ) (value : BurnolL2) (tau : ℝ) : BurnolL2 :=
  positiveMellinQuarterRightResolventWeight z tau • burnolMultiplicativeDilation (tau/2) value
def Rplus (z : ℂ) (value : BurnolL2) : BurnolL2 := -(∫ tau : ℝ in Ioi 0,RplusIntegrand z value tau)
def reverseFluxIntegrand (z : ℂ) (value : BurnolL2) (tau : ℝ) : BurnolL2 :=
  positiveMellinQuarterRightResolventWeight z tau • (tailFlux (tau/2) value+meanFlux (tau/2) value)
def reverseFlux (z : ℂ) (value : BurnolL2) : BurnolL2 := -(∫ tau : ℝ in Ioi 0,reverseFluxIntegrand z value tau)

theorem Rplus_integrable (z : ℂ) (rightQuarter : 1/4<z.re) (value : BurnolL2) : IntegrableOn (RplusIntegrand z value) (Ioi 0) := by
  have actual := burnolTateReciprocalL2.integrable_comp
    (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter (burnolTateReciprocalL2 value))
  apply actual.congr
  filter_upwards with tau
  unfold RplusIntegrand burnolDirectRightResolventIntegrand
  rw [map_smul]
  have action := burnolTateReciprocalL2_dilation_inverse (tau/2) (burnolTateReciprocalL2 value)
  rw [burnolTateReciprocalL2_involutive] at action
  simpa only [neg_div] using congrArg
    (fun field : BurnolL2 => positiveMellinQuarterRightResolventWeight z tau • field) action.symm


theorem tate_R (z : ℂ) (rightQuarter : 1/4<z.re) (value : BurnolL2) :
    burnolTateReciprocalL2 (burnolDirectRightResolvent z value)=Rplus z (burnolTateReciprocalL2 value) :=
  burnolTateReciprocalL2_directRightResolvent z rightQuarter value

theorem Rplus_tate (z : ℂ) (rightQuarter : 1/4<z.re) (value : BurnolL2) :
    Rplus z value=burnolTateReciprocalL2 (burnolDirectRightResolvent z (burnolTateReciprocalL2 value)) := by
  rw [tate_R z rightQuarter,burnolTateReciprocalL2_involutive]

theorem Rplus_sub (z : ℂ) (rightQuarter : 1/4<z.re) (left right : BurnolL2) :
    Rplus z (left-right)=Rplus z left-Rplus z right := by
  rw [Rplus_tate z rightQuarter,Rplus_tate z rightQuarter,Rplus_tate z rightQuarter,map_sub,
    burnolDirectRightResolvent_sub z rightQuarter,map_sub]

theorem Rplus_smul (z c : ℂ) (rightQuarter : 1/4<z.re) (value : BurnolL2) :
    Rplus z (c • value)=c • Rplus z value := by
  rw [Rplus_tate z rightQuarter,Rplus_tate z rightQuarter,map_smul,burnolDirectRightResolvent_smul,map_smul]

theorem reverse_flux_integrand (z : ℂ) (value : BurnolL2) (tau : ℝ) :
    reverseFluxIntegrand z value tau=M (RplusIntegrand z value tau)-RplusIntegrand z (M value) tau := by
  unfold reverseFluxIntegrand RplusIntegrand
  rw [map_smul,← smul_sub,finite_source_dilation]

theorem reverse_flux_integrable (z : ℂ) (rightQuarter : 1/4<z.re) (value : BurnolL2) :
    IntegrableOn (reverseFluxIntegrand z value) (Ioi 0) := by
  have source := (M.integrable_comp (Rplus_integrable z rightQuarter value)).sub (Rplus_integrable z rightQuarter (M value))
  have same : reverseFluxIntegrand z value=fun tau=>M (RplusIntegrand z value tau)-RplusIntegrand z (M value) tau := by
    funext tau;exact reverse_flux_integrand z value tau
  rw [same]
  exact source

theorem actual_M_Rplus_action (z : ℂ) (rightQuarter : 1/4<z.re) (value : BurnolL2) :
    M (Rplus z value)=Rplus z (M value)+reverseFlux z value := by
  unfold Rplus reverseFlux
  rw [map_neg,← M.integral_comp_comm (Rplus_integrable z rightQuarter value)]
  simp only [reverse_flux_integrand]
  rw [integral_sub (M.integrable_comp (Rplus_integrable z rightQuarter value)) (Rplus_integrable z rightQuarter (M value))]
  module

theorem fourier_R (z : ℂ) (rightQuarter : 1/4<z.re) (value : BurnolL2) :
    fourierL2 (burnolDirectRightResolvent z value)=Rplus z (fourierL2 value) := by
  unfold burnolDirectRightResolvent Rplus
  rw [map_neg]
  have mapped := fourierL2.toLinearIsometry.toContinuousLinearMap.integral_comp_comm (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter value)
  simp only [LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry] at mapped
  rw [← mapped]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro tau _
  change fourierL2 (positiveMellinQuarterRightResolventWeight z tau • burnolMultiplicativeDilation (-tau/2) value)=
    positiveMellinQuarterRightResolventWeight z tau • burnolMultiplicativeDilation (tau/2) (fourierL2 value)
  rw [map_smul,fourierL2_burnolMultiplicativeDilation]
  rw [show -(-tau/2)=tau/2 by ring]

theorem Rplus_identity (z w : ℂ) (zRight : 1/4<z.re) (wRight : 1/4<w.re) (value : BurnolL2) :
    Rplus z value-Rplus w value=(z-w) • Rplus z (Rplus w value) := by
  rw [Rplus_tate z zRight,Rplus_tate w wRight,← map_sub,burnolDirectRightResolvent_identity z w zRight wRight,map_smul]
  simp only [Rplus_tate z zRight,burnolTateReciprocalL2_involutive]

-- The paid source resolvent identity supplies the actual inverse, including z=w.
theorem source_resolvent_inverse (z w : ℂ) (zRight : 1/4<z.re) (wRight : 1/4<w.re) (value : BurnolL2) :
    -( (w-z) • Rplus z value-value)-(w-z) • Rplus w ((w-z) • Rplus z value-value)=value := by
  rw [Rplus_sub w wRight,Rplus_smul w (w-z) wRight]
  have source := Rplus_identity w z wRight zRight value
  rw [smul_sub,smul_smul]
  have scaled := congrArg (fun field : BurnolL2 => (w-z) • field) source
  rw [smul_smul] at scaled
  rw [← scaled]
  rw [smul_sub]
  module

end FiniteMobiusResolventFlux
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
