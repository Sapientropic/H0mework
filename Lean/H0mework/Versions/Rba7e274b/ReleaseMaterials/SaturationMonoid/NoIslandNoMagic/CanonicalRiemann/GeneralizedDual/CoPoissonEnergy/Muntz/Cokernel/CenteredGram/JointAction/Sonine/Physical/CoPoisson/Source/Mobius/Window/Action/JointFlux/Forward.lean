import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.JointFlux.Dilation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalJointFluxSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators

def sourceMeanResponseIntegrand (z : ℂ) (value : BurnolL2) (tau : ℝ) : BurnolL2 :=
  positiveMellinQuarterRightResolventWeight z tau •
    ((Paid.sigma*sourceMeanDifference (-tau/2) value) • Paid.box 4)
def sourceMeanResponse (z : ℂ) (value : BurnolL2) : BurnolL2 :=
  -(∫ tau : ℝ in Ioi 0,sourceMeanResponseIntegrand z value tau)

theorem source_mean_response_integrand (z : ℂ) (value : BurnolL2) (tau : ℝ) (nonnegative : 0≤tau) :
    sourceMeanResponseIntegrand z value tau=
      FiniteMobiusResolventFlux.actualFluxIntegrand z value tau+
        Paid.outerCut (burnolDirectRightResolventIntegrand z (Paid.M value) tau) := by
  unfold sourceMeanResponseIntegrand FiniteMobiusResolventFlux.actualFluxIntegrand burnolDirectRightResolventIntegrand
  rw [actual_negative_flux_source value (-tau/2) (by linarith),smul_add,map_smul,smul_neg]
  module

theorem source_mean_response_integrable (z : ℂ) (right : 1/4<z.re) (value : BurnolL2) :
    IntegrableOn (sourceMeanResponseIntegrand z value) (Ioi 0) := by
  have actual := (FiniteMobiusResolventFlux.actual_flux_integrable z right value).add
    (Paid.outerCut.integrable_comp (burnolDirectRightResolventIntegrand_integrableOn z right (Paid.M value)))
  apply actual.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau positive
  exact (source_mean_response_integrand z value tau (show 0≤tau from le_of_lt positive)).symm

 theorem actual_forward_flux_source (z : ℂ) (right : 1/4<z.re) (value : BurnolL2) :
    Paid.actualFlux z value= -Paid.outerCut (burnolDirectRightResolvent z (Paid.M value))+sourceMeanResponse z value := by
  unfold sourceMeanResponse
  have decomposition : (∫ tau : ℝ in Ioi 0,sourceMeanResponseIntegrand z value tau)=
      (∫ tau : ℝ in Ioi 0,FiniteMobiusResolventFlux.actualFluxIntegrand z value tau)+
        (∫ tau : ℝ in Ioi 0,Paid.outerCut (burnolDirectRightResolventIntegrand z (Paid.M value) tau)) := by
    rw [← integral_add (FiniteMobiusResolventFlux.actual_flux_integrable z right value)
      (Paid.outerCut.integrable_comp (burnolDirectRightResolventIntegrand_integrableOn z right (Paid.M value)))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro tau positive
    exact source_mean_response_integrand z value tau (show 0≤tau from le_of_lt positive)
  rw [decomposition]
  unfold Paid.actualFlux burnolDirectRightResolvent
  rw [map_neg,← Paid.outerCut.integral_comp_comm (burnolDirectRightResolventIntegrand_integrableOn z right (Paid.M value))]
  module
end OriginalJointFluxSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
