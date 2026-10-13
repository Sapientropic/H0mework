import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Dilation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FiniteMobiusResolventFlux
open Complex MeasureTheory Set
open scoped InnerProductSpace

def actualFluxIntegrand (z : ℂ) (value : BurnolL2) (tau : ℝ) : BurnolL2 :=
  positiveMellinQuarterRightResolventWeight z tau • (tailFlux (-tau/2) value+meanFlux (-tau/2) value)
def actualFlux (z : ℂ) (value : BurnolL2) : BurnolL2 := -(∫ tau : ℝ in Ioi 0,actualFluxIntegrand z value tau)

theorem actual_flux_integrand (z : ℂ) (value : BurnolL2) (tau : ℝ) :
    actualFluxIntegrand z value tau=M (burnolDirectRightResolventIntegrand z value tau)-
      burnolDirectRightResolventIntegrand z (M value) tau := by
  unfold actualFluxIntegrand burnolDirectRightResolventIntegrand
  rw [map_smul,← smul_sub,finite_source_dilation]

theorem actual_flux_integrable (z : ℂ) (rightQuarter : 1/4<z.re) (value : BurnolL2) :
    IntegrableOn (actualFluxIntegrand z value) (Ioi 0) := by
  have source := (M.integrable_comp (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter value)).sub
    (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter (M value))
  have same : actualFluxIntegrand z value = fun tau => M (burnolDirectRightResolventIntegrand z value tau)-
      burnolDirectRightResolventIntegrand z (M value) tau := by funext tau;exact actual_flux_integrand z value tau
  rw [same]
  exact source

-- The actual finite cutoff flux is paid before the original R source action is read.
theorem actual_M_R_action (z : ℂ) (rightQuarter : 1/4<z.re) (value : BurnolL2) :
    M (burnolDirectRightResolvent z value)=burnolDirectRightResolvent z (M value)+actualFlux z value := by
  have left := M.integrable_comp (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter value)
  have right := burnolDirectRightResolventIntegrand_integrableOn z rightQuarter (M value)
  unfold burnolDirectRightResolvent actualFlux
  rw [map_neg,← M.integral_comp_comm (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter value)]
  simp only [actual_flux_integrand]
  rw [integral_sub left right]
  module

theorem original_K_M_R_action (z : ℂ) (rightQuarter : 1/4<z.re) (coordinate : BurnolCompletedMellinCoordinate) :
    M (burnolDirectRightResolvent z (burnolCompletedMellinRieszVector coordinate : BurnolL2))=
      burnolDirectRightResolvent z (burnolMobiusSourceL2 (burnolCompletedMellinRieszVector coordinate))+
        actualFlux z (burnolCompletedMellinRieszVector coordinate : BurnolL2) := by
  rw [actual_M_R_action z rightQuarter,lower_source_physical]

end FiniteMobiusResolventFlux
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
