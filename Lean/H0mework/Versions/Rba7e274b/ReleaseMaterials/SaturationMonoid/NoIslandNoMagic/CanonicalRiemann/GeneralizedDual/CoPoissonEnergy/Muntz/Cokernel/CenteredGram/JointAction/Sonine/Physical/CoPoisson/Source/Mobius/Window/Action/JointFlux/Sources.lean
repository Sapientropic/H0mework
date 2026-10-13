import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.JointFlux.Reverse
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.JointFlux.Response
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalJointFluxSource
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource

theorem original_contact_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (FiniteMobiusResolventFlux.S.contactCorrection coordinate)=FiniteMobiusResolventFlux.S.contactCorrection coordinate := by
  unfold FiniteMobiusResolventFlux.S.contactCorrection
  rw [map_sub,map_smul,map_smul,OriginalContactFeedbackSource.original_primitive_even]
  unfold OriginalRieszFiniteSource.fourierPrimitive
  rw [← fourierL2_reflectL2_commute,OriginalContactFeedbackSource.original_primitive_even]

 theorem original_regular_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (FiniteMobiusResolventFlux.S.regularSource coordinate)=FiniteMobiusResolventFlux.S.regularSource coordinate := by
  unfold FiniteMobiusResolventFlux.S.regularSource
  simp only [map_sub,map_add,map_smul]
  have u : reflectL2 Response.wholeU=Response.wholeU := by
    unfold Response.wholeU
    change reflectL2 (burnolRadiusZeroExtension (1/4:ℝ) (Response.u:BurnolQuarterIntervalL2))=_
    rw [burnolRadiusZeroExtension_reflect,Response.u_reflection]
    rfl
  have v : reflectL2 Response.wholeV=Response.wholeV := by
    unfold Response.wholeV
    change reflectL2 (burnolRadiusZeroExtension (1/4:ℝ) (Response.v:BurnolQuarterIntervalL2))=_
    rw [burnolRadiusZeroExtension_reflect,Response.v_reflection]
    rfl
  rw [← fourierL2_reflectL2_commute,← fourierL2_reflectL2_commute,u,v]
  unfold OriginalRieszFiniteSource.fourierPrimitive
  rw [← fourierL2_reflectL2_commute,OriginalContactFeedbackSource.original_primitive_even]

 theorem original_return_response_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (OriginalReturnResponseSource.wholeReturnResponse coordinate)=OriginalReturnResponseSource.wholeReturnResponse coordinate := by
  unfold OriginalReturnResponseSource.wholeReturnResponse
  rw [OriginalReturnResponseSource.actual_return_response_coefficients]
  change reflectL2 (burnolRadiusZeroExtension (1/4:ℝ) (-Kernel.A coordinate • (Response.v:BurnolQuarterIntervalL2)+Kernel.beta coordinate • (Response.u:BurnolQuarterIntervalL2)))=_
  rw [burnolRadiusZeroExtension_reflect,map_add,map_smul,map_smul,Response.v_reflection,Response.u_reflection]
  rfl

 theorem original_Y_mean_response (coordinate : BurnolCompletedMellinCoordinate) :
    generatedMeanCoefficient (star coordinate.value/2) (OriginalContactFeedbackSource.sourceForcing coordinate)=
      Paid.sigma*(-Paid.actualMean (OriginalContactFeedbackSource.sourceForcing coordinate)/(star coordinate.value/2)-
        2*Paid.actualMean (OriginalContactFeedbackSource.sourceField coordinate)) := by
  unfold generatedMeanCoefficient
  rw [OriginalContactFeedbackSource.original_combined_R_return,map_smul]
  rfl

 theorem original_Er_mean_response (coordinate : BurnolCompletedMellinCoordinate) :
    generatedMeanCoefficient (star coordinate.value/2) (OriginalReturnResponseSource.wholeReturnResponse coordinate)=
      Paid.sigma*(-Paid.actualMean (OriginalReturnResponseSource.wholeReturnResponse coordinate)/(star coordinate.value/2)+
        2*Paid.actualMean (OriginalReturnResponseSource.correctedReturn coordinate)) := by
  unfold generatedMeanCoefficient
  rw [OriginalReturnResponseSource.original_R_return_response,map_smul]
  simp only [smul_eq_mul]
  ring
end OriginalJointFluxSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
