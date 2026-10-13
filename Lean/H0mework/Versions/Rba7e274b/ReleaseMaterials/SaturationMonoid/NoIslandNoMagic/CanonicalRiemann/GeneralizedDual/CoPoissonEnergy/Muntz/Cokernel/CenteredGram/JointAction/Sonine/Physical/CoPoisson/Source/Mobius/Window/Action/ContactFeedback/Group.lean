import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ContactFeedback.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalContactFeedbackSource
open Complex MeasureTheory Set
open scoped InnerProductSpace
open OriginalRieszSource
namespace Paid
export FiniteMobiusResolventFlux (M D Rplus Rplus_sub Rplus_smul actualFlux)
end Paid

theorem original_primitive_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (OriginalRieszFiniteSource.edgePrimitive coordinate)=OriginalRieszFiniteSource.edgePrimitive coordinate := by
  unfold OriginalRieszFiniteSource.edgePrimitive burnolAmbientEvenPart
  rw [map_smul,map_smul,map_add,reflectL2_reflectL2]
  module

 theorem original_fourier_primitive_return (coordinate : BurnolCompletedMellinCoordinate) :
    fourierL2 (OriginalRieszFiniteSource.fourierPrimitive coordinate)=OriginalRieszFiniteSource.edgePrimitive coordinate := by
  unfold OriginalRieszFiniteSource.fourierPrimitive
  rw [fourierL2_fourierL2,original_primitive_even]

 def retainedPrimitiveReturn (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Paid.Rplus (star coordinate.value/2) (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))

 def generatedContactAction (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -(burnolTateReciprocalL2 (generatedCombinedReturn coordinate))+
    OriginalReturnResponseSource.generatedReturnDefect coordinate-
      (2*(star coordinate.value-1/2)*Kernel.beta coordinate) • retainedPrimitiveReturn coordinate

-- F² is reduced only on the original even primitive, and the remaining P return retains its actual source price.
theorem original_complete_contact_action (coordinate : BurnolCompletedMellinCoordinate) :
    OriginalFourierMobiusReturnSource.generatedEtaAction coordinate=generatedContactAction coordinate := by
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  rw [← OriginalFourierMobiusReturnSource.original_eta_fourier_action]
  unfold OriginalReturnResponseSource.retainedEtaAction generatedContactAction retainedPrimitiveReturn
  have primitive : Paid.D (OriginalRieszFiniteSource.fourierPrimitive coordinate)=
      Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)-
        burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)) := by
    unfold Paid.D
    simp only [sub_apply,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry]
    rw [original_fourier_primitive_return]
  rw [primitive,Paid.Rplus_sub _ right]
  have combined := original_combined_Tate_return coordinate
  unfold sourceForcing at combined
  rw [map_sub,map_smul,map_sub,map_smul,Paid.Rplus_sub _ right,Paid.Rplus_smul _ _ right] at combined
  rw [← combined]
  module

end OriginalContactFeedbackSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
