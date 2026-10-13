import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ReturnResponse.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalReturnResponseSource
open Complex MeasureTheory
open scoped InnerProductSpace
namespace Paid
export FiniteMobiusResolventFlux (D Rplus actual_defect_R_action defectFlux)
end Paid

def generatedReturnDefect (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -(2:ℂ) • Paid.D (correctedReturn coordinate)-
    Paid.defectFlux (star coordinate.value/2) (wholeReturnResponse coordinate)

-- The original return consumes the complete actual finite cutoff flux, not a commutator label.
theorem actual_return_defect_action (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.Rplus (star coordinate.value/2) (Paid.D (wholeReturnResponse coordinate))=
      generatedReturnDefect coordinate := by
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  have source := Paid.actual_defect_R_action (star coordinate.value/2) right (wholeReturnResponse coordinate)
  rw [original_R_return_response,map_smul] at source
  exact eq_sub_of_add_eq (source.symm)

 theorem original_return_defect_occurrence (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.Rplus (star coordinate.value/2) (Paid.D (OriginalColumnMomentSource.wholeReturnResponse coordinate))=
      generatedReturnDefect coordinate := by
  rw [original_return_response_occurrence,actual_return_defect_action]

end OriginalReturnResponseSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
