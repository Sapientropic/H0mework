import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJetStepSourceProgram
import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.ProjectedSourceCompact

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPaNativePortSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution

abbrev Value := OriginalKReturnJetStepSourceCalculation.Value
abbrev Var := OriginalKReturnJetStepSourceCalculation.Var
abbrev Base := OriginalKReturnJetStepSourceCalculation.Base
abbrev Half := OriginalKReturnJetStepSourceCalculation.Half
abbrev E := Expr Value Var ()

local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def unitAction (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  ((burnolPaResolventSourceCoefficient c).smulRight (burnolUnitTailResponse c 4)).comp
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).orthogonalProjectionOnto

private def linear (action : BurnolL2 →L[ℂ] BurnolL2) (input : E) : E :=
  .linear action.toLinearMap.toAddMonoidHom input

def rCode (c : BurnolCompletedMellinCoordinate) : E :=
  linear (burnolDirectRightResolventCLM c) (.var 0)

/-- Variable zero is the first reader's actual R Result; variable one is its actual Pa input. -/
def correctionCode (c : BurnolCompletedMellinCoordinate) : E :=
  .add (.var 0) (linear (-unitAction c) (.var 1))

def code (c : BurnolCompletedMellinCoordinate) (field : Fin 2) : E :=
  Fin.cases (rCode c) (fun _ : Fin 1 => correctionCode c) field

theorem operation_budget (c : BurnolCompletedMellinCoordinate) (field : Fin 2) :
    0 < remaining (code c field) := by
  fin_cases field <;> change 0 < _ + 1 <;> omega

end OriginalKPaNativePortSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
