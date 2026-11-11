import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPaNativePortSourceProgram

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPaNativeCayleySourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource

abbrev Value := OriginalKPaNativePortSourceCalculation.Value
abbrev Var := OriginalKPaNativePortSourceCalculation.Var
abbrev Base := OriginalKPaNativePortSourceCalculation.Base
abbrev Half := OriginalKPaNativePortSourceCalculation.Half
abbrev E := Expr Value Var ()

private def linear (action : BurnolL2 →L[ℂ] BurnolL2) (input : E) : E :=
  .linear action.toLinearMap.toAddMonoidHom input
private def scale (scalar : ℂ) (input : E) : E :=
  linear (scalar • ContinuousLinearMap.id ℂ BurnolL2) input

abbrev paAction := OriginalKReturnJordanSourceCalculation.paAction

def qAction : BurnolL2 →L[ℂ] BurnolL2 :=
  BurnolPaAmbientCarrier.subtypeL.comp OriginalKCombCofinalPaAction.Q

/-- Variable zero is the prior actual R Result and variable one is its original Pa Result. -/
def rawCode (c : BurnolCompletedMellinCoordinate) : E :=
  .add (.var 1) (scale (sourceDamping c : ℂ) (.var 0))

/-- Both projection readers borrow variable zero from the same first actual U Result. -/
def paCode : E := linear paAction (.var 0)
def qCode : E := linear qAction (.var 0)

def code (c : BurnolCompletedMellinCoordinate) (field : Fin 3) : E :=
  Fin.cases (rawCode c) (fun rest : Fin 2 =>
    Fin.cases paCode (fun _ : Fin 1 => qCode) rest) field

theorem operation_budget (c : BurnolCompletedMellinCoordinate) (field : Fin 3) :
    0 < remaining (code c field) := by
  fin_cases field <;> change 0 < _ + 1 <;> omega

end OriginalKPaNativeCayleySourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
