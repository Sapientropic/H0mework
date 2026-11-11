import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJordanSourceProgram

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKReturnJetStepSourceCalculation
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution

abbrev Value := OriginalKReturnJordanSourceCalculation.Value
abbrev Var := OriginalKReturnJordanSourceCalculation.Var
abbrev Base := OriginalKReturnJordanSourceCalculation.Base
abbrev Half := OriginalKReturnJordanSourceCalculation.Half
abbrev E := Expr Value Var ()

private def linear (action : BurnolL2 →L[ℂ] BurnolL2) (input : E) : E :=
  .linear action.toLinearMap.toAddMonoidHom input

/-- The input is the prior execution's full jet child, before any Pa projection. -/
def stepCode (c : BurnolCompletedMellinCoordinate) : E :=
  linear (burnolDirectRightResolventCLM c).adjoint (.var 0)

def paCode (c : BurnolCompletedMellinCoordinate) : E :=
  linear OriginalKReturnJordanSourceCalculation.paAction (stepCode c)

/-- The second reader borrows this execution's Pa result and retains the original forward actor. -/
abbrev prefixCode := OriginalKReturnJordanSourceCalculation.prefixCode
abbrev nextCode := OriginalKReturnJordanSourceCalculation.nextCode

def code (c : BurnolCompletedMellinCoordinate) (order : Nat) (field : Fin 2) : E :=
  Fin.cases (paCode c) (fun _ : Fin 1 => nextCode c order) field

theorem operation_budget (c : BurnolCompletedMellinCoordinate) (order : Nat) (field : Fin 2) :
    0 < remaining (code c order field) := by
  fin_cases field <;> change 0 < _ + 1 <;> omega

end OriginalKReturnJetStepSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
