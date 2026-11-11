import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJordanSourceData
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKJointMobiusRSourceProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaSourceKernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Source.PowerWave

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKReturnJordanSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource OriginalKDirectRCofinalOutsideVolterraSource

abbrev Value := OriginalKJointMobiusSourceCalculation.Value
abbrev Var (_ : Unit) := Fin 2
abbrev Base := OriginalKJointMobiusSourceCalculation.Base
abbrev Half := OriginalKJointMobiusSourceCalculation.Half
abbrev E := Expr Value Var ()
abbrev coordinate := OriginalKJointMobiusSourceCalculation.coordinate

private def linear (action : BurnolL2 →L[ℂ] BurnolL2) (input : E) : E :=
  .linear action.toLinearMap.toAddMonoidHom input
private def scale (scalar : ℂ) (input : E) : E :=
  linear (scalar • ContinuousLinearMap.id ℂ BurnolL2) input
private def sub (left right : E) : E := .add left (scale (-1) right)
private def fourier (input : E) : E :=
  linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap input

/-- The two inputs are the existing R execution's response child and complete result. -/
def returnCode (c : BurnolCompletedMellinCoordinate) : E :=
  linear burnolEvenAmbientProjectionEndomorphism
    (linear (sourceCayley (OriginalPrimitiveRankBalance.conjugateCoordinate c))
      (.add (.var 0) (scale
        (sourceDamping (OriginalPrimitiveRankBalance.conjugateCoordinate c) : ℂ)
        (linear burnolEvenAmbientProjectionEndomorphism (fourier (.var 1))))))

def differenceCode (c : BurnolCompletedMellinCoordinate) : E :=
  sub (returnCode c) (.var 0)

def sourceAction (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  jQuarterAmplitude c • ContinuousLinearMap.id ℂ BurnolL2 -
    hQuarterAmplitude c • fourierL2.toContinuousLinearEquiv.toContinuousLinearMap

def sourceCode (c : BurnolCompletedMellinCoordinate) : E :=
  linear (sourceAction c) (differenceCode c)

def jetCode (c : BurnolCompletedMellinCoordinate) : Nat → E
  | 0 => sourceCode c
  | j+1 => linear (burnolDirectRightResolventCLM c).adjoint (jetCode c j)

def paAction : BurnolL2 →L[ℂ] BurnolL2 :=
  BurnolPaAmbientCarrier.subtypeL.comp OriginalKCombCofinalPaAction.E

def paCode (c : BurnolCompletedMellinCoordinate) (order : Nat) : E :=
  linear paAction (jetCode c order)

/-- Here variable zero is the first result of this same dependent bundle. -/
def prefixCode (c : BurnolCompletedMellinCoordinate) : Nat → E
  | 0 => .var 0
  | j+1 => linear (burnolDirectRightResolventCLM c) (prefixCode c j)

def nextCode (c : BurnolCompletedMellinCoordinate) (order : Nat) : E :=
  linear (burnolDirectRightResolventCLM c) (prefixCode c order)

def code (c : BurnolCompletedMellinCoordinate) (order : Nat) (field : Fin 2) : E :=
  Fin.cases (paCode c order) (fun _ : Fin 1 => nextCode c order) field

theorem operation_budget (c : BurnolCompletedMellinCoordinate) (order : Nat) (field : Fin 2) :
    0 < remaining (code c order field) := by
  fin_cases field <;> change 0 < _+1 <;> omega

end OriginalKReturnJordanSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
