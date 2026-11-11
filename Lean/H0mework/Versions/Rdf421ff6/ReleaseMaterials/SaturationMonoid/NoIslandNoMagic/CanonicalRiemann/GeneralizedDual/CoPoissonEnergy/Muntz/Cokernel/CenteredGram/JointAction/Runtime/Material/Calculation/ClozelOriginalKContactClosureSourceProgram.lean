import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKJointMobiusSourceProgram
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.SourceData
import H0mework.Versions.V2.Arithmetic.RiemannFirstSource.GeneratorResolventOperator

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKContactClosureSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalKPairedBEulerJunctionSource

abbrev Value := OriginalKJointMobiusSourceCalculation.Value
abbrev Var (_ : Unit) := Fin 3
abbrev Base := OriginalKJointMobiusSourceCalculation.Base
abbrev Half := OriginalKJointMobiusSourceCalculation.Half
abbrev E := Expr Value Var ()
abbrev coordinate := OriginalKJointMobiusSourceCalculation.coordinate

private def linear (action : BurnolL2 →L[ℂ] BurnolL2) (input : E) : E :=
  .linear action.toLinearMap.toAddMonoidHom input
private def scale (scalar : ℂ) (input : E) : E :=
  linear (scalar • ContinuousLinearMap.id ℂ BurnolL2) input

def positionAction (d : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  (1-star d.value) • (burnolDirectRightResolventCLM d).adjoint -
    (2 : ℂ) • ContinuousLinearMap.id ℂ BurnolL2

def fourierAction (d : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  star d.value • (burnolDirectRightResolventCLM d).adjoint +
    (2 : ℂ) • ContinuousLinearMap.id ℂ BurnolL2

def regularCode (d : BurnolCompletedMellinCoordinate) : E :=
  linear (burnolDirectRightResolventCLM d).adjoint (.var 0)

/-- Each signed contact keeps its own action node and its actual source-slot child. -/
def contactCode (c d : BurnolCompletedMellinCoordinate) (field : Fin 4) : E :=
  ![scale (sourceJump c 0) (linear (positionAction d) (.var 1)),
    scale (-sourceTrace c 0) (linear (positionAction d) (.var 2)),
    scale (-sourceJump c 1) (linear (fourierAction d)
      (linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap (.var 1))),
    scale (sourceTrace c 1) (linear (fourierAction d)
      (linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap (.var 2)))] field

def contactsCode (c d : BurnolCompletedMellinCoordinate) : E :=
  .add (.add (.add (contactCode c d 0) (contactCode c d 1))
    (contactCode c d 2)) (contactCode c d 3)

def effectCode (c d : BurnolCompletedMellinCoordinate) : E :=
  .add (regularCode d) (contactsCode c d)

def inputCode (c d : BurnolCompletedMellinCoordinate) : E :=
  linear burnolEvenAmbientProjectionEndomorphism (effectCode c d)

def code (c d : BurnolCompletedMellinCoordinate) : E :=
  linear (burnolDirectRightResolventCLM d) (inputCode c d)

theorem operation_budget (c d : BurnolCompletedMellinCoordinate) :
    0 < remaining (code c d) := by
  change 0 < remaining (inputCode c d)+1
  omega

/-- The three source fields are regular, junction step and quarter step, before any contact action. -/
def reader (source : Env Value Var) (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : Half observation) (d : BurnolCompletedMellinCoordinate)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()) :=
  { environment := source
    expression := code (coordinate observation nontrivial half occurrence) d }

theorem reader_source (source : Env Value Var) (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : Half observation) (d : BurnolCompletedMellinCoordinate)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (reader source observation nontrivial half d occurrence).environment = source ∧
      (coordinate observation nontrivial half occurrence).value = observation.coordinate ∧
      (reader source observation nontrivial half d occurrence).expression =
        code (coordinate observation nontrivial half occurrence) d := ⟨rfl,rfl,rfl⟩

end OriginalKContactClosureSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
