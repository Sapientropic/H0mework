import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKCoefficientBSelfCalculation
import H0mework.Versions.R7e4da746.Arithmetic.MobiusSource.Tate
import H0mework.Versions.R7e4da746.Arithmetic.MellinProjection.PaBoundaryCommutator

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKJointMobiusSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution

abbrev Value := OriginalKCoefficientBSelfCalculation.Value
abbrev Var := OriginalKCoefficientBSelfCalculation.Var
abbrev Base := OriginalKCoefficientBSelfCalculation.Base
abbrev Half := OriginalKCoefficientBSelfCalculation.Half
abbrev E := OriginalKCoefficientBSelfCalculation.E
abbrev sourceEnvironment := OriginalKCoefficientBSelfCalculation.sourceEnvironment
abbrev coordinate := OriginalKCoefficientBSelfCalculation.coordinate
abbrev fixedShift := OriginalKCoefficientBSelfCalculation.fixedShift

/-- The complete boundary acts on the calculated elementary and two B subtrees. -/
def sourceCode (c : BurnolCompletedMellinCoordinate) : E :=
  OriginalKBFiniteCalculation.boundaryActionCode c fixedShift
    (OriginalKCoefficientBSelfCalculation.sourceKernelCode c)

/-- The inverse is an action on the actual boundary, rather than an inverse-source leaf. -/
def code (c : BurnolCompletedMellinCoordinate) : E :=
  .linear (burnolMobiusSourceL2.comp burnolEvenAmbientProjection).toLinearMap.toAddMonoidHom
    (sourceCode c)

theorem operation_budget (c : BurnolCompletedMellinCoordinate) :
    0 < remaining (code c) := by
  change 0 < remaining (sourceCode c) + 1
  omega

def reader (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()) :=
  { environment := sourceEnvironment
    expression := code (coordinate observation nontrivial half occurrence) }

theorem reader_source (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (reader observation nontrivial half occurrence).environment = sourceEnvironment ∧
      (coordinate observation nontrivial half occurrence).value = observation.coordinate ∧
      (reader observation nontrivial half occurrence).expression =
        code (coordinate observation nontrivial half occurrence) := ⟨rfl, rfl, rfl⟩

end OriginalKJointMobiusSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
