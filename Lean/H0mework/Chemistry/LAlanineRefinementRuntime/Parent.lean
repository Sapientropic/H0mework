import H0mework.Chemistry.LAlanineBasinPartition.RuntimeBasinRuntimeRegression

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def refinementParentRuntime := BasinPartition.Runtime.basinRuntimeAfterFirst

def refinementParentMaterial : BasinPartition.Runtime.BasinMaterial :=
  match BasinPartition.Runtime.basinRuntimeFacade.readoutAt refinementParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def refinementParentResult := refinementParentMaterial.parent.parent.physical
def refinementParentFrame := refinementParentResult.nuclear.target
def refinementParentLedger := refinementParentResult.nuclear.targetLedger
def refinementParentFullState := refinementParentResult.realized
def refinementParentHistory := refinementParentMaterial.parent.parent.history
def refinementParentCharge := refinementParentMaterial.parent.decoded
def refinementParentTime := refinementParentResult.clock

theorem refinementParent_installed :
    type_of% (BasinPartition.Runtime.basinRuntimeFace_factorizes refinementParentRuntime (.component .material)) ∧
    type_of% (BasinPartition.Runtime.basinRuntimeFace_factorizes refinementParentRuntime (.component .certificate)) :=
  ⟨BasinPartition.Runtime.basinRuntimeFace_factorizes refinementParentRuntime (.component .material),
    BasinPartition.Runtime.basinRuntimeFace_factorizes refinementParentRuntime (.component .certificate)⟩

theorem refinementParent_actual :
    refinementParentMaterial = BasinPartition.Runtime.generatedBasinMaterial ∧
    refinementParentFrame = Reentry.Source.stepReadout.nuclear.target ∧
    refinementParentLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    refinementParentFullState = Reentry.Source.targetRealized ∧
    refinementParentHistory = Reentry.Runtime.reentrySourceHistory ∧
    refinementParentCharge = ChargeIdentity.Source.decodedCharge := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem refinementParent_clock : refinementParentTime = 3 * Propagation.Producer.nativeClockStep :=
  BasinPartition.Runtime.basinParent_clock

theorem refinementParent_error_and_memory :
    refinementParentResult.realized = refinementParentResult.held + refinementParentResult.inheritedResidual +
      refinementParentResult.newNumericalResidual ∧
    ‖refinementParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  BasinPartition.Runtime.basinParent_error_and_memory

abbrev RefinementBase := BasinPartition.Runtime.basinLivingRoot.toAuthoritativeRoot.source
abbrev RefinementLedger := RefinementBase.restructuringSource.toLedgerSource

theorem refinementParent_same_actual_visit :
    refinementParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
