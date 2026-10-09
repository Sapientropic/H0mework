import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.RuntimeConsumers

/-! The same occurrence installs its complete original signed-gradient window. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def wholeTubeParentRuntime := TrueTubeRuntime.tubeRuntimeAfterFirst
def wholeTubeParentMaterial : TrueTubeRuntime.TrueTubeMaterial :=
  match TrueTubeRuntime.tubeRuntimeFacade.readoutAt wholeTubeParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def wholeTubeParentResult := wholeTubeParentMaterial.parent.parent.parent.parent.parent.parent.parent.parent.physical
def wholeTubeParentHistory := wholeTubeParentMaterial.parent.parent.parent.parent.parent.parent.parent.parent.history

theorem wholeTubeParent_installed :
    type_of% (TrueTubeRuntime.tubeRuntimeFace_factorizes wholeTubeParentRuntime (.component .material)) ∧
    type_of% (TrueTubeRuntime.tubeRuntimeFace_factorizes wholeTubeParentRuntime (.component .certificate)) :=
  ⟨TrueTubeRuntime.tubeRuntimeFace_factorizes wholeTubeParentRuntime (.component .material),
    TrueTubeRuntime.tubeRuntimeFace_factorizes wholeTubeParentRuntime (.component .certificate)⟩

theorem wholeTubeParent_actual :
    wholeTubeParentMaterial = TrueTubeRuntime.generatedTrueTubeMaterial ∧
    wholeTubeParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    wholeTubeParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    wholeTubeParentResult.realized = Reentry.Source.targetRealized ∧
    wholeTubeParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem wholeTubeParent_clock : wholeTubeParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  TrueTubeRuntime.tubeParent_clock

theorem wholeTubeParent_error_and_memory :
    wholeTubeParentResult.realized = wholeTubeParentResult.held + wholeTubeParentResult.inheritedResidual +
      wholeTubeParentResult.newNumericalResidual ∧
    ‖wholeTubeParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  TrueTubeRuntime.tubeParent_error_and_memory

abbrev WholeTubeBase := TrueTubeRuntime.tubeLivingRoot.toAuthoritativeRoot.source
abbrev WholeTubeLedger := WholeTubeBase.restructuringSource.toLedgerSource

theorem wholeTubeParent_same_actual_visit :
    wholeTubeParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
