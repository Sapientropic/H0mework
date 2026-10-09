import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlow.RuntimeConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def wholeBandCell0ParentRuntime := WholeBandFlowRuntime.wholeBandFlowRuntimeAfterFirst
def wholeBandCell0ParentMaterial : WholeBandFlowRuntime.WholeBandFlowMaterial :=
  match WholeBandFlowRuntime.wholeBandFlowRuntimeFacade.readoutAt wholeBandCell0ParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def wholeBandCell0ParentResult := WholeBandFlowRuntime.wholeBandFlowParentResult
def wholeBandCell0ParentHistory := WholeBandFlowRuntime.wholeBandFlowParentHistory

theorem wholeBandCell0Parent_installed :
    type_of% (WholeBandFlowRuntime.wholeBandFlowRuntimeFace_factorizes wholeBandCell0ParentRuntime (.component .material)) ∧
    type_of% (WholeBandFlowRuntime.wholeBandFlowRuntimeFace_factorizes wholeBandCell0ParentRuntime (.component .certificate)) :=
  ⟨WholeBandFlowRuntime.wholeBandFlowRuntimeFace_factorizes wholeBandCell0ParentRuntime (.component .material),
    WholeBandFlowRuntime.wholeBandFlowRuntimeFace_factorizes wholeBandCell0ParentRuntime (.component .certificate)⟩

theorem wholeBandCell0Parent_actual :
    wholeBandCell0ParentMaterial = WholeBandFlowRuntime.generatedWholeBandFlowMaterial ∧
    wholeBandCell0ParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    wholeBandCell0ParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    wholeBandCell0ParentResult.realized = Reentry.Source.targetRealized ∧
    wholeBandCell0ParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem wholeBandCell0Parent_clock : wholeBandCell0ParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  WholeBandFlowRuntime.wholeBandFlowParent_clock

theorem wholeBandCell0Parent_error_and_memory :
    wholeBandCell0ParentResult.realized = wholeBandCell0ParentResult.held + wholeBandCell0ParentResult.inheritedResidual +
      wholeBandCell0ParentResult.newNumericalResidual ∧
    ‖wholeBandCell0ParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  WholeBandFlowRuntime.wholeBandFlowParent_error_and_memory

abbrev WholeBandCell0Base := WholeBandFlowRuntime.wholeBandFlowLivingRoot.toAuthoritativeRoot.source
abbrev WholeBandCell0Ledger := WholeBandCell0Base.restructuringSource.toLedgerSource

theorem wholeBandCell0Parent_same_actual_visit :
    wholeBandCell0ParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
