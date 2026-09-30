import H0mework.Chemistry.LAlanineBandRuntime.Consumers
import H0mework.Chemistry.LAlanineBandSource.Parent

/-! The original occurrence installs the whole-band source and its paid dependent restrictions. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandFlowRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def wholeBandFlowParentRuntime := WholeBandRuntime.wholeBandRuntimeAfterFirst
def wholeBandFlowParentMaterial : WholeBandRuntime.WholeBandMaterial :=
  match WholeBandRuntime.wholeBandRuntimeFacade.readoutAt wholeBandFlowParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def wholeBandFlowParentResult := WholeBandRuntime.wholeBandParentResult
def wholeBandFlowParentHistory := WholeBandRuntime.wholeBandParentHistory

theorem wholeBandFlowParent_installed :
    type_of% (WholeBandRuntime.wholeBandRuntimeFace_factorizes wholeBandFlowParentRuntime (.component .material)) ∧
    type_of% (WholeBandRuntime.wholeBandRuntimeFace_factorizes wholeBandFlowParentRuntime (.component .certificate)) :=
  ⟨WholeBandRuntime.wholeBandRuntimeFace_factorizes wholeBandFlowParentRuntime (.component .material),
    WholeBandRuntime.wholeBandRuntimeFace_factorizes wholeBandFlowParentRuntime (.component .certificate)⟩

theorem wholeBandFlowParent_actual :
    wholeBandFlowParentMaterial = WholeBandRuntime.generatedWholeBandMaterial ∧
    wholeBandFlowParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    wholeBandFlowParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    wholeBandFlowParentResult.realized = Reentry.Source.targetRealized ∧
    wholeBandFlowParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem wholeBandFlowParent_clock : wholeBandFlowParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  WholeBandRuntime.wholeBandParent_clock

theorem wholeBandFlowParent_error_and_memory :
    wholeBandFlowParentResult.realized = wholeBandFlowParentResult.held + wholeBandFlowParentResult.inheritedResidual +
      wholeBandFlowParentResult.newNumericalResidual ∧
    ‖wholeBandFlowParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  WholeBandRuntime.wholeBandParent_error_and_memory

abbrev WholeBandFlowBase := WholeBandRuntime.wholeBandLivingRoot.toAuthoritativeRoot.source
abbrev WholeBandFlowLedger := WholeBandFlowBase.restructuringSource.toLedgerSource

theorem wholeBandFlowParent_same_actual_visit :
    wholeBandFlowParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandFlowRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
