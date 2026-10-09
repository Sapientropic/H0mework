import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowQuantitative.RuntimeConsumers
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandSource.Parent

/-! The original occurrence installs the whole-band source and its paid dependent restrictions. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def wholeBandParentRuntime := WholeBandSource.sourceParentRuntime
def wholeBandParentMaterial : TrueFlowQuantitativeRuntime.QuantitativeMaterial :=
  match TrueFlowQuantitativeRuntime.quantitativeRuntimeFacade.readoutAt wholeBandParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def wholeBandParentResult := TrueFlowQuantitativeRuntime.quantitativeParentResult
def wholeBandParentHistory := TrueFlowQuantitativeRuntime.quantitativeParentHistory

theorem wholeBandParent_installed :
    type_of% (TrueFlowQuantitativeRuntime.quantitativeRuntimeFace_factorizes wholeBandParentRuntime (.component .material)) ∧
    type_of% (TrueFlowQuantitativeRuntime.quantitativeRuntimeFace_factorizes wholeBandParentRuntime (.component .certificate)) :=
  ⟨TrueFlowQuantitativeRuntime.quantitativeRuntimeFace_factorizes wholeBandParentRuntime (.component .material),
    TrueFlowQuantitativeRuntime.quantitativeRuntimeFace_factorizes wholeBandParentRuntime (.component .certificate)⟩

theorem wholeBandParent_actual :
    wholeBandParentMaterial = TrueFlowQuantitativeRuntime.generatedQuantitativeMaterial ∧
    wholeBandParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    wholeBandParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    wholeBandParentResult.realized = Reentry.Source.targetRealized ∧
    wholeBandParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem wholeBandParent_clock : wholeBandParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  TrueFlowQuantitativeRuntime.quantitativeParent_clock

theorem wholeBandParent_error_and_memory :
    wholeBandParentResult.realized = wholeBandParentResult.held + wholeBandParentResult.inheritedResidual +
      wholeBandParentResult.newNumericalResidual ∧
    ‖wholeBandParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  TrueFlowQuantitativeRuntime.quantitativeParent_error_and_memory

abbrev WholeBandBase := TrueFlowQuantitativeRuntime.quantitativeLivingRoot.toAuthoritativeRoot.source
abbrev WholeBandLedger := WholeBandBase.restructuringSource.toLedgerSource

theorem wholeBandParent_same_actual_visit :
    wholeBandParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
