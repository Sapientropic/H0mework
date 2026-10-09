import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.RuntimeConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0SpatialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def wholeBandCell0SpatialParentRuntime := WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialRuntimeAfterFirst
def wholeBandCell0SpatialParentMaterial : WholeBandCell0DifferentialRuntime.WholeBandCell0DifferentialMaterial :=
  match WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialRuntimeFacade.readoutAt wholeBandCell0SpatialParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def wholeBandCell0SpatialParentResult := WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialParentResult
def wholeBandCell0SpatialParentHistory := WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialParentHistory

theorem wholeBandCell0SpatialParent_installed :
    type_of% (WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialRuntimeFace_factorizes wholeBandCell0SpatialParentRuntime (.component .material)) ∧
    type_of% (WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialRuntimeFace_factorizes wholeBandCell0SpatialParentRuntime (.component .certificate)) :=
  ⟨WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialRuntimeFace_factorizes wholeBandCell0SpatialParentRuntime (.component .material),
    WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialRuntimeFace_factorizes wholeBandCell0SpatialParentRuntime (.component .certificate)⟩

theorem wholeBandCell0SpatialParent_actual :
    wholeBandCell0SpatialParentMaterial = WholeBandCell0DifferentialRuntime.generatedWholeBandCell0DifferentialMaterial ∧
    wholeBandCell0SpatialParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    wholeBandCell0SpatialParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    wholeBandCell0SpatialParentResult.realized = Reentry.Source.targetRealized ∧
    wholeBandCell0SpatialParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem wholeBandCell0SpatialParent_clock : wholeBandCell0SpatialParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialParent_clock

theorem wholeBandCell0SpatialParent_error_and_memory :
    wholeBandCell0SpatialParentResult.realized = wholeBandCell0SpatialParentResult.held + wholeBandCell0SpatialParentResult.inheritedResidual +
      wholeBandCell0SpatialParentResult.newNumericalResidual ∧
    ‖wholeBandCell0SpatialParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialParent_error_and_memory

abbrev WholeBandCell0SpatialBase := WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialLivingRoot.toAuthoritativeRoot.source
abbrev WholeBandCell0SpatialLedger := WholeBandCell0SpatialBase.restructuringSource.toLedgerSource

theorem wholeBandCell0SpatialParent_same_actual_visit :
    wholeBandCell0SpatialParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0SpatialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
