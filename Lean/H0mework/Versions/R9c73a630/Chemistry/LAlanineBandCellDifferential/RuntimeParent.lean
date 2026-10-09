import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.RuntimeConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0DifferentialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def wholeBandCell0DifferentialParentRuntime := WholeBandCell0Runtime.wholeBandCell0RuntimeAfterFirst
def wholeBandCell0DifferentialParentMaterial : WholeBandCell0Runtime.WholeBandCell0Material :=
  match WholeBandCell0Runtime.wholeBandCell0RuntimeFacade.readoutAt wholeBandCell0DifferentialParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def wholeBandCell0DifferentialParentResult := WholeBandCell0Runtime.wholeBandCell0ParentResult
def wholeBandCell0DifferentialParentHistory := WholeBandCell0Runtime.wholeBandCell0ParentHistory

theorem wholeBandCell0DifferentialParent_installed :
    type_of% (WholeBandCell0Runtime.wholeBandCell0RuntimeFace_factorizes wholeBandCell0DifferentialParentRuntime (.component .material)) ∧
    type_of% (WholeBandCell0Runtime.wholeBandCell0RuntimeFace_factorizes wholeBandCell0DifferentialParentRuntime (.component .certificate)) :=
  ⟨WholeBandCell0Runtime.wholeBandCell0RuntimeFace_factorizes wholeBandCell0DifferentialParentRuntime (.component .material),
    WholeBandCell0Runtime.wholeBandCell0RuntimeFace_factorizes wholeBandCell0DifferentialParentRuntime (.component .certificate)⟩

theorem wholeBandCell0DifferentialParent_actual :
    wholeBandCell0DifferentialParentMaterial = WholeBandCell0Runtime.generatedWholeBandCell0Material ∧
    wholeBandCell0DifferentialParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    wholeBandCell0DifferentialParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    wholeBandCell0DifferentialParentResult.realized = Reentry.Source.targetRealized ∧
    wholeBandCell0DifferentialParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem wholeBandCell0DifferentialParent_clock : wholeBandCell0DifferentialParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  WholeBandCell0Runtime.wholeBandCell0Parent_clock

theorem wholeBandCell0DifferentialParent_error_and_memory :
    wholeBandCell0DifferentialParentResult.realized = wholeBandCell0DifferentialParentResult.held + wholeBandCell0DifferentialParentResult.inheritedResidual +
      wholeBandCell0DifferentialParentResult.newNumericalResidual ∧
    ‖wholeBandCell0DifferentialParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  WholeBandCell0Runtime.wholeBandCell0Parent_error_and_memory

abbrev WholeBandCell0DifferentialBase := WholeBandCell0Runtime.wholeBandCell0LivingRoot.toAuthoritativeRoot.source
abbrev WholeBandCell0DifferentialLedger := WholeBandCell0DifferentialBase.restructuringSource.toLedgerSource

theorem wholeBandCell0DifferentialParent_same_actual_visit :
    wholeBandCell0DifferentialParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0DifferentialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
