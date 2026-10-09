import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.RuntimeConsumers

/-! The original whole-flow occurrence installs its source-generated differential. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferentialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def differentialParentRuntime := TrueTubeWholeRuntime.wholeTubeRuntimeAfterFirst
def differentialParentMaterial : TrueTubeWholeRuntime.WholeTubeMaterial :=
  match TrueTubeWholeRuntime.wholeTubeRuntimeFacade.readoutAt differentialParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def differentialParentResult := differentialParentMaterial.parent.parent.parent.parent.parent.parent.parent.parent.parent.physical
def differentialParentHistory := differentialParentMaterial.parent.parent.parent.parent.parent.parent.parent.parent.parent.history

theorem differentialParent_installed :
    type_of% (TrueTubeWholeRuntime.wholeTubeRuntimeFace_factorizes differentialParentRuntime (.component .material)) ∧
    type_of% (TrueTubeWholeRuntime.wholeTubeRuntimeFace_factorizes differentialParentRuntime (.component .certificate)) :=
  ⟨TrueTubeWholeRuntime.wholeTubeRuntimeFace_factorizes differentialParentRuntime (.component .material),
    TrueTubeWholeRuntime.wholeTubeRuntimeFace_factorizes differentialParentRuntime (.component .certificate)⟩

theorem differentialParent_actual :
    differentialParentMaterial = TrueTubeWholeRuntime.generatedWholeTubeMaterial ∧
    differentialParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    differentialParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    differentialParentResult.realized = Reentry.Source.targetRealized ∧
    differentialParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem differentialParent_clock : differentialParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  TrueTubeWholeRuntime.wholeTubeParent_clock

theorem differentialParent_error_and_memory :
    differentialParentResult.realized = differentialParentResult.held + differentialParentResult.inheritedResidual +
      differentialParentResult.newNumericalResidual ∧
    ‖differentialParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  TrueTubeWholeRuntime.wholeTubeParent_error_and_memory

abbrev DifferentialBase := TrueTubeWholeRuntime.wholeTubeLivingRoot.toAuthoritativeRoot.source
abbrev DifferentialLedger := DifferentialBase.restructuringSource.toLedgerSource

theorem differentialParent_same_actual_visit :
    differentialParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferentialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
