import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowBoundary.RuntimeConsumers

/-! The original occurrence installs its actual true-flow conservation. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowConservationRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def conservationParentRuntime := TrueFlowBoundaryRuntime.trueBoundaryRuntimeAfterFirst
def conservationParentMaterial : TrueFlowBoundaryRuntime.TrueBoundaryMaterial :=
  match TrueFlowBoundaryRuntime.trueBoundaryRuntimeFacade.readoutAt conservationParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def conservationParentResult := conservationParentMaterial.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.physical
def conservationParentHistory := conservationParentMaterial.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.history

theorem conservationParent_installed :
    type_of% (TrueFlowBoundaryRuntime.trueBoundaryRuntimeFace_factorizes conservationParentRuntime (.component .material)) ∧
    type_of% (TrueFlowBoundaryRuntime.trueBoundaryRuntimeFace_factorizes conservationParentRuntime (.component .certificate)) :=
  ⟨TrueFlowBoundaryRuntime.trueBoundaryRuntimeFace_factorizes conservationParentRuntime (.component .material),
    TrueFlowBoundaryRuntime.trueBoundaryRuntimeFace_factorizes conservationParentRuntime (.component .certificate)⟩

theorem conservationParent_actual :
    conservationParentMaterial = TrueFlowBoundaryRuntime.generatedTrueBoundaryMaterial ∧
    conservationParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    conservationParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    conservationParentResult.realized = Reentry.Source.targetRealized ∧
    conservationParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem conservationParent_clock : conservationParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  TrueFlowBoundaryRuntime.trueBoundaryParent_clock

theorem conservationParent_error_and_memory :
    conservationParentResult.realized = conservationParentResult.held + conservationParentResult.inheritedResidual +
      conservationParentResult.newNumericalResidual ∧
    ‖conservationParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  TrueFlowBoundaryRuntime.trueBoundaryParent_error_and_memory

abbrev ConservationBase := TrueFlowBoundaryRuntime.trueBoundaryLivingRoot.toAuthoritativeRoot.source
abbrev ConservationLedger := ConservationBase.restructuringSource.toLedgerSource

theorem conservationParent_same_actual_visit :
    conservationParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.TrueFlowConservationRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
