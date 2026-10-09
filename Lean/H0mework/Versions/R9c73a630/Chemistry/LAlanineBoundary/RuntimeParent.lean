import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.RuntimeConsumers

/-! Same-root boundary authority and inherited source inventory. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.BoundaryRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def boundaryParentRuntime := WholeCellRuntime.wholeRuntimeAfterFirst
def boundaryParentMaterial : WholeCellRuntime.WholeCellMaterial :=
  match WholeCellRuntime.wholeRuntimeFacade.readoutAt boundaryParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def boundaryParentResult := boundaryParentMaterial.parent.parent.parent.parent.parent.parent.physical
def boundaryParentHistory := boundaryParentMaterial.parent.parent.parent.parent.parent.parent.history

theorem boundaryParent_installed :
    type_of% (WholeCellRuntime.wholeRuntimeFace_factorizes boundaryParentRuntime (.component .material)) ∧
    type_of% (WholeCellRuntime.wholeRuntimeFace_factorizes boundaryParentRuntime (.component .certificate)) :=
  ⟨WholeCellRuntime.wholeRuntimeFace_factorizes boundaryParentRuntime (.component .material),
    WholeCellRuntime.wholeRuntimeFace_factorizes boundaryParentRuntime (.component .certificate)⟩

theorem boundaryParent_actual :
    boundaryParentMaterial = WholeCellRuntime.generatedWholeCellMaterial ∧
    boundaryParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    boundaryParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    boundaryParentResult.realized = Reentry.Source.targetRealized ∧
    boundaryParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem boundaryParent_clock : boundaryParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  WholeCellRuntime.wholeParent_clock

theorem boundaryParent_error_and_memory :
    boundaryParentResult.realized = boundaryParentResult.held + boundaryParentResult.inheritedResidual +
      boundaryParentResult.newNumericalResidual ∧
    ‖boundaryParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  WholeCellRuntime.wholeParent_error_and_memory

abbrev BoundaryBase := WholeCellRuntime.wholeLivingRoot.toAuthoritativeRoot.source
abbrev BoundaryLedger := BoundaryBase.restructuringSource.toLedgerSource

theorem boundaryParent_same_actual_visit :
    boundaryParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.BoundaryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
