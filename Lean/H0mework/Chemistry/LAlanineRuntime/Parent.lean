import H0mework.Chemistry.LAlanineRefinementRuntime.RefinementRuntimeRegression

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.ContinuousRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def bandParentRuntime := Runtime.refinementRuntimeAfterFirst
def bandParentMaterial : Runtime.RefinementMaterial :=
  match Runtime.refinementRuntimeFacade.readoutAt bandParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def bandParentResult := bandParentMaterial.parent.parent.parent.physical
def bandParentHistory := bandParentMaterial.parent.parent.parent.history

theorem bandParent_installed :
    type_of% (Runtime.refinementRuntimeFace_factorizes bandParentRuntime (.component .material)) ∧
    type_of% (Runtime.refinementRuntimeFace_factorizes bandParentRuntime (.component .certificate)) :=
  ⟨Runtime.refinementRuntimeFace_factorizes bandParentRuntime (.component .material),
    Runtime.refinementRuntimeFace_factorizes bandParentRuntime (.component .certificate)⟩

theorem bandParent_actual :
    bandParentMaterial = Runtime.generatedRefinementMaterial ∧
    bandParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    bandParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    bandParentResult.realized = Reentry.Source.targetRealized ∧
    bandParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem bandParent_clock : bandParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  Runtime.refinementParent_clock

theorem bandParent_error_and_memory :
    bandParentResult.realized = bandParentResult.held + bandParentResult.inheritedResidual +
      bandParentResult.newNumericalResidual ∧
    ‖bandParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  Runtime.refinementParent_error_and_memory

abbrev BandBase := Runtime.refinementLivingRoot.toAuthoritativeRoot.source
abbrev BandLedger := BandBase.restructuringSource.toLedgerSource

theorem bandParent_same_actual_visit :
    bandParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.ContinuousRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
