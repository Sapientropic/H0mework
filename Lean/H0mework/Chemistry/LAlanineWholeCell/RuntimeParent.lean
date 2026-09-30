import H0mework.Chemistry.LAlanineSpatialRuntime.Consumers

/-! Read the actual spatial material from the original sealed parent runtime. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def wholeParentRuntime := SpatialRuntime.spatialRuntimeAfterFirst
def wholeParentMaterial : SpatialRuntime.SpatialMaterial :=
  match SpatialRuntime.spatialRuntimeFacade.readoutAt wholeParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def wholeParentResult := wholeParentMaterial.parent.parent.parent.parent.parent.physical
def wholeParentHistory := wholeParentMaterial.parent.parent.parent.parent.parent.history

theorem wholeParent_installed :
    type_of% (SpatialRuntime.spatialRuntimeFace_factorizes wholeParentRuntime (.component .material)) ∧
    type_of% (SpatialRuntime.spatialRuntimeFace_factorizes wholeParentRuntime (.component .certificate)) :=
  ⟨SpatialRuntime.spatialRuntimeFace_factorizes wholeParentRuntime (.component .material),
    SpatialRuntime.spatialRuntimeFace_factorizes wholeParentRuntime (.component .certificate)⟩

theorem wholeParent_actual :
    wholeParentMaterial = SpatialRuntime.generatedSpatialMaterial ∧
    wholeParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    wholeParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    wholeParentResult.realized = Reentry.Source.targetRealized ∧
    wholeParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem wholeParent_clock : wholeParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  SpatialRuntime.spatialParent_clock

theorem wholeParent_error_and_memory :
    wholeParentResult.realized = wholeParentResult.held + wholeParentResult.inheritedResidual +
      wholeParentResult.newNumericalResidual ∧
    ‖wholeParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  SpatialRuntime.spatialParent_error_and_memory

abbrev WholeBase := SpatialRuntime.spatialLivingRoot.toAuthoritativeRoot.source
abbrev WholeLedger := WholeBase.restructuringSource.toLedgerSource

theorem wholeParent_same_actual_visit :
    wholeParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.WholeCellRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
