import H0mework.Chemistry.LAlanineTrueFlowGeometry.RuntimeConsumers

/-! The original occurrence installs its generated true-flow boundary. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowBoundaryRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def trueBoundaryParentRuntime := TrueFlowGeometryRuntime.geometryRuntimeAfterFirst
def trueBoundaryParentMaterial : TrueFlowGeometryRuntime.GeometryMaterial :=
  match TrueFlowGeometryRuntime.geometryRuntimeFacade.readoutAt trueBoundaryParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def trueBoundaryParentResult := trueBoundaryParentMaterial.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.physical
def trueBoundaryParentHistory := trueBoundaryParentMaterial.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.history

theorem trueBoundaryParent_installed :
    type_of% (TrueFlowGeometryRuntime.geometryRuntimeFace_factorizes trueBoundaryParentRuntime (.component .material)) ∧
    type_of% (TrueFlowGeometryRuntime.geometryRuntimeFace_factorizes trueBoundaryParentRuntime (.component .certificate)) :=
  ⟨TrueFlowGeometryRuntime.geometryRuntimeFace_factorizes trueBoundaryParentRuntime (.component .material),
    TrueFlowGeometryRuntime.geometryRuntimeFace_factorizes trueBoundaryParentRuntime (.component .certificate)⟩

theorem trueBoundaryParent_actual :
    trueBoundaryParentMaterial = TrueFlowGeometryRuntime.generatedGeometryMaterial ∧
    trueBoundaryParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    trueBoundaryParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    trueBoundaryParentResult.realized = Reentry.Source.targetRealized ∧
    trueBoundaryParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem trueBoundaryParent_clock : trueBoundaryParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  TrueFlowGeometryRuntime.geometryParent_clock

theorem trueBoundaryParent_error_and_memory :
    trueBoundaryParentResult.realized = trueBoundaryParentResult.held + trueBoundaryParentResult.inheritedResidual +
      trueBoundaryParentResult.newNumericalResidual ∧
    ‖trueBoundaryParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  TrueFlowGeometryRuntime.geometryParent_error_and_memory

abbrev TrueBoundaryBase := TrueFlowGeometryRuntime.geometryLivingRoot.toAuthoritativeRoot.source
abbrev TrueBoundaryLedger := TrueBoundaryBase.restructuringSource.toLedgerSource

theorem trueBoundaryParent_same_actual_visit :
    trueBoundaryParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.TrueFlowBoundaryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
