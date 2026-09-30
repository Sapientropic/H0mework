import H0mework.Chemistry.LAlanineTrueFlowDifferential.RuntimeConsumers

/-! The original occurrence installs its generated true-flow geometry. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometryRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def geometryParentRuntime := TrueFlowDifferentialRuntime.differentialRuntimeAfterFirst
def geometryParentMaterial : TrueFlowDifferentialRuntime.DifferentialMaterial :=
  match TrueFlowDifferentialRuntime.differentialRuntimeFacade.readoutAt geometryParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def geometryParentResult := geometryParentMaterial.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.physical
def geometryParentHistory := geometryParentMaterial.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.history

theorem geometryParent_installed :
    type_of% (TrueFlowDifferentialRuntime.differentialRuntimeFace_factorizes geometryParentRuntime (.component .material)) ∧
    type_of% (TrueFlowDifferentialRuntime.differentialRuntimeFace_factorizes geometryParentRuntime (.component .certificate)) :=
  ⟨TrueFlowDifferentialRuntime.differentialRuntimeFace_factorizes geometryParentRuntime (.component .material),
    TrueFlowDifferentialRuntime.differentialRuntimeFace_factorizes geometryParentRuntime (.component .certificate)⟩

theorem geometryParent_actual :
    geometryParentMaterial = TrueFlowDifferentialRuntime.generatedDifferentialMaterial ∧
    geometryParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    geometryParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    geometryParentResult.realized = Reentry.Source.targetRealized ∧
    geometryParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem geometryParent_clock : geometryParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  TrueFlowDifferentialRuntime.differentialParent_clock

theorem geometryParent_error_and_memory :
    geometryParentResult.realized = geometryParentResult.held + geometryParentResult.inheritedResidual +
      geometryParentResult.newNumericalResidual ∧
    ‖geometryParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  TrueFlowDifferentialRuntime.differentialParent_error_and_memory

abbrev GeometryBase := TrueFlowDifferentialRuntime.differentialLivingRoot.toAuthoritativeRoot.source
abbrev GeometryLedger := GeometryBase.restructuringSource.toLedgerSource

theorem geometryParent_same_actual_visit :
    geometryParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
