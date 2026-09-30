import H0mework.Chemistry.LAlanineBoundary.RuntimeConsumers

/-! The same physical occurrence installs its actual true-ODE continuation face. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def tubeParentRuntime := BoundaryRuntime.boundaryRuntimeAfterFirst
def tubeParentMaterial : BoundaryRuntime.BoundaryMaterial :=
  match BoundaryRuntime.boundaryRuntimeFacade.readoutAt tubeParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def tubeParentResult := tubeParentMaterial.parent.parent.parent.parent.parent.parent.parent.physical
def tubeParentHistory := tubeParentMaterial.parent.parent.parent.parent.parent.parent.parent.history

theorem tubeParent_installed :
    type_of% (BoundaryRuntime.boundaryRuntimeFace_factorizes tubeParentRuntime (.component .material)) ∧
    type_of% (BoundaryRuntime.boundaryRuntimeFace_factorizes tubeParentRuntime (.component .certificate)) :=
  ⟨BoundaryRuntime.boundaryRuntimeFace_factorizes tubeParentRuntime (.component .material),
    BoundaryRuntime.boundaryRuntimeFace_factorizes tubeParentRuntime (.component .certificate)⟩

theorem tubeParent_actual :
    tubeParentMaterial = BoundaryRuntime.generatedBoundaryMaterial ∧
    tubeParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    tubeParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    tubeParentResult.realized = Reentry.Source.targetRealized ∧
    tubeParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tubeParent_clock : tubeParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  BoundaryRuntime.boundaryParent_clock

theorem tubeParent_error_and_memory :
    tubeParentResult.realized = tubeParentResult.held + tubeParentResult.inheritedResidual +
      tubeParentResult.newNumericalResidual ∧
    ‖tubeParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  BoundaryRuntime.boundaryParent_error_and_memory

abbrev TubeBase := BoundaryRuntime.boundaryLivingRoot.toAuthoritativeRoot.source
abbrev TubeLedger := TubeBase.restructuringSource.toLedgerSource

theorem tubeParent_same_actual_visit :
    tubeParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.TrueTubeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
