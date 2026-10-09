import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.ConservationRuntimeConsumers

/-! Original Root58 occurrence and complete inherited material. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.AtomicMass.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def atomicMassParentRuntime := BasinRefinement.BandConservationRuntime.bandConservationRuntimeAfterFirst
def atomicMassParentMaterial : BasinRefinement.BandConservationRuntime.BandConservationMaterial :=
  match BasinRefinement.BandConservationRuntime.bandConservationRuntimeFacade.readoutAt atomicMassParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def atomicMassParentResult := BasinRefinement.BandConservationRuntime.bandConservationParentResult
def atomicMassParentHistory := BasinRefinement.BandConservationRuntime.bandConservationParentHistory

theorem atomicMassParent_installed :
    type_of% (BasinRefinement.BandConservationRuntime.bandConservationRuntimeFace_factorizes atomicMassParentRuntime (.component .material)) ∧
    type_of% (BasinRefinement.BandConservationRuntime.bandConservationRuntimeFace_factorizes atomicMassParentRuntime (.component .certificate)) :=
  ⟨BasinRefinement.BandConservationRuntime.bandConservationRuntimeFace_factorizes atomicMassParentRuntime (.component .material),
    BasinRefinement.BandConservationRuntime.bandConservationRuntimeFace_factorizes atomicMassParentRuntime (.component .certificate)⟩

theorem atomicMassParent_actual :
    atomicMassParentMaterial = BasinRefinement.BandConservationRuntime.generatedBandConservationMaterial ∧
    atomicMassParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    atomicMassParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    atomicMassParentResult.realized = Reentry.Source.targetRealized ∧
    atomicMassParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem atomicMassParent_clock : atomicMassParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  BasinRefinement.BandConservationRuntime.bandConservationParent_clock

theorem atomicMassParent_error_and_memory :
    atomicMassParentResult.realized = atomicMassParentResult.held + atomicMassParentResult.inheritedResidual +
      atomicMassParentResult.newNumericalResidual ∧
    ‖atomicMassParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  BasinRefinement.BandConservationRuntime.bandConservationParent_error_and_memory

abbrev AtomicMassBase := BasinRefinement.BandConservationRuntime.bandConservationLivingRoot.toAuthoritativeRoot.source
abbrev AtomicMassLedger := AtomicMassBase.restructuringSource.toLedgerSource

theorem atomicMassParent_same_actual_visit :
    atomicMassParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.AtomicMass.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
