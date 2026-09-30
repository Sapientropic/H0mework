import H0mework.Chemistry.LAlanineWholeBandAdjacent.RuntimeConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.BandConservationRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def bandConservationParentRuntime := AdjacentSpatialRuntime.adjacentSpatialRuntimeAfterFirst
def bandConservationParentMaterial : AdjacentSpatialRuntime.AdjacentSpatialMaterial :=
  match AdjacentSpatialRuntime.adjacentSpatialRuntimeFacade.readoutAt bandConservationParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def bandConservationParentResult := AdjacentSpatialRuntime.adjacentSpatialParentResult
def bandConservationParentHistory := AdjacentSpatialRuntime.adjacentSpatialParentHistory

theorem bandConservationParent_installed :
    type_of% (AdjacentSpatialRuntime.adjacentSpatialRuntimeFace_factorizes bandConservationParentRuntime (.component .material)) ∧
    type_of% (AdjacentSpatialRuntime.adjacentSpatialRuntimeFace_factorizes bandConservationParentRuntime (.component .certificate)) :=
  ⟨AdjacentSpatialRuntime.adjacentSpatialRuntimeFace_factorizes bandConservationParentRuntime (.component .material),
    AdjacentSpatialRuntime.adjacentSpatialRuntimeFace_factorizes bandConservationParentRuntime (.component .certificate)⟩

theorem bandConservationParent_actual :
    bandConservationParentMaterial = AdjacentSpatialRuntime.generatedAdjacentSpatialMaterial ∧
    bandConservationParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    bandConservationParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    bandConservationParentResult.realized = Reentry.Source.targetRealized ∧
    bandConservationParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem bandConservationParent_clock : bandConservationParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  AdjacentSpatialRuntime.adjacentSpatialParent_clock

theorem bandConservationParent_error_and_memory :
    bandConservationParentResult.realized = bandConservationParentResult.held + bandConservationParentResult.inheritedResidual +
      bandConservationParentResult.newNumericalResidual ∧
    ‖bandConservationParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  AdjacentSpatialRuntime.adjacentSpatialParent_error_and_memory

abbrev BandConservationBase := AdjacentSpatialRuntime.adjacentSpatialLivingRoot.toAuthoritativeRoot.source
abbrev BandConservationLedger := BandConservationBase.restructuringSource.toLedgerSource

theorem bandConservationParent_same_actual_visit :
    bandConservationParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.BandConservationRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
