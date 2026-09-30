import H0mework.Chemistry.LAlanineWholeBandCell1.RuntimeConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentSpatialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def adjacentSpatialParentRuntime := WholeBandCell1Runtime.wholeBandCell1RuntimeAfterFirst
def adjacentSpatialParentMaterial : WholeBandCell1Runtime.WholeBandCell1Material :=
  match WholeBandCell1Runtime.wholeBandCell1RuntimeFacade.readoutAt adjacentSpatialParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def adjacentSpatialParentResult := WholeBandCell1Runtime.wholeBandCell1ParentResult
def adjacentSpatialParentHistory := WholeBandCell1Runtime.wholeBandCell1ParentHistory

theorem adjacentSpatialParent_installed :
    type_of% (WholeBandCell1Runtime.wholeBandCell1RuntimeFace_factorizes adjacentSpatialParentRuntime (.component .material)) ∧
    type_of% (WholeBandCell1Runtime.wholeBandCell1RuntimeFace_factorizes adjacentSpatialParentRuntime (.component .certificate)) :=
  ⟨WholeBandCell1Runtime.wholeBandCell1RuntimeFace_factorizes adjacentSpatialParentRuntime (.component .material),
    WholeBandCell1Runtime.wholeBandCell1RuntimeFace_factorizes adjacentSpatialParentRuntime (.component .certificate)⟩

theorem adjacentSpatialParent_actual :
    adjacentSpatialParentMaterial = WholeBandCell1Runtime.generatedWholeBandCell1Material ∧
    adjacentSpatialParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    adjacentSpatialParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    adjacentSpatialParentResult.realized = Reentry.Source.targetRealized ∧
    adjacentSpatialParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem adjacentSpatialParent_clock : adjacentSpatialParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  WholeBandCell1Runtime.wholeBandCell1Parent_clock

theorem adjacentSpatialParent_error_and_memory :
    adjacentSpatialParentResult.realized = adjacentSpatialParentResult.held + adjacentSpatialParentResult.inheritedResidual +
      adjacentSpatialParentResult.newNumericalResidual ∧
    ‖adjacentSpatialParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  WholeBandCell1Runtime.wholeBandCell1Parent_error_and_memory

abbrev AdjacentSpatialBase := WholeBandCell1Runtime.wholeBandCell1LivingRoot.toAuthoritativeRoot.source
abbrev AdjacentSpatialLedger := AdjacentSpatialBase.restructuringSource.toLedgerSource

theorem adjacentSpatialParent_same_actual_visit :
    adjacentSpatialParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.AdjacentSpatialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
