import H0mework.Realization.Graph.Realization
import H0mework.Versions.V2.Arithmetic.RiemannGraph.ZeroRieszGraphOrthogonalState

/-!
# Same-zero Riesz state in the common actual graph target

The generic completed-range realization sends both canonical orthogonal
Riesz representatives into the same owner-free `Energy × ℂ` carrier.
The realization is isometric, preserves nonzero states, and keeps the exact
source functional readback.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram

open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedHilbertCokernel
open scoped InnerProductSpace

noncomputable section

def selectedRieszGraphTargetState
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    GraphTarget PositiveMellinQuarterEnergy :=
  graphHilbertAmbientRealization
      (quarterMellinL2Feature (selectedCoPoissonMuntzParameter observation))
      (quarterMellinL2Functional (selectedCoPoissonMuntzParameter observation))
    (selectedRieszGraphHilbertState observation nontrivial)

def reversalRieszGraphTargetState
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    GraphTarget PositiveMellinQuarterEnergy :=
  graphHilbertAmbientRealization
      (quarterMellinL2Feature (reversalCoPoissonMuntzParameter observation))
      (quarterMellinL2Functional (reversalCoPoissonMuntzParameter observation))
    (reversalRieszGraphHilbertState observation nontrivial)

theorem selectedRieszGraphTargetState_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedRieszGraphTargetState observation nontrivial ≠ 0 := by
  intro targetZero
  apply selectedRieszGraphHilbertState_ne_zero observation nontrivial
  apply (graphHilbertAmbientRealization
    (quarterMellinL2Feature (selectedCoPoissonMuntzParameter observation))
    (quarterMellinL2Functional
      (selectedCoPoissonMuntzParameter observation))).injective
  simpa [selectedRieszGraphTargetState] using targetZero

theorem reversalRieszGraphTargetState_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalRieszGraphTargetState observation nontrivial ≠ 0 := by
  intro targetZero
  apply reversalRieszGraphHilbertState_ne_zero observation nontrivial
  apply (graphHilbertAmbientRealization
    (quarterMellinL2Feature (reversalCoPoissonMuntzParameter observation))
    (quarterMellinL2Functional
      (reversalCoPoissonMuntzParameter observation))).injective
  simpa [reversalRieszGraphTargetState] using targetZero

theorem selectedRieszGraphTargetState_source_readback
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (value : QuarterMellinL2Test
      (selectedCoPoissonMuntzParameter observation)) :
    inner ℂ (selectedRieszGraphTargetState observation nontrivial)
        (graphHilbertAmbientRealization
          (quarterMellinL2Feature
            (selectedCoPoissonMuntzParameter observation))
          (quarterMellinL2Functional
            (selectedCoPoissonMuntzParameter observation))
          (quotientOrthogonalEquiv
            (selectedRelationGraphMap observation nontrivial)
            (coPoissonMuntzGraphSourceMap
              (selectedCoPoissonMuntzParameter observation)
              (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
              (selectedCoPoissonMuntzParameter_re_lt_half
                observation nontrivial)
              value))) =
      quarterMellinL2Functional
        (selectedCoPoissonMuntzParameter observation) value := by
  rw [selectedRieszGraphTargetState, LinearIsometry.inner_map_map]
  exact selectedRieszOrthogonalRepresentative_source_readback
    observation nontrivial value

theorem reversalRieszGraphTargetState_source_readback
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (value : QuarterMellinL2Test
      (reversalCoPoissonMuntzParameter observation)) :
    inner ℂ (reversalRieszGraphTargetState observation nontrivial)
        (graphHilbertAmbientRealization
          (quarterMellinL2Feature
            (reversalCoPoissonMuntzParameter observation))
          (quarterMellinL2Functional
            (reversalCoPoissonMuntzParameter observation))
          (quotientOrthogonalEquiv
            (reversalRelationGraphMap observation nontrivial)
            (coPoissonMuntzGraphSourceMap
              (reversalCoPoissonMuntzParameter observation)
              (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
              (reversalCoPoissonMuntzParameter_re_lt_half
                observation nontrivial)
              value))) =
      quarterMellinL2Functional
        (reversalCoPoissonMuntzParameter observation) value := by
  rw [reversalRieszGraphTargetState, LinearIsometry.inner_map_map]
  exact reversalRieszOrthogonalRepresentative_source_readback
    observation nontrivial value

end


end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
