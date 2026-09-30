import H0mework.Versions.Y.Arithmetic.RiemannGraph.NoGo.ClozelMeasurementOnlyIntegralLiftNoGo
import H0mework.Versions.Y.Arithmetic.SonineSource.ZeroBalancedSonineEnergyState

/-!
# Off-center vertical point in the actual graph closure

The graph completion is the closure of the full source graph, not the whole
ambient product.  Nevertheless the expanding side of every off-center zero
already supplies a nonzero vertical point in that exact closure: the
zero-owned Riesz state itself.  Thus a future support proof cannot obtain
vertical exclusion from the existing full graph completion.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

open SourceGeneratedFunctionalGraphPerfectification
open Set

noncomputable section

universe c h

/-- A nonzero measurement-only point in the closure of one actual source
graph. -/
def NonzeroVerticalGraphClosure
    {C : Type c} [AddCommGroup C] [Module ℂ C]
    {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) : Prop :=
  ∃ point : GraphTarget H,
    point ∈ closure (LinearMap.range (graphFeature feature functional) :
      Set (GraphTarget H)) ∧
    point.fst = 0 ∧ point.snd ≠ 0

theorem selected_nonzeroVerticalGraphClosure_of_re_lt_half
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left : observation.coordinate.re < 1 / 2) :
    NonzeroVerticalGraphClosure
      (quarterMellinL2Feature
        (selectedCoPoissonMuntzParameter observation))
      (quarterMellinL2Functional
        (selectedCoPoissonMuntzParameter observation)) := by
  refine ⟨selectedRieszGraphTargetState observation nontrivial, ?_, ?_, ?_⟩
  · exact graphHilbertAmbientRealization_mem_graphClosure
      (quarterMellinL2Feature
        (selectedCoPoissonMuntzParameter observation))
      (quarterMellinL2Functional
        (selectedCoPoissonMuntzParameter observation))
      (selectedRieszGraphHilbertState observation nontrivial)
  · rw [← zeroOwnedJointStateModuleOccurrence_root_selectedState
      observation nontrivial]
    exact selectedRieszEnergy_eq_zero_of_re_lt_half
      observation nontrivial left
  · rw [← zeroOwnedJointStateModuleOccurrence_root_selectedState
      observation nontrivial]
    exact selectedStageZeroJointState_snd_ne_zero observation nontrivial

theorem reversal_nonzeroVerticalGraphClosure_of_half_lt_re
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (right : 1 / 2 < observation.coordinate.re) :
    NonzeroVerticalGraphClosure
      (quarterMellinL2Feature
        (reversalCoPoissonMuntzParameter observation))
      (quarterMellinL2Functional
        (reversalCoPoissonMuntzParameter observation)) := by
  refine ⟨reversalRieszGraphTargetState observation nontrivial, ?_, ?_, ?_⟩
  · exact graphHilbertAmbientRealization_mem_graphClosure
      (quarterMellinL2Feature
        (reversalCoPoissonMuntzParameter observation))
      (quarterMellinL2Functional
        (reversalCoPoissonMuntzParameter observation))
      (reversalRieszGraphHilbertState observation nontrivial)
  · rw [← zeroOwnedJointStateModuleOccurrence_root_reversalState
      observation nontrivial]
    exact reversalRieszEnergy_eq_zero_of_half_lt_re
      observation nontrivial right
  · rw [← zeroOwnedJointStateModuleOccurrence_root_reversalState
      observation nontrivial]
    exact reversalStageZeroJointState_snd_ne_zero observation nontrivial

end

end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
