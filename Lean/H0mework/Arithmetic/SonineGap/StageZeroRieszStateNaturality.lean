import H0mework.Realization.Graph.RieszRealization
import H0mework.Arithmetic.SonineGap.StageZeroResidualPrism

/-!
# Stage-zero Riesz-state naturality in the actual graph target

The normalized relation-graph self-morphism fixes the realized canonical
Riesz state pairing.  The state's detector coordinate is the square of the
quotient Riesz norm and is therefore nonzero.  These are direct A1c consumers
of the source-neutral Riesz-realization kernel.
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

open SourceGeneratedFunctionalGraphCokernel
open SourceGeneratedFunctionalGraphPerfectification

noncomputable section

theorem selectedRieszGraphTargetState_stageZero_normalized_stationary
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    inner ℂ (selectedRieszGraphTargetState observation nontrivial)
        (graphTargetMap
          (normalizedQuarterDilationGraphMorphism
            (selectedCoPoissonMuntzParameter observation)
            stageZeroSqrtScale stageZeroSqrtScale_pos)
          (selectedRieszGraphTargetState observation nontrivial)) =
      inner ℂ (selectedRieszGraphTargetState observation nontrivial)
        (selectedRieszGraphTargetState observation nontrivial) := by
  have stationary := realizedRieszState_graphMorphism_stationary
      (quarterMellinL2Feature
        (selectedCoPoissonMuntzParameter observation))
      (quarterMellinL2Functional
        (selectedCoPoissonMuntzParameter observation))
      (coPoissonQuarterMellinConvergentMap
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))
      (selectedZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
        observation nontrivial)
      (normalizedQuarterDilationRelationMorphism
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        stageZeroSqrtScale stageZeroSqrtScale_pos)
  rw [show
    (normalizedQuarterDilationRelationMorphism
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      stageZeroSqrtScale stageZeroSqrtScale_pos).graphMorphism =
        normalizedQuarterDilationGraphMorphism
          (selectedCoPoissonMuntzParameter observation)
          stageZeroSqrtScale stageZeroSqrtScale_pos from rfl] at stationary
  simpa [selectedRieszGraphTargetState,
    selectedRelationGraphMap,
    selectedRieszGraphHilbertState,
    selectedRieszOrthogonalRepresentative,
    selectedCoPoissonMuntzRieszVector] using stationary

theorem reversalRieszGraphTargetState_stageZero_normalized_stationary
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    inner ℂ (reversalRieszGraphTargetState observation nontrivial)
        (graphTargetMap
          (normalizedQuarterDilationGraphMorphism
            (reversalCoPoissonMuntzParameter observation)
            stageZeroSqrtScale stageZeroSqrtScale_pos)
          (reversalRieszGraphTargetState observation nontrivial)) =
      inner ℂ (reversalRieszGraphTargetState observation nontrivial)
        (reversalRieszGraphTargetState observation nontrivial) := by
  have stationary := realizedRieszState_graphMorphism_stationary
      (quarterMellinL2Feature
        (reversalCoPoissonMuntzParameter observation))
      (quarterMellinL2Functional
        (reversalCoPoissonMuntzParameter observation))
      (coPoissonQuarterMellinConvergentMap
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial))
      (reversalZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
        observation nontrivial)
      (normalizedQuarterDilationRelationMorphism
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        stageZeroSqrtScale stageZeroSqrtScale_pos)
  rw [show
    (normalizedQuarterDilationRelationMorphism
      (reversalCoPoissonMuntzParameter observation)
      (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
      (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      stageZeroSqrtScale stageZeroSqrtScale_pos).graphMorphism =
        normalizedQuarterDilationGraphMorphism
          (reversalCoPoissonMuntzParameter observation)
          stageZeroSqrtScale stageZeroSqrtScale_pos from rfl] at stationary
  simpa [reversalRieszGraphTargetState,
    reversalRelationGraphMap,
    reversalRieszGraphHilbertState,
    reversalRieszOrthogonalRepresentative,
    reversalCoPoissonMuntzRieszVector] using stationary

theorem selectedRieszGraphTargetState_snd_eq_norm_sq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (selectedRieszGraphTargetState observation nontrivial).snd =
      ((‖selectedCoPoissonMuntzRieszVector observation nontrivial‖ : ℂ) ^ 2) := by
  simpa [selectedRieszGraphTargetState, selectedRelationGraphMap,
    selectedRieszGraphHilbertState, selectedRieszOrthogonalRepresentative,
    selectedCoPoissonMuntzRieszVector] using
    (realizedRieszState_snd_eq_norm_sq
      (quarterMellinL2Feature
        (selectedCoPoissonMuntzParameter observation))
      (quarterMellinL2Functional
        (selectedCoPoissonMuntzParameter observation))
      (coPoissonQuarterMellinConvergentMap
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))
      (selectedZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
        observation nontrivial))

theorem reversalRieszGraphTargetState_snd_eq_norm_sq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (reversalRieszGraphTargetState observation nontrivial).snd =
      ((‖reversalCoPoissonMuntzRieszVector observation nontrivial‖ : ℂ) ^ 2) := by
  simpa [reversalRieszGraphTargetState, reversalRelationGraphMap,
    reversalRieszGraphHilbertState, reversalRieszOrthogonalRepresentative,
    reversalCoPoissonMuntzRieszVector] using
    (realizedRieszState_snd_eq_norm_sq
      (quarterMellinL2Feature
        (reversalCoPoissonMuntzParameter observation))
      (quarterMellinL2Functional
        (reversalCoPoissonMuntzParameter observation))
      (coPoissonQuarterMellinConvergentMap
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial))
      (reversalZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
        observation nontrivial))

theorem selectedStageZeroJointState_snd_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (selectedStageZeroJointState observation nontrivial).snd ≠ 0 := by
  rw [show selectedStageZeroJointState observation nontrivial =
      selectedRieszGraphTargetState observation nontrivial by
    exact zeroOwnedJointStateModuleOccurrence_root_selectedState
      observation nontrivial]
  rw [selectedRieszGraphTargetState_snd_eq_norm_sq]
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr
      (selectedCoPoissonMuntzRieszVector_ne_zero observation nontrivial)))

theorem reversalStageZeroJointState_snd_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (reversalStageZeroJointState observation nontrivial).snd ≠ 0 := by
  rw [show reversalStageZeroJointState observation nontrivial =
      reversalRieszGraphTargetState observation nontrivial by
    exact zeroOwnedJointStateModuleOccurrence_root_reversalState
      observation nontrivial]
  rw [reversalRieszGraphTargetState_snd_eq_norm_sq]
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr
      (reversalCoPoissonMuntzRieszVector_ne_zero observation nontrivial)))

end


end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
