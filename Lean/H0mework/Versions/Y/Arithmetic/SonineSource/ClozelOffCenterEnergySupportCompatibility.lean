import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaQuarterScaleRuntimeReadback
import H0mework.Versions.Y.Arithmetic.SonineSource.StageZeroSonineEnergyCompression
import H0mework.Versions.Y.Arithmetic.SonineSource.ClozelOffCenterVerticalGraphClosure

/-!
# Compatibility of the current law surface with zero energy support

The off-center expanding sibling simultaneously has a nonzero vertical full
graph point, zero common-Sonine energy, no literal integral/perfect lift, a
nonzero algebraic range class, and actual topological admission with zero
external defect.  Prime visibility and the common compressed J--adjoint law
remain true.  Hence none of the currently installed laws excludes the
measurement-only branch.
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

open Character.GlobalCoPoissonCurrent
open SourceGeneratedCompressedUnitaryDefectPort
open SourceGeneratedFaithfulIntegralFace
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralOrbitClosedDefectPort
open ThetaJRoleRepresentation

noncomputable section

local instance offCenterBalancedFaceComplete :
    CompleteSpace StageZeroBalancedQuarterEnergyOrthogonalCarrier := by
  apply IsComplete.completeSpace_coe
  exact stageZeroBalancedQuarterEnergyOrthogonalFace.isClosed.isComplete

/-- The exact sibling-specific obstruction generated off center. -/
inductive OffCenterEnergySupportObstruction
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : Prop where
  | selected
      (left : observation.coordinate.re < 1 / 2)
      (vertical : NonzeroVerticalGraphClosure
        (quarterMellinL2Feature
          (selectedCoPoissonMuntzParameter observation))
        (quarterMellinL2Functional
          (selectedCoPoissonMuntzParameter observation)))
      (compression_zero : stageZeroSonineEnergyCompression
        (selectedStageZeroBalancedEnergyState observation nontrivial) = 0)
      (integral_lift_empty :
        IsEmpty (SelectedIntegralOrbitPointLift observation nontrivial))
      (perfect_lift_empty :
        IsEmpty (SelectedPerfectCarrierPointLift observation nontrivial))
      (algebraic_range_class_ne_zero :
        (Submodule.Quotient.mk
          (selectedStageZeroJointState observation nontrivial) :
          JointGraphTarget ⧸ LinearMap.range
            (selectedIntegralGraphOrbit observation nontrivial)) ≠ 0)
      (topological_admission :
        selectedStageZeroJointState observation nontrivial ∈
          selectedStageZeroOrbitClosedRange observation nontrivial)
      (external_defect_zero :
        externalDefect
            (selectedStageZeroOrbitClosedRange observation nontrivial)
            stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
            (selectedStageZeroOrbitIdentitySeed observation nontrivial) = 0)
  | reversal
      (right : 1 / 2 < observation.coordinate.re)
      (vertical : NonzeroVerticalGraphClosure
        (quarterMellinL2Feature
          (reversalCoPoissonMuntzParameter observation))
        (quarterMellinL2Functional
          (reversalCoPoissonMuntzParameter observation)))
      (compression_zero : stageZeroSonineEnergyCompression
        (reversalStageZeroBalancedEnergyState observation nontrivial) = 0)
      (integral_lift_empty :
        IsEmpty (ReversalIntegralOrbitPointLift observation nontrivial))
      (perfect_lift_empty :
        IsEmpty (ReversalPerfectCarrierPointLift observation nontrivial))
      (algebraic_range_class_ne_zero :
        (Submodule.Quotient.mk
          (reversalStageZeroJointState observation nontrivial) :
          JointGraphTarget ⧸ LinearMap.range
            (reversalIntegralGraphOrbit observation nontrivial)) ≠ 0)
      (topological_admission :
        reversalStageZeroJointState observation nontrivial ∈
          reversalStageZeroOrbitClosedRange observation nontrivial)
      (external_defect_zero :
        externalDefect
            (reversalStageZeroOrbitClosedRange observation nontrivial)
            stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
            (reversalStageZeroOrbitIdentitySeed observation nontrivial) = 0)

/-- Every off-center zero generates the exact compatibility obstruction; no
branch or representation witness is accepted from the caller. -/
theorem offCenterEnergySupportObstruction
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (offCenter : observation.coordinate.re ≠ 1 / 2) :
    OffCenterEnergySupportObstruction observation nontrivial := by
  rcases lt_or_gt_of_ne offCenter with left | right
  · exact .selected left
      (selected_nonzeroVerticalGraphClosure_of_re_lt_half
        observation nontrivial left)
      (by
        have stateZero :
            selectedStageZeroBalancedEnergyState observation nontrivial = 0 := by
          apply Subtype.ext
          exact selectedRieszEnergy_eq_zero_of_re_lt_half
            observation nontrivial left
        rw [stateZero, map_zero])
      (selectedIntegralOrbitPointLift_isEmpty_of_re_lt_half
        observation nontrivial left)
      (selectedPerfectCarrierPointLift_isEmpty_of_re_lt_half
        observation nontrivial left)
      (selectedIntegralRangeClass_ne_zero_of_re_lt_half
        observation nontrivial left)
      (selectedExpandingRieszState_mem_complexifiedOrbitClosure
        observation nontrivial left)
      (selectedExpandingActualOrbit_externalDefect_zero
        observation nontrivial left)
  · exact .reversal right
      (reversal_nonzeroVerticalGraphClosure_of_half_lt_re
        observation nontrivial right)
      (by
        have stateZero :
            reversalStageZeroBalancedEnergyState observation nontrivial = 0 := by
          apply Subtype.ext
          exact reversalRieszEnergy_eq_zero_of_half_lt_re
            observation nontrivial right
        rw [stateZero, map_zero])
      (reversalIntegralOrbitPointLift_isEmpty_of_half_lt_re
        observation nontrivial right)
      (reversalPerfectCarrierPointLift_isEmpty_of_half_lt_re
        observation nontrivial right)
      (reversalIntegralRangeClass_ne_zero_of_half_lt_re
        observation nontrivial right)
      (reversalExpandingRieszState_mem_complexifiedOrbitClosure
        observation nontrivial right)
      (reversalExpandingActualOrbit_externalDefect_zero
        observation nontrivial right)

/-- Prime-visible integral boundary, J-character conservation and the
operator-level compressed J law all coexist with the obstruction above. -/
theorem offCenter_existing_energySupport_laws_cohabit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (offCenter : observation.coordinate.re ≠ 1 / 2) :
    (∀ prime : Nat.Primes,
        residualClass (L := IntegralScaleCarrier) prime
          stageZeroQuarterIntegralBoundary ≠ 0) ∧
      selectedStageZeroRawRieszTarget observation nontrivial *
        star (reversalStageZeroRawRieszTarget observation nontrivial) = 1 ∧
      (∀ value : StageZeroBalancedQuarterEnergyOrthogonalCarrier,
        balancedFaceEquiv stageZeroBalancedQuarterEnergyOrthogonalFace
            positiveMellinQuarterEnergyReflectionIsometry
            stageZeroBalancedQuarterEnergyOrthogonal_isBalanced
            (stageZeroSonineEnergyCompression value) =
          ContinuousLinearMap.adjoint stageZeroSonineEnergyCompression
            (balancedFaceEquiv stageZeroBalancedQuarterEnergyOrthogonalFace
              positiveMellinQuarterEnergyReflectionIsometry
              stageZeroBalancedQuarterEnergyOrthogonal_isBalanced value)) ∧
      OffCenterEnergySupportObstruction observation nontrivial := by
  exact ⟨stageZeroQuarterIntegralBoundary_residualClass_ne_zero,
    stageZeroRawRieszTargets_paired_stationarity observation nontrivial,
    stageZeroSonineEnergyCompression_J_adjoint,
    offCenterEnergySupportObstruction observation nontrivial offCenter⟩

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
