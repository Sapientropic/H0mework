import H0mework.Versions.Y1.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.LivingLawCanonicalRiemannPrimeExponentPoleReceiptRelationRoot
import H0mework.Versions.Y.Arithmetic.SonineSource.PairedOmegaJointRelationDisposition

/-!
# Same-root consumer for the receipt relation and faithful effect history

The old faithful joint-effect history is inherited through the complete
coface chain into the receipt-relation root.  Its balance relation and the
new certified-row split are therefore consumed with one source emitter,
whole-ledger write-back, and generated next.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace Runtime
namespace MuntzGraph
namespace Conductor
namespace History
namespace PrimePowerCurrent
namespace ReceiptRelation

open CanonicalUnitArithmeticRoot
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open CofinalFaithfulSettlementFace
open RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure
open Arithmetic.Character.CommonAction.Boundary

noncomputable section

def requestedPrimePowerReceiptRelationRequest
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    PrimeExponentPoleReceiptRelationRequestAt observation nontrivial
      ((runtimePrimeExponentPoleReceiptRelationRoot observation nontrivial
        ).emitted
          (CanonicalUnitArithmeticRoot.finiteVisit
            (PrimePower.Runtime.primePowerRuntimeStage prime exponent)
            ).current) where
  cursor := scheduleIndex prime exponent
  current_eq := by
    simp only [scheduledPrime_scheduleIndex,
      scheduledExponent_scheduleIndex prime exponent positive]
    rfl

def requestedPrimePowerReceiptRelationInstalled
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :=
  generatePrimeExponentPoleReceiptRelationInstalledAt
    observation nontrivial
    ((runtimePrimeExponentPoleReceiptRelationRoot observation nontrivial
      ).emitted
        (CanonicalUnitArithmeticRoot.finiteVisit
          (PrimePower.Runtime.primePowerRuntimeStage prime exponent)).current)
    (requestedPrimePowerReceiptRelationRequest
      observation nontrivial prime exponent positive)

theorem requestedPrimePowerReceiptRelationInstalled_eq_projection
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (runtimePrimeExponentPoleReceiptRelationProjectionLaw
      observation nontrivial).project PUnit.unit
        ((runtimePrimeExponentPoleReceiptRelationRoot observation nontrivial
          ).emitted
            (CanonicalUnitArithmeticRoot.finiteVisit
              (PrimePower.Runtime.primePowerRuntimeStage prime exponent)
              ).current)
        PUnit.unit
        (requestedPrimePowerReceiptRelationRequest
          observation nontrivial prime exponent positive) =
      requestedPrimePowerReceiptRelationInstalled
        observation nontrivial prime exponent positive :=
  rfl

/-- The existing faithful joint relation reaches the previous effect root
without changing its material law. -/
def runtimeJointFaithfulInstallationAtPrimeExponentPoleRootEffectRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeJointFaithfulMaterialLaw observation nontrivial).toProjectionLaw
      (runtimePrimeExponentPoleRootEffectAuthoritySource
        observation nontrivial).projectionLaw :=
  ((((runtimeJointFaithfulInstallationAtConductorHistoryRoot
      observation nontrivial).trans
        (runtimeConductorPrimePowerInheritedInstallation
          observation nontrivial)).trans
      (runtimePrimeExponentPoleCouplingInheritedInstallation
        observation nontrivial)).trans
    (runtimePrimeExponentPoleEnergyCoimageInheritedInstallation
      observation nontrivial)).trans
  (runtimePrimeExponentPoleRootEffectInheritedInstallation
    observation nontrivial)

def runtimeJointFaithfulInstallationAtReceiptRelationRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeJointFaithfulMaterialLaw observation nontrivial).toProjectionLaw
      (runtimePrimeExponentPoleReceiptRelationAuthoritySource
        observation nontrivial).projectionLaw :=
  (runtimeJointFaithfulInstallationAtPrimeExponentPoleRootEffectRoot
    observation nontrivial).trans
      (runtimePrimeExponentPoleReceiptRelationInheritedInstallation
        observation nontrivial)

def runtimeJointFaithfulRecognitionAtReceiptRelationRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeCofinalFaithfulRecognitionAt PairedOmegaJointRelationCarrier
      (runtimePrimeExponentPoleReceiptRelationRoot observation nontrivial) :=
  SourceNativeCofinalFaithfulRecognitionAt.create
    (runtimeJointFaithfulMaterialLaw observation nontrivial)
    (runtimeJointFaithfulInstallationAtReceiptRelationRoot
      observation nontrivial)

def runtimeJointFaithfulStepAtReceiptRelationRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    RootGeneratedCofinalFaithfulSettlementStepAt
      (runtimeJointFaithfulRecognitionAtReceiptRelationRoot
        observation nontrivial)
      (runtimePrimeExponentPoleReceiptRelationVisitAt
        observation nontrivial depth) :=
  (runtimeJointFaithfulRecognitionAtReceiptRelationRoot
    observation nontrivial).generateStepAt
      (runtimePrimeExponentPoleReceiptRelationVisitAt
        observation nontrivial depth)

theorem runtimeJointFaithfulStepAtReceiptRelationRoot_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let step := runtimeJointFaithfulStepAtReceiptRelationRoot
      observation nontrivial depth
    HEq step.wholeLedgerWriteBack
        ((runtimePrimeExponentPoleReceiptRelationRoot observation nontrivial
          ).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
            (runtimePrimeExponentPoleReceiptRelationVisitAt
              observation nontrivial depth).current) ∧
      step.nextCurrent =
        (runtimePrimeExponentPoleReceiptRelationRoot observation nontrivial
          ).generatedNextCurrentAt
            (runtimePrimeExponentPoleReceiptRelationVisitAt
              observation nontrivial depth) ∧
      HEq
        ((runtimePrimeExponentPoleReceiptRelationRoot observation nontrivial
          ).toAuthoritativeRoot.source.projectionLaw.outcomeAt
            ((runtimeJointFaithfulInstallationAtReceiptRelationRoot
              observation nontrivial).embed PUnit.unit)
            step.sourceOccurrence)
        ((runtimeJointFaithfulMaterialLaw observation nontrivial
          ).toProjectionLaw.outcomeAt PUnit.unit step.sourceOccurrence) := by
  dsimp only
  exact ⟨
    RootGeneratedCofinalFaithfulSettlementStepAt.wholeLedgerWriteBack_eq_root _,
    RootGeneratedCofinalFaithfulSettlementStepAt.nextCurrent_eq_root _,
    (runtimeJointFaithfulStepAtReceiptRelationRoot
      observation nontrivial depth).installedFaithful_factorizes⟩

/-- The inherited balance relation is a literal trace event of the current
receipt-relation root step, not a theorem read from a sibling root. -/
theorem runtimeEffectBalanceEvent_mem_receiptRelationRootTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    runtimeJointBalancePresentedEvent depth ∈
      ((runtimeJointFaithfulStepAtReceiptRelationRoot
        observation nontrivial depth).history.observation 0).trace := by
  apply RootedAccountedUnfolding.frontier_mem_trace
  have frontierEq :
      ((runtimeJointFaithfulStepAtReceiptRelationRoot
        observation nontrivial depth).history.observation 0).frontier =
          [runtimeJointBalancePresentedEvent depth] := by
    change (runtimeJointRelationSeedAt
      (currentEffectStage
        (CanonicalUnitArithmeticRoot.finiteVisit depth).current)).frontier = _
    rw [currentEffectStage_finiteVisit,
      runtimeJointRelationSeedAt_frontier]
  have listMem : runtimeJointBalancePresentedEvent depth ∈
      [runtimeJointBalancePresentedEvent depth] := by simp
  exact frontierEq.symm ▸ listMem

/-- The stage-three common-action boundary is an actual dependent read of the
existing receipt-root source-boundary event.  Its installed projection,
integral and Mellin coordinates, exact trace membership, whole-ledger
write-back and generated next are consumed in one theorem mouth. -/
theorem stageThreeActionBoundary_receiptRootedWrite
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    type_of% (stageThreeActionBoundary_integralRootRead
      observation nontrivial) ∧
      type_of% (stageThreeActionBoundary_measurementRootRead
        observation nontrivial) ∧
      type_of% (requestedPrimePowerReceiptRelationInstalled_eq_projection
        observation nontrivial stageThreeConductorIndex.1
          stageThreeConductorIndex.2.1 stageThreeConductorIndex.2.2) ∧
      runtimeJointSourceBoundaryPresentedEvent stageThreeRuntimeStage ∈
        ((runtimeJointFaithfulStepAtReceiptRelationRoot observation nontrivial
          stageThreeRuntimeStage).history.observation 0).trace ∧
      type_of% (stageThreeJointMeasurement_rootEffect_write
        observation nontrivial) ∧
      type_of% (runtimePrimeExponentPoleReceiptRelation_factorizes
        observation nontrivial stageThreeRuntimeStage) ∧
      type_of% (runtimeJointFaithfulStepAtReceiptRelationRoot_factorizes
        observation nontrivial stageThreeRuntimeStage) := by
  refine ⟨stageThreeActionBoundary_integralRootRead observation nontrivial,
    stageThreeActionBoundary_measurementRootRead observation nontrivial,
    requestedPrimePowerReceiptRelationInstalled_eq_projection
      observation nontrivial stageThreeConductorIndex.1
        stageThreeConductorIndex.2.1 stageThreeConductorIndex.2.2,
    ?_,
    stageThreeJointMeasurement_rootEffect_write observation nontrivial,
    runtimePrimeExponentPoleReceiptRelation_factorizes
      observation nontrivial stageThreeRuntimeStage,
    runtimeJointFaithfulStepAtReceiptRelationRoot_factorizes
      observation nontrivial stageThreeRuntimeStage⟩
  change runtimeJointSourceBoundaryPresentedEvent stageThreeRuntimeStage ∈
    ((runtimeJointFaithfulStepAt observation nontrivial
      stageThreeRuntimeStage).history.observation 0).trace
  exact runtimeJointFaithfulObservation_sourceBoundary_mem
    observation nontrivial stageThreeRuntimeStage 0

/-- End-to-end source contract for one requested prime-power receipt.  The
arithmetic row generates the split relation and its unique zero fold; the
same fixed root exposes the inherited balance history, whole ledger, and
next. -/
theorem requestedPrimePower_receiptRelation_rootedConsumer
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    let cursor := scheduleIndex prime exponent
    let depth := PrimePower.Runtime.primePowerRuntimeStage prime exponent
    let installed := requestedPrimePowerReceiptRelationInstalled
      observation nontrivial prime exponent positive
    type_of% (requestedScheduleIndex_reads_existing_split
      observation nontrivial prime exponent positive) ∧
      type_of% (requestedPrimePowerReceiptRelationInstalled_eq_projection
        observation nontrivial prime exponent positive) ∧
      type_of% installed.occurrence_eq ∧
      type_of% installed.source_coordinate_projection ∧
      type_of% installed.source_allPrime_projection ∧
      (∀ role, (Source.zeroOwnedReceiptCoordinateOccurrence
          observation nontrivial cursor).root.2.roleValue role =
        receiptRoleValue observation nontrivial cursor role) ∧
      type_of% installed.source_root_relation ∧
      type_of% installed.source_halfDensity_normalization ∧
      type_of% installed.cofinal_root_projection ∧
      (∀ cursor role,
        (Cofinal.receiptCofinalFace observation nontrivial).root.root.2.table
            cursor role =
          receiptRoleValue observation nontrivial cursor role) ∧
      type_of% installed.cofinal_global_component_readback ∧
      (∀ cursor, type_of% (installed.cofinal_global_relation cursor)) ∧
      type_of% installed.exact_envelope_source_injective ∧
      (∀ table, type_of% (installed.exact_envelope_source_readback table)) ∧
      type_of% installed.arithmetic_observation.observation_injective ∧
      (∀ cursor role,
        type_of% (installed.arithmetic_observation.observation_readback
          cursor role)) ∧
      (∀ cursor, type_of%
        (installed.arithmetic_observation.role_separated_relation cursor)) ∧
      type_of%
        installed.factorization_cokernel_observation.joint_observation_injective ∧
      (∀ cursor role, type_of%
        (installed.factorization_cokernel_observation.source_readback
          cursor role)) ∧
      (∀ cursor role stage, type_of%
        (installed.factorization_cokernel_observation.local_factorization_square
          cursor role stage)) ∧
      (∀ cursor, type_of%
        (installed.factorization_cokernel_observation.role_fusion_zero cursor)) ∧
      type_of%
        installed.factorization_cokernel_observation.shared_factorization_seed ∧
      type_of%
        installed.factorization_cokernel_observation.shared_eulerLog_occurrence ∧
      (∀ stage, type_of%
        (installed.factorization_cokernel_observation.existing_pair_cofiber_read
          stage)) ∧
      type_of%
        installed.arithmetic_complexification_residual.occurrence_projects ∧
      type_of%
        installed.arithmetic_complexification_residual.global_integral_class_ne_zero ∧
      (∀ stage, type_of%
        (installed.arithmetic_complexification_residual.every_finite_complexification_zero
          stage)) ∧
      type_of%
        installed.arithmetic_complexification_residual.shared_factorization_seed ∧
      type_of%
        installed.arithmetic_character_perfectification.occurrence_projects ∧
      type_of%
        installed.arithmetic_character_perfectification.character_point_ne_zero ∧
      type_of%
        installed.arithmetic_character_perfectification.character_point_evaluation ∧
      type_of%
        installed.arithmetic_character_perfectification.source_generates_detecting_character ∧
      (∀ stage, type_of%
        (installed.arithmetic_character_perfectification.retains_finite_complexification_residual
          stage)) ∧
      type_of% installed.stage_three_arithmetic_character.occurrence_projects ∧
      (∀ value, type_of%
        (installed.stage_three_arithmetic_character.operator_range_zero value)) ∧
      type_of%
        installed.stage_three_arithmetic_character.local_endpoint_read_ne_zero ∧
      type_of%
        installed.stage_three_arithmetic_character.global_endpoint_read_ne_zero ∧
      type_of%
        installed.stage_three_arithmetic_character.canonical_point_read_ne_zero ∧
      type_of%
        installed.stage_three_arithmetic_mellin_common_action.occurrence_projects ∧
      type_of%
        installed.stage_three_arithmetic_mellin_common_action.arithmetic_base_ne_zero ∧
      type_of%
        installed.stage_three_arithmetic_mellin_common_action.mellin_measurement_generated ∧
      type_of%
        installed.stage_three_arithmetic_mellin_common_action.actual_prime ∧
      type_of%
        installed.stage_three_arithmetic_mellin_common_action.actual_scale ∧
      type_of%
        installed.stage_three_arithmetic_mellin_common_action.generator_square ∧
      type_of%
        installed.stage_three_arithmetic_mellin_action_boundary.boundary_is_receipt ∧
      type_of%
        installed.stage_three_arithmetic_mellin_action_boundary.joint_measurement_write ∧
      type_of%
        installed.stage_three_arithmetic_mellin_action_boundary.incidence_readback ∧
      type_of%
        installed.stage_three_arithmetic_mellin_action_boundary.root_effect_write ∧
      (primeExponentPoleReceiptRelationOccurrence
          observation nontrivial cursor).map
            PrimeExponentPoleReceiptRelationPointAt.certifiedRow =
        certifiedRowOccurrence cursor ∧
      retainedEnergyVerticalPresentedEvent ∈
          (primeExponentPoleReceiptPresentedRelationOccurrence
            observation nontrivial cursor).trace ∧
      (primeExponentPoleReceiptPresentedRelationOccurrence
          observation nontrivial cursor).fold
            (receiptWholeOccurrenceNodeAlgebra
              observation nontrivial cursor) = 0 ∧
      runtimeJointBalancePresentedEvent depth ∈
        ((runtimeJointFaithfulStepAtReceiptRelationRoot
          observation nontrivial depth).history.observation 0).trace ∧
      type_of% (runtimePrimeExponentPoleReceiptRelation_factorizes
        observation nontrivial depth) ∧
      type_of% (runtimeJointFaithfulStepAtReceiptRelationRoot_factorizes
        observation nontrivial depth) := by
  dsimp only
  let installed := requestedPrimePowerReceiptRelationInstalled
    observation nontrivial prime exponent positive
  exact ⟨requestedScheduleIndex_reads_existing_split
      observation nontrivial prime exponent positive,
    requestedPrimePowerReceiptRelationInstalled_eq_projection
      observation nontrivial prime exponent positive,
    installed.occurrence_eq,
    installed.source_coordinate_projection,
    installed.source_allPrime_projection,
    installed.source_role_specialization,
    installed.source_root_relation,
    installed.source_halfDensity_normalization,
    installed.cofinal_root_projection,
    installed.cofinal_role_readback,
    installed.cofinal_global_component_readback,
    installed.cofinal_global_relation,
    installed.exact_envelope_source_injective,
    installed.exact_envelope_source_readback,
    installed.arithmetic_observation.observation_injective,
    installed.arithmetic_observation.observation_readback,
    installed.arithmetic_observation.role_separated_relation,
    installed.factorization_cokernel_observation.joint_observation_injective,
    installed.factorization_cokernel_observation.source_readback,
    installed.factorization_cokernel_observation.local_factorization_square,
    installed.factorization_cokernel_observation.role_fusion_zero,
    installed.factorization_cokernel_observation.shared_factorization_seed,
    installed.factorization_cokernel_observation.shared_eulerLog_occurrence,
    installed.factorization_cokernel_observation.existing_pair_cofiber_read,
    installed.arithmetic_complexification_residual.occurrence_projects,
    installed.arithmetic_complexification_residual.global_integral_class_ne_zero,
    installed.arithmetic_complexification_residual.every_finite_complexification_zero,
    installed.arithmetic_complexification_residual.shared_factorization_seed,
    installed.arithmetic_character_perfectification.occurrence_projects,
    installed.arithmetic_character_perfectification.character_point_ne_zero,
    installed.arithmetic_character_perfectification.character_point_evaluation,
    installed.arithmetic_character_perfectification.source_generates_detecting_character,
    installed.arithmetic_character_perfectification.retains_finite_complexification_residual,
    installed.stage_three_arithmetic_character.occurrence_projects,
    installed.stage_three_arithmetic_character.operator_range_zero,
    installed.stage_three_arithmetic_character.local_endpoint_read_ne_zero,
    installed.stage_three_arithmetic_character.global_endpoint_read_ne_zero,
    installed.stage_three_arithmetic_character.canonical_point_read_ne_zero,
    installed.stage_three_arithmetic_mellin_common_action.occurrence_projects,
    installed.stage_three_arithmetic_mellin_common_action.arithmetic_base_ne_zero,
    installed.stage_three_arithmetic_mellin_common_action.mellin_measurement_generated,
    installed.stage_three_arithmetic_mellin_common_action.actual_prime,
    installed.stage_three_arithmetic_mellin_common_action.actual_scale,
    installed.stage_three_arithmetic_mellin_common_action.generator_square,
    installed.stage_three_arithmetic_mellin_action_boundary.boundary_is_receipt,
    installed.stage_three_arithmetic_mellin_action_boundary.joint_measurement_write,
    installed.stage_three_arithmetic_mellin_action_boundary.incidence_readback,
    installed.stage_three_arithmetic_mellin_action_boundary.root_effect_write,
    installed.certifiedRow_projection,
    installed.relation_mem,
    installed.whole_fold_zero,
    runtimeEffectBalanceEvent_mem_receiptRelationRootTrace
      observation nontrivial _,
    runtimePrimeExponentPoleReceiptRelation_factorizes
      observation nontrivial _,
    runtimeJointFaithfulStepAtReceiptRelationRoot_factorizes
      observation nontrivial _⟩

end
end ReceiptRelation
end PrimePowerCurrent
end History
end Conductor
end MuntzGraph
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
