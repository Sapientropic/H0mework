import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Policy.UBIPolicyBreakingOccurrence
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M13.Consumer.ReflexiveTheoryConsumerRegression

/-!
# M14 UBI-policy self-U8 direct consumer

The UBI capture-collapse classifier now generates the exact mother-law audit
and rooted gate consumed by the existing M13 revolutionary runtime.  This
file proves identity of the gate, minimal coface, revised core, first write,
claim migration, and later retirement.  It stores no second self-U8 carrier.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14UBIPolicySelfU8Regression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Theory Revision Audit Settlement
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalInquiryRuntime
open M9ProofCarryingRenewalU8Revision
open M14UBIPeriodicActualServiceCapacity
open M14UBIPolicyBreakingOccurrence

@[simp] theorem policyGate_rooted_is_selfU8_rooted :
    u8Gate.rooted = M13SelfU8Regression.selfU8.rooted :=
  rfl

@[simp] theorem policyGate_coface_is_selfU8_coface :
    u8Gate.minimalCoface = M13SelfU8Regression.selfU8.minimalCoface :=
  rfl

@[simp] theorem policyGate_rooted_is_jointCore_rooted :
    u8Gate.rooted = jointCore.frontier.rooted :=
  rfl

@[simp] theorem policyGate_coface_is_jointCore_coface :
    u8Gate.minimalCoface = jointCore.frontier.coface :=
  rfl

theorem runtime_consumes_jointCore_after_policy_factorization :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      jointCore jointRuntime 0 :=
  M13SelfU8Regression.runtime_consumes_exact_joint_core

theorem policy_scope_is_selfU8_row :
    audit.scopedEntry = M13SelfU8Regression.selfU8.rooted.rootEntry :=
  rfl

/-- The policy gate's generated coface factors directly into the exact
revised carrier consumed by `jointCore`; this is the missing causal bridge
from the policy audit to the runtime realization. -/
theorem policyGate_factorizes_into_jointCore : Nonempty
    (FaithfulCofaceMorphism u8Gate.minimalCoface
      jointCore.revision.generate.toAdmissibleMinimalCoface) :=
  ⟨jointCore.cofaceFactorization.1⟩

theorem policyGate_attachedRealization_is_jointCore : Nonempty
    (SourceGeneratedAttachedCofaceRealizationAt
      jointCore.revision.generate) :=
  ⟨jointCore.cofaceFactorization.2⟩

@[simp] theorem policyCore_firstWrite_is_selfU8_firstWrite :
    jointCore.cofaceFactorization.2.firstWrite =
      M13SelfU8Regression.selfU8.firstWrite :=
  rfl

theorem policyCore_firstWriteConsumes_is_selfU8 :
    HEq jointCore.cofaceFactorization.2.firstWriteConsumes
      M13SelfU8Regression.selfU8.firstWriteConsumes :=
  HEq.rfl

/-- Exact first-write-to-claim-lifecycle commuting mouth. -/
theorem policy_firstWrite_claimMigration_commutes :
    M13ClaimMigrationRetirementRegression.runtimeFirstWrite =
        jointCore.cofaceFactorization.2.firstWrite ∧
      HEq M13ClaimMigrationRetirementRegression.runtimeFirstWriteConsumes
        jointCore.cofaceFactorization.2.firstWriteConsumes ∧
      M13ReflexiveClaimLifecycleFixture.ClaimP.boundarySource
          M13ClaimMigrationRetirementRegression.migration.firstWriteSettlement.event =
        (⟨(0 : Nat),
          M9ProofCarryingRenewalU8RevisedWorld.revisedLivingRoot.emitted
            (0 : Nat)⟩ : M13ReflexiveClaimLifecycleFixture.RevisedRootOccurrence) ∧
      M13ClaimMigrationRetirementRegression.firstWholeLedgerWriteBack =
        (M9ProofCarryingRenewalU8RevisedWorld.revisedLivingRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            M13ClaimMigrationRetirementRegression.firstVisit).wholeLedgerWriteBack ∧
      M13ClaimMigrationRetirementRegression.firstGeneratedNext =
        M9ProofCarryingRenewalU8RevisedWorld.revisedLivingRoot.generatedNextCurrentAt
          M13ClaimMigrationRetirementRegression.firstVisit :=
  ⟨rfl, HEq.rfl,
    M13ClaimMigrationRetirementRegression.migration_sourceEvent_is_rootOccurrence,
    rfl, rfl⟩

theorem policy_breaking_occurrence_generates_selfU8_path :
    ((geometryCompilerAt 0).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt 0).actionableExitCapacity = 0) ∧
      u8Gate.rooted = M13SelfU8Regression.selfU8.rooted ∧
      u8Gate.minimalCoface = M13SelfU8Regression.selfU8.minimalCoface ∧
      Nonempty (FaithfulCofaceMorphism u8Gate.minimalCoface
        jointCore.revision.generate.toAdmissibleMinimalCoface) ∧
      SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
        jointCore jointRuntime 0 :=
  ⟨audit_breaking_capacity_collapse,
    policyGate_rooted_is_selfU8_rooted,
    policyGate_coface_is_selfU8_coface,
    policyGate_factorizes_into_jointCore,
    runtime_consumes_jointCore_after_policy_factorization⟩

structure UBIPolicySelfU8Certificate : Prop where
  exactBreakingOccurrence :
    (⟨jointVisit.current, audit.rootOccurrence⟩ :
      Sigma M14UBIPolicyBreakingOccurrence.Root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt) =
      ⟨(M14UBIPeriodicRootHistory.temporalVisitAt 0).current,
        (M14UBIPeriodicRootHistory.periodicSourceBackedPaymentAt 0
          ).rootOccurrence.occurrence⟩
  capacityCollapse :
    (geometryCompilerAt 0).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt 0).actionableExitCapacity = 0
  policyScopeIsFailureRow : audit.scopedEntry = audit.failureFace.rootEntry
  rootedIsSelfU8 : u8Gate.rooted = M13SelfU8Regression.selfU8.rooted
  cofaceIsSelfU8 :
    u8Gate.minimalCoface = M13SelfU8Regression.selfU8.minimalCoface
  gateToCoreFactorization : Nonempty
    (FaithfulCofaceMorphism u8Gate.minimalCoface
      jointCore.revision.generate.toAdmissibleMinimalCoface)
  attachedRealization : Nonempty
    (SourceGeneratedAttachedCofaceRealizationAt jointCore.revision.generate)
  runtimeConsumesCore :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      jointCore jointRuntime 0
  exactFirstWrite : jointCore.cofaceFactorization.2.firstWrite =
    M13SelfU8Regression.selfU8.firstWrite
  exactFirstWriteConsumes :
    HEq jointCore.cofaceFactorization.2.firstWriteConsumes
      M13SelfU8Regression.selfU8.firstWriteConsumes
  firstWriteClaimMigrationCommutes :
    M13ClaimMigrationRetirementRegression.runtimeFirstWrite =
        jointCore.cofaceFactorization.2.firstWrite ∧
      HEq M13ClaimMigrationRetirementRegression.runtimeFirstWriteConsumes
        jointCore.cofaceFactorization.2.firstWriteConsumes ∧
      M13ReflexiveClaimLifecycleFixture.ClaimP.boundarySource
          M13ClaimMigrationRetirementRegression.migration.firstWriteSettlement.event =
        (⟨(0 : Nat),
          M9ProofCarryingRenewalU8RevisedWorld.revisedLivingRoot.emitted
            (0 : Nat)⟩ : M13ReflexiveClaimLifecycleFixture.RevisedRootOccurrence) ∧
      M13ClaimMigrationRetirementRegression.firstWholeLedgerWriteBack =
        (M9ProofCarryingRenewalU8RevisedWorld.revisedLivingRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            M13ClaimMigrationRetirementRegression.firstVisit).wholeLedgerWriteBack ∧
      M13ClaimMigrationRetirementRegression.firstGeneratedNext =
        M9ProofCarryingRenewalU8RevisedWorld.revisedLivingRoot.generatedNextCurrentAt
          M13ClaimMigrationRetirementRegression.firstVisit
  firstWriteTargetsLaterVisit :
    M13ClaimMigrationRetirementRegression.runtimeFirstWrite.targetVisit =
      M9ProofCarryingRenewalU8RevisedWorld.revisedVisitAt 1
  migrationFaceInstalled :
    M9ProofCarryingRenewalU8RevisedWorld.revisedLivingRoot.toAuthoritativeRoot.source.projectionLaw.project
      .claimMigration
      (M9ProofCarryingRenewalU8RevisedWorld.revisedLivingRoot.emitted
        M13ClaimMigrationRetirementRegression.firstVisit.current)
      ⟨rfl⟩ = M13ClaimMigrationRetirementRegression.migrationFace
  migrationFaceExact :
    M13ReflexiveClaimLifecycleFixture.RootClaimMigrationFaceAt.exactMigration
      M13ClaimMigrationRetirementRegression.migrationFace =
        M13ClaimMigrationRetirementRegression.migration
  replacementRetainsLiveClaim : Nonempty
    (ExactSettlementEdge.LiveResidualAt
      M13ClaimMigrationRetirementRegression.migration.firstWriteSettlement)
  replacementIsNotRetirement : ¬ Nonempty
    (ExactSettlementEdge.ClosedSettlementAt
      M13ClaimMigrationRetirementRegression.migration.firstWriteSettlement)
  retirementFaceInstalled :
    M9ProofCarryingRenewalU8RevisedWorld.revisedLivingRoot.toAuthoritativeRoot.source.projectionLaw.project
      .claimRetirement
      (M9ProofCarryingRenewalU8RevisedWorld.revisedLivingRoot.emitted
        M13ClaimMigrationRetirementRegression.laterVisit.current)
      ⟨rfl⟩ = M13ClaimMigrationRetirementRegression.retirementFace
  retirementFaceExact :
    M13ReflexiveClaimLifecycleFixture.RootClaimRetirementFaceAt.exactRetirement
      M13ClaimMigrationRetirementRegression.retirementFace =
        M13ClaimMigrationRetirementRegression.retirement
  laterActualRetirement : ResponsibilityState.DisappearsAt
    M13ClaimMigrationRetirementRegression.migration.firstWriteSettlement.edge.target
    (M13ClaimMigrationRetirementRegression.migration.laterSettlement
      M13ClaimMigrationRetirementRegression.laterConsumer).edge.target
    (M13ClaimMigrationRetirementRegression.migration.laterSettlement
      M13ClaimMigrationRetirementRegression.laterConsumer).slot.val
  bareCapacityNoU8 : True
  bareBreakingNoU8 : True

theorem ubiPolicySelfU8DirectConsumer : UBIPolicySelfU8Certificate where
  exactBreakingOccurrence := audit_rootOccurrence_is_payment_rootOccurrence
  capacityCollapse := audit_breaking_capacity_collapse
  policyScopeIsFailureRow := audit.scopedEntry_eq_failureRow
  rootedIsSelfU8 := policyGate_rooted_is_selfU8_rooted
  cofaceIsSelfU8 := policyGate_coface_is_selfU8_coface
  gateToCoreFactorization := policyGate_factorizes_into_jointCore
  attachedRealization := policyGate_attachedRealization_is_jointCore
  runtimeConsumesCore :=
    runtime_consumes_jointCore_after_policy_factorization
  exactFirstWrite := policyCore_firstWrite_is_selfU8_firstWrite
  exactFirstWriteConsumes := policyCore_firstWriteConsumes_is_selfU8
  firstWriteClaimMigrationCommutes :=
    policy_firstWrite_claimMigration_commutes
  firstWriteTargetsLaterVisit :=
    M13ClaimMigrationRetirementRegression.runtimeFirstWrite_targetVisit_eq_laterRootVisit
  migrationFaceInstalled :=
    M13ClaimMigrationRetirementRegression.migrationFace_is_revisedRoot_projection
  migrationFaceExact := M13ClaimMigrationRetirementRegression.migrationFace_exact
  replacementRetainsLiveClaim :=
    M13ClaimMigrationRetirementRegression.replaced_claim_is_still_live_and_not_closed.1
  replacementIsNotRetirement :=
    M13ClaimMigrationRetirementRegression.replaced_claim_is_still_live_and_not_closed.2
  retirementFaceInstalled :=
    M13ClaimMigrationRetirementRegression.retirementFace_is_revisedRoot_projection
  retirementFaceExact :=
    M13ClaimMigrationRetirementRegression.retirementFace_exact
  laterActualRetirement :=
    M13ClaimMigrationRetirementRegression.later_event_closes_migrated_claim
  bareCapacityNoU8 := bare_capacity_collapse_cannot_open_U8
  bareBreakingNoU8 := bare_policy_breaking_occurrence_cannot_open_U8

end
end M14UBIPolicySelfU8Regression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14UBIPolicySelfU8Regression.policy_breaking_occurrence_generates_selfU8_path
#print axioms SaturationMonoid.ProcessGame.Society.M14UBIPolicySelfU8Regression.ubiPolicySelfU8DirectConsumer
