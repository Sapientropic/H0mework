import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Producer.SourceGeneratedContributionCapacityTargetOriginOrBirth
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Credit.Risk.Merge.Capacity.ProofCarryingContributionCapacityRuntimeRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Gate.Consumer.ProofCarryingContributionCapacityJointSettlementGateFrontier

/-!
# Direct consumer of target origin / birth admission

The consumer closes both controls.  The actual joint-settlement action's A13
target inventory is completely old-origin and cannot be relabelled fresh.
The capacity-U8 revised inventory is source-indexed: entries 0 and 1 retain
old debt origins, while entry 2 is the generated residual birth relative to
the embedded pre-revision old face.

Birth is not a no-preimage label.  The canonical birth simultaneously carries
fresh debt, generated row, initial causal authority, admitted obligation,
existing parent bearer and independent root consumer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityTargetOriginOrBirth

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ObstructionGeneratedMinimalCoface
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8Revision
open M14SourceGeneratedContributionCapacityU8TargetState
open M14ProofCarryingContributionCapacityRuntimeRegression
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedSequentialContributionCapacityJointSettlement
open M14SourceGeneratedContributionCapacityJointSettlementGateFrontier
open M14ProofCarryingContributionCapacityJointSettlementGateFrontier
open M14SourceGeneratedContributionCapacityTargetOriginOrBirth

abbrev CanonicalResidualBirth :=
  ExactGeneratedContributionCapacityResidualBirthAdmissionAt canonicalOldVisit

def canonicalResidualBirth : CanonicalResidualBirth :=
  sourceGeneratedContributionCapacityResidualBirthAdmission canonicalOldVisit

theorem contributionCapacityU8InheritedContributionFresh_isEmpty :
    IsEmpty
      (RootDebtFreshAt (CapacityU8NAt canonicalOldVisit)
        (contributionCapacityU8PreRevisionLedger canonicalOldVisit).support
        (contributionCapacityU8InheritedContribution canonicalOldVisit)) :=
  ⟨fun fresh => PEmpty.elim
    ((contributionCapacityU8InheritedContributionOrigin canonicalOldVisit
      ).excludesFresh fresh)⟩

theorem contributionCapacityU8InheritedObstructionFresh_isEmpty :
    IsEmpty
      (RootDebtFreshAt (CapacityU8NAt canonicalOldVisit)
        (contributionCapacityU8PreRevisionLedger canonicalOldVisit).support
        (contributionCapacityU8InheritedObstruction canonicalOldVisit)) :=
  ⟨fun fresh => PEmpty.elim
    ((contributionCapacityU8InheritedObstructionOrigin canonicalOldVisit
      ).excludesFresh fresh)⟩

theorem canonicalJointSettlementActualAction_ingressEveryTargetOld :
    (targetEntry :
      (contributionCapacityJointSettlementLiveLedger canonicalOldVisit).Entry) →
      Nonempty
        (Sigma fun oldEntry :
            (contributionCapacitySettlementSurvivorLedger
              canonicalOldVisit).Entry =>
          PLift
            ((contributionCapacityJointSettlementIngressPresentation
              canonicalOldVisit).forward oldEntry = targetEntry)) :=
  (generatedContributionCapacityJointSettlementActionAt canonicalOldVisit 1
    (CanonicalGateMaterialAt canonicalOldVisit 1)).receipt.ingressNoFresh

theorem bareFresh_noPreimage_row_obligation_orConsumer_cannot_retype_asBirth :
    True := by
  fail_if_success exact (canonicalResidualBirth.freshDebt : CanonicalResidualBirth)
  fail_if_success exact
    (canonicalResidualBirth.noOldPreimage : CanonicalResidualBirth)
  fail_if_success exact
    (canonicalResidualBirth.generatedRow : CanonicalResidualBirth)
  fail_if_success exact
    (canonicalResidualBirth.initialAuthority : CanonicalResidualBirth)
  fail_if_success exact (canonicalResidualBirth.obligation : CanonicalResidualBirth)
  fail_if_success exact (canonicalResidualBirth.consumer : CanonicalResidualBirth)
  fail_if_success exact ((2 : Fin 3) : CanonicalResidualBirth)
  trivial

structure ProofCarryingContributionCapacityTargetOriginOrBirth : Prop where
  capacityRuntime : Nonempty ProofCarryingContributionCapacityRuntimeCertificate
  jointGateRuntime :
    ProofCarryingContributionCapacityJointSettlementGateFrontier
  jointEveryTargetOldOrigin :
    (targetEntry :
      (contributionCapacityJointSettlementLiveLedger canonicalOldVisit).Entry) →
      Nonempty
        (ExactTargetDebtOriginAt
          (contributionCapacityJointSettlementLiveLedger canonicalOldVisit)
          targetEntry)
  jointEveryTargetNotFresh :
    (targetEntry :
      (contributionCapacityJointSettlementLiveLedger canonicalOldVisit).Entry) →
      IsEmpty
        (RootDebtFreshAt (JointSettlementNAt canonicalOldVisit)
          (contributionCapacityJointSettlementLiveLedger
            canonicalOldVisit).support targetEntry)
  jointActualActionIngressOld :
    (targetEntry :
      (contributionCapacityJointSettlementLiveLedger canonicalOldVisit).Entry) →
      Nonempty
        (Sigma fun oldEntry :
            (contributionCapacitySettlementSurvivorLedger
              canonicalOldVisit).Entry =>
          PLift
            ((contributionCapacityJointSettlementIngressPresentation
              canonicalOldVisit).forward oldEntry = targetEntry))
  everyU8TargetHasSourceGeneratedProvenance :
    (entryIndex : Fin 3) → Nonempty
      (ContributionCapacityU8TargetProvenanceAt canonicalOldVisit entryIndex)
  everyActualU8TargetHasIndexedProvenance :
    (targetEntry : (contributionCapacityU8Ledger canonicalOldVisit).Entry) →
      Nonempty
        (Sigma fun entryIndex : Fin 3 =>
          PLift
              (contributionCapacityU8EntryAt canonicalOldVisit entryIndex =
                targetEntry) ×
            ContributionCapacityU8TargetProvenanceAt canonicalOldVisit
              entryIndex)
  inheritedContributionNotBirth : IsEmpty
    (RootDebtFreshAt (CapacityU8NAt canonicalOldVisit)
      (contributionCapacityU8PreRevisionLedger canonicalOldVisit).support
      (contributionCapacityU8InheritedContribution canonicalOldVisit))
  inheritedObstructionNotBirth : IsEmpty
    (RootDebtFreshAt (CapacityU8NAt canonicalOldVisit)
      (contributionCapacityU8PreRevisionLedger canonicalOldVisit).support
      (contributionCapacityU8InheritedObstruction canonicalOldVisit))
  generatedResidualFresh : Nonempty
    (RootDebtFreshAt (CapacityU8NAt canonicalOldVisit)
      (contributionCapacityU8PreRevisionLedger canonicalOldVisit).support
      (contributionCapacityU8GeneratedResidual canonicalOldVisit))
  generatedResidualHasNoOldPreimage : IsEmpty
    (Sigma fun oldEntry : OpenResponsibilityAt
        (CutN (capacityActionRootedAt canonicalOldVisit))
        (contributionCapacityCutTargetSupport
          (capacityActionRootedAt canonicalOldVisit)) =>
      PLift
        ((CapacityCofaceAt canonicalOldVisit).cofaceLedgerRetract.forward
          oldEntry = contributionCapacityU8GeneratedResidual canonicalOldVisit))
  generatedResidualClaimHasNoOldPreimage : IsEmpty
    (Sigma fun oldClaim :
        (CutN (capacityActionRootedAt canonicalOldVisit)).Claim =>
      PLift
        ((CapacityCofaceAt canonicalOldVisit).translation.claim.forward
          oldClaim =
            (contributionCapacityU8GeneratedResidual canonicalOldVisit).claim))
  generatedResidualIncidenceHasNoOldPreimage : IsEmpty
    (Sigma fun oldIncidence :
        (CutN (capacityActionRootedAt canonicalOldVisit)).Incidence =>
      PLift
        ((CapacityCofaceAt canonicalOldVisit).translation.incidence.forward
          oldIncidence =
            (CapacityU8NAt canonicalOldVisit).incidenceAt
              (CapacityCofaceAt canonicalOldVisit).cofaceSupport))
  birthAdmissionGenerated : Nonempty CanonicalResidualBirth
  generatedResidualRow : Nonempty
    ((contributionCapacityU8InitialGenerated canonicalOldVisit
      ).GeneratedEntryRowAt
        (contributionCapacityU8GeneratedResidual canonicalOldVisit))
  generatedResidualInitialAuthority : Nonempty
    (SourceNativeLivingTemporalCausalEntryAuthorityAt
      (CapacityU8RootAt canonicalOldVisit)
      (contributionCapacityU8TemporalVisitAt canonicalOldVisit 0)
      (contributionCapacityU8GeneratedResidual canonicalOldVisit))
  generatedResidualStanding : Nonempty
    { obligation : AdmittedObligation
        (ContributionCapacityU8LifecycleV canonicalOldVisit) //
      obligation.content =
          (contributionCapacityU8GeneratedResidual canonicalOldVisit).1 ∧
        obligation.bearer =
          sourceGeneratedLossAllocationMaterial.parentBearer }
  generatedResidualIndependentConsumer : Nonempty
    (SourceNativeInquiryAnswerConsumerAt ()
      (ULift.up.{1, 0}
        (contributionCapacityU8InitialGenerated canonicalOldVisit).occurrence)
      (contributionCapacityU8GeneratedResidual canonicalOldVisit)
      (contributionCapacityU8InitialAnswerFaceAt canonicalOldVisit))

theorem proofCarryingContributionCapacityTargetOriginOrBirth :
    ProofCarryingContributionCapacityTargetOriginOrBirth where
  capacityRuntime :=
    ⟨proofCarryingContributionCapacityRuntimeCertificate⟩
  jointGateRuntime :=
    proofCarryingContributionCapacityJointSettlementGateFrontier
  jointEveryTargetOldOrigin := fun targetEntry =>
    ⟨contributionCapacityJointSettlementA13TargetDebtOriginAt
      canonicalOldVisit targetEntry⟩
  jointEveryTargetNotFresh :=
    contributionCapacityJointSettlementTargetFresh_isEmpty canonicalOldVisit
  jointActualActionIngressOld :=
    canonicalJointSettlementActualAction_ingressEveryTargetOld
  everyU8TargetHasSourceGeneratedProvenance := fun entryIndex =>
    ⟨contributionCapacityU8TargetProvenanceAt canonicalOldVisit entryIndex⟩
  everyActualU8TargetHasIndexedProvenance := fun targetEntry =>
    ⟨contributionCapacityU8AnyTargetProvenanceAt canonicalOldVisit
      targetEntry⟩
  inheritedContributionNotBirth :=
    contributionCapacityU8InheritedContributionFresh_isEmpty
  inheritedObstructionNotBirth :=
    contributionCapacityU8InheritedObstructionFresh_isEmpty
  generatedResidualFresh := ⟨canonicalResidualBirth.freshDebt⟩
  generatedResidualHasNoOldPreimage := canonicalResidualBirth.noOldPreimage
  generatedResidualClaimHasNoOldPreimage :=
    (generatedContributionCapacityTypedRevisionAt canonicalOldVisit
      ).revisedClaim_hasNoOldPreimage
  generatedResidualIncidenceHasNoOldPreimage :=
    (generatedContributionCapacityTypedRevisionAt canonicalOldVisit
      ).newOnlyIncidence_hasNoOldPreimage
  birthAdmissionGenerated := ⟨canonicalResidualBirth⟩
  generatedResidualRow := ⟨canonicalResidualBirth.generatedRow⟩
  generatedResidualInitialAuthority :=
    ⟨canonicalResidualBirth.initialAuthority⟩
  generatedResidualStanding :=
    ⟨⟨canonicalResidualBirth.obligation,
      by rw [canonicalResidualBirth.obligationExact]; rfl,
      canonicalResidualBirth.bearerExisting⟩⟩
  generatedResidualIndependentConsumer :=
    ⟨canonicalResidualBirth.consumer⟩

end
end M14ProofCarryingContributionCapacityTargetOriginOrBirth
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityTargetOriginOrBirth.proofCarryingContributionCapacityTargetOriginOrBirth
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityTargetOriginOrBirth.bareFresh_noPreimage_row_obligation_orConsumer_cannot_retype_asBirth
