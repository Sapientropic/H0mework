import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Bearer.Source.SourceGeneratedPlatformGateAffectedBearerIncidence
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Celebration.Channel.Consumer.ProofCarryingContributionCapacityPostSettlementChannelFamily

/-!
# Full paid transport of old gates through platform admission

The revised channel sum does not by itself prove that tenure and health
survive operationally.  This module consumes each root-installed channel at
the exact right replay index and transports its relation witness, payment,
settlement, service, feasible exit, root consumer and generated next together
with the old embedding into the revised carrier.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPlatformGateOldPaidChannelTransport

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedPlatformChannelRevisionCandidate
open M14SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransport
open M14SourceGeneratedCycleMemoryPlatformGateU8
open M14SourceGeneratedPlatformGateAffectedBearerIncidence

def platformGateOldPaidChannelIndexAt (boundary : Nat) : Nat :=
  boundary + 2

@[simp] theorem platformGateOldPaidChannelCurrent_eq_rightCurrent
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    contributionCapacityPostSettlementEssentialAccessChannelCurrentAt oldVisit
        sourceIndex (platformGateOldPaidChannelIndexAt boundary) =
      rightCurrentAt oldVisit sourceIndex boundary :=
  rfl

def platformGateOldPaidChannelAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) (channel : EssentialAccessChannel) :
    ConsumedContributionCapacityPostSettlementChannelAt oldVisit sourceIndex
      (platformGateOldPaidChannelIndexAt boundary) channel :=
  proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
    sourceIndex (platformGateOldPaidChannelIndexAt boundary) channel

def platformGateOldRevisedChannelAt (boundary : Nat)
    (channel : EssentialAccessChannel) :
    RevisedPaidEssentialAccessChannelAt
      (sourceGeneratedPlatformChannelRevisionCandidateAt boundary
        ).obstruction :=
  .inl channel

theorem platformGateOldRevisedChannel_seed_preserved
    (boundary : Nat) (channel : EssentialAccessChannel) :
    revisedChannelSeed
        (obstruction :=
          (sourceGeneratedPlatformChannelRevisionCandidateAt boundary
            ).obstruction)
        (platformGateOldRevisedChannelAt boundary channel) =
      channelSeed channel :=
  rfl

theorem platformGateOldPaidChannel_paymentOccurrenceExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : EssentialAccessChannel) :
    (platformGateOldPaidChannelAt oldVisit sourceIndex boundary channel
      ).2.rootReadCarrier.existingPaymentOccurrence =
      ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
        ).paymentOccurrence := by
  rw [(platformGateOldPaidChannelAt oldVisit sourceIndex boundary channel
    ).2.paymentOccurrence_exact]
  rfl

theorem platformGateOldPaidChannel_settlementExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : EssentialAccessChannel) :
    (platformGateOldPaidChannelAt oldVisit sourceIndex boundary channel
      ).2.rootReadCarrier.existingActualSettlement =
      ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
        ).actualSettlement := by
  rw [(platformGateOldPaidChannelAt oldVisit sourceIndex boundary channel
    ).2.actualSettlement_exact]
  rfl

theorem platformGateOldPaidChannel_rootOccurrenceExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : EssentialAccessChannel) :
    (platformGateOldPaidChannelAt oldVisit sourceIndex boundary channel
      ).1.actualExit.paymentOccurrence.rootOccurrence =
      M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (.finite (oldRootVisitAt oldVisit sourceIndex boundary)) := by
  exact (platformGateOldPaidChannelAt oldVisit sourceIndex boundary channel
    ).1.paymentRootOccurrence_exact

theorem platformGateOldPaidChannel_actualNextExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : EssentialAccessChannel) :
    (platformGateOldPaidChannelAt oldVisit sourceIndex boundary channel
      ).2.actualNext =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (rightCurrentAt oldVisit sourceIndex boundary + 1) := by
  change
    (platformGateOldPaidChannelAt oldVisit sourceIndex boundary channel
      ).2.actualNext =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
          oldVisit sourceIndex (platformGateOldPaidChannelIndexAt boundary) + 1)
  exact (platformGateOldPaidChannelAt oldVisit sourceIndex boundary channel
    ).2.actualNext_commutes

inductive SourceGeneratedPlatformGateOldPaidChannelTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : EssentialAccessChannel) : Type 31
  | private transported

def sourceGeneratedPlatformGateOldPaidChannelTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : EssentialAccessChannel) :
    SourceGeneratedPlatformGateOldPaidChannelTransportAt oldVisit sourceIndex
      boundary channel :=
  .transported

namespace SourceGeneratedPlatformGateOldPaidChannelTransportAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  {channel : EssentialAccessChannel}
  (transport : SourceGeneratedPlatformGateOldPaidChannelTransportAt oldVisit
    sourceIndex boundary channel)

def bearerIncidence :
    SourceGeneratedPlatformGateAffectedBearerIncidenceAt oldVisit sourceIndex
      boundary := by
  cases transport
  exact sourceGeneratedPlatformGateAffectedBearerIncidenceAt oldVisit
    sourceIndex boundary

def consumed : ConsumedContributionCapacityPostSettlementChannelAt oldVisit
    sourceIndex (platformGateOldPaidChannelIndexAt boundary) channel := by
  cases transport
  exact platformGateOldPaidChannelAt oldVisit sourceIndex boundary channel

def revisedChannel : RevisedPaidEssentialAccessChannelAt
    (sourceGeneratedPlatformChannelRevisionCandidateAt boundary
      ).obstruction := by
  cases transport
  exact platformGateOldRevisedChannelAt boundary channel

def paymentReceipt := (consumed transport).2.paymentReceipt

def routeReceipt := (consumed transport).2.routeReceipt

def serviceReceipt := (consumed transport).2.serviceReceipt

def feasibleExit := (consumed transport).2.rootReadCarrier.feasible

def responsibilityConsumer := (consumed transport).2.responsibilityConsumer

def actualNext := (consumed transport).2.actualNext

theorem revisedSeedPreserved : revisedChannelSeed
      (obstruction :=
        (sourceGeneratedPlatformChannelRevisionCandidateAt boundary
          ).obstruction)
      (revisedChannel transport) = channelSeed channel :=
  platformGateOldRevisedChannel_seed_preserved boundary channel

theorem relationWitnessReturns :
    ((consumed transport).2.relationWitnessReturn).1.actor
          essentialAccessRelationCompiler = channelActor channel ∧
      essentialAccessRelationCompiler.relationOf
          ((consumed transport).2.relationWitnessReturn).1 =
        channelRelation channel :=
  (consumed transport).2.relationWitnessReturn_exact

theorem paymentOccurrenceExact :
    (consumed transport).2.rootReadCarrier.existingPaymentOccurrence =
      ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
        ).paymentOccurrence :=
  platformGateOldPaidChannel_paymentOccurrenceExact oldVisit sourceIndex
    boundary channel

theorem settlementExact :
    (consumed transport).2.rootReadCarrier.existingActualSettlement =
      ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
        ).actualSettlement :=
  platformGateOldPaidChannel_settlementExact oldVisit sourceIndex boundary
    channel

theorem rootOccurrenceExact :
    (consumed transport).1.actualExit.paymentOccurrence.rootOccurrence =
      M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (.finite (oldRootVisitAt oldVisit sourceIndex boundary)) :=
  platformGateOldPaidChannel_rootOccurrenceExact oldVisit sourceIndex boundary
    channel

theorem nextExact : actualNext transport =
    contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
      (rightCurrentAt oldVisit sourceIndex boundary + 1) :=
  platformGateOldPaidChannel_actualNextExact oldVisit sourceIndex boundary
    channel

end SourceGeneratedPlatformGateOldPaidChannelTransportAt

theorem platformGateOldPaidChannelTransport_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : EssentialAccessChannel) :
    let transport := sourceGeneratedPlatformGateOldPaidChannelTransportAt
      oldVisit sourceIndex boundary channel
    type_of% (platformGateAffectedBearerIncidence_directConsumer oldVisit
      sourceIndex boundary) ∧
      revisedChannelSeed
          (obstruction :=
            (sourceGeneratedPlatformChannelRevisionCandidateAt boundary
              ).obstruction)
          transport.revisedChannel = channelSeed channel ∧
      transport.consumed.2.rootReadCarrier.existingPaymentOccurrence =
        ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
          ).paymentOccurrence ∧
      transport.consumed.2.rootReadCarrier.existingActualSettlement =
        ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
          ).actualSettlement ∧
      Nonempty (type_of% transport.serviceReceipt) ∧
      Nonempty (type_of% transport.feasibleExit) ∧
      Nonempty (RenewalResponsibilityConsumerAt
        transport.consumed.1.actualExit.paymentOccurrence.installed.operationalAuthority) ∧
      transport.actualNext =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (rightCurrentAt oldVisit sourceIndex boundary + 1) := by
  dsimp
  let transport := sourceGeneratedPlatformGateOldPaidChannelTransportAt
    oldVisit sourceIndex boundary channel
  exact ⟨platformGateAffectedBearerIncidence_directConsumer oldVisit
      sourceIndex boundary,
    transport.revisedSeedPreserved,
    transport.paymentOccurrenceExact,
    transport.settlementExact,
    ⟨transport.serviceReceipt⟩,
    ⟨transport.feasibleExit⟩,
    ⟨transport.responsibilityConsumer⟩,
    transport.nextExact⟩

theorem platformGateTenureHealthPaidTransports_sameNext
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (sourceGeneratedPlatformGateOldPaidChannelTransportAt oldVisit
      sourceIndex boundary tenureAuthority).actualNext =
      (sourceGeneratedPlatformGateOldPaidChannelTransportAt oldVisit
        sourceIndex boundary healthAuthority).actualNext := by
  rw [SourceGeneratedPlatformGateOldPaidChannelTransportAt.nextExact,
    SourceGeneratedPlatformGateOldPaidChannelTransportAt.nextExact]

end
end M14ProofCarryingPlatformGateOldPaidChannelTransport
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPlatformGateOldPaidChannelTransport.platformGateOldPaidChannel_paymentOccurrenceExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPlatformGateOldPaidChannelTransport.sourceGeneratedPlatformGateOldPaidChannelTransportAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPlatformGateOldPaidChannelTransport.platformGateOldPaidChannelTransport_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPlatformGateOldPaidChannelTransport.platformGateTenureHealthPaidTransports_sameNext
