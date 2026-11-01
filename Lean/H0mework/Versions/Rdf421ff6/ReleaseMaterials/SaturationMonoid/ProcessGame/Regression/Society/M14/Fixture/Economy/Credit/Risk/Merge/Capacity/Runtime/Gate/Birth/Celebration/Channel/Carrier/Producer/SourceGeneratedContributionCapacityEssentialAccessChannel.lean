import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Sector.EssentialAccessSectorRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.UBIPeriodicActualServiceCapacity

/-!
# Existing-actual-exit essential-access channel

Tenure and health are the existing exact relation-authority test fibre.  This
carrier reindexes each relation-generated channel by one already generated
periodic actual exit and the same actual settlement's served slot.  It
retains payment, route, service, root consumer and a returnable relation
witness without creating a channel registry, actor table or future schedule.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityEssentialAccessChannel

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3FiniteExchangeFixture
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIProofCarryingRootCapacity
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression

abbrev EssentialAccessChannel := EssentialAccessRelationAuthority

def channelSeed : EssentialAccessChannel →
    essentialAccessRelationCompiler.ExactRelationSeed
  | .tenure _ => exactEssentialAccessSeed .tenure
  | .health _ => exactEssentialAccessSeed .health

def channelActor (channel : EssentialAccessChannel) :
    essentialAccessRelationCompiler.Actor :=
  (channelSeed channel).actor essentialAccessRelationCompiler

def channelRelation (channel : EssentialAccessChannel) :
    essentialAccessRelationCompiler.GeneratedRelation :=
  essentialAccessRelationCompiler.relationOf (channelSeed channel)

def channelPhase (channel : EssentialAccessChannel) : EssentialAccessSector :=
  essentialAccessRelationCompiler.phaseStep (channelRelation channel)

def channelTargetRole : EssentialAccessChannel → EssentialAccessRole
  | .tenure _ => .tenureProvider
  | .health _ => .healthProvider

theorem channelInterest (channel : EssentialAccessChannel) :
    essentialAccessRelationCompiler.GeneratedInterestAt
      (channelActor channel) (channelRelation channel) := by
  cases channel with
  | tenure interest => exact interest
  | health interest => exact interest

theorem channelPhase_relationGenerated (channel : EssentialAccessChannel) :
    essentialAccessRelationCompiler.phaseStep (channelRelation channel) =
      channelPhase channel :=
  rfl

theorem channelTargetRole_relationGenerated
    (channel : EssentialAccessChannel) :
    essentialAccessRelationCompiler.RelationRoleAt
      (channelActor channel) (channelRelation channel) .target
        (channelTargetRole channel) := by
  cases channel with
  | tenure interest => exact ⟨interest, rfl⟩
  | health interest => exact ⟨interest, rfl⟩

def channelSlotAt (depth : Nat) : EssentialAccessChannel →
    Fin (anomiePhaseAt depth).served.length
  | .tenure _ => firstSlotAt depth
  | .health _ => ⟨1, by rw [anomiePhaseAt_served_length]; decide⟩

def channelCrossingAt (depth : Nat) (channel : EssentialAccessChannel) :
    (crossingCompilerAt depth).ExactCrossing :=
  ExactServedCrossingDebitedRunAt.servicedCrossingAt
    (phase := anomiePhaseAt depth)
    (crossingCompiler := crossingCompilerAt depth)
    (channelSlotAt depth channel)

def channelServiceReceiptAt (depth : Nat)
    (channel : EssentialAccessChannel) :
    (serviceCompilerAt depth).ServesAt
      ((anomiePhaseAt depth).served.get (channelSlotAt depth channel))
      (run.events.get
        (Fin.cast (actualSettlementAt depth).eventsLength_eq_allocated.symm
          (channelSlotAt depth channel))) :=
  (actualSettlementAt depth).serviceReceiptAt _

def channelFeasibleExitAt (depth : Nat)
    (channel : EssentialAccessChannel) :
    ExactFeasibleExitEdgeAt (geometryCompilerAt depth)
      ExitFutureCode.leave (channelSlotAt depth channel) :=
  FeasibleExitEdgeAt.generate
    (actualSettlement := actualSettlementAt depth)
    actionableExit.2 SourceBackedUBIPaymentReceiptAt.generate
      (SourceGeneratedUBIRouteReceiptAt.generate
        (channelCrossingAt depth channel))

abbrev EssentialAccessChannelWitnessReturnAt
    (channel : EssentialAccessChannel) :=
  Sigma fun seed : essentialAccessRelationCompiler.ExactRelationSeed =>
    PLift (seed.actor essentialAccessRelationCompiler = channelActor channel) ×
      PLift (essentialAccessRelationCompiler.relationOf seed =
        channelRelation channel)

def essentialAccessChannelWitnessReturnAt
    (channel : EssentialAccessChannel) :
    EssentialAccessChannelWitnessReturnAt channel :=
  ⟨channelSeed channel, PLift.up rfl, PLift.up rfl⟩

structure SourceGeneratedContributionCapacityEssentialAccessChannelAt
    (depth : Nat) (channel : EssentialAccessChannel)
    (existingActualExit : PeriodicActualServiceExitAt depth) : Type 20 where
  private mk ::
  relationInterest : essentialAccessRelationCompiler.GeneratedInterestAt
    (channelActor channel) (channelRelation channel)
  phaseGenerated :
    essentialAccessRelationCompiler.phaseStep (channelRelation channel) =
      channelPhase channel
  targetRoleGenerated : essentialAccessRelationCompiler.RelationRoleAt
    (channelActor channel) (channelRelation channel) .target
      (channelTargetRole channel)
  serviceReceipt : (serviceCompilerAt depth).ServesAt
    ((anomiePhaseAt depth).served.get (channelSlotAt depth channel))
    (run.events.get
      (Fin.cast (actualSettlementAt depth).eventsLength_eq_allocated.symm
        (channelSlotAt depth channel)))
  serviceReceiptExact : serviceReceipt =
    channelServiceReceiptAt depth channel
  feasible : ExactFeasibleExitEdgeAt (geometryCompilerAt depth)
    ExitFutureCode.leave (channelSlotAt depth channel)
  feasibleExact : feasible = channelFeasibleExitAt depth channel
  existingPaymentOccurrence : PeriodicSourceBackedPaymentAt depth
  existingPaymentOccurrence_eq :
    existingPaymentOccurrence = existingActualExit.paymentOccurrence
  existingActualSettlement : ExactServedCrossingDebitedRunAt
    (anomiePhaseAt depth) debited (serviceCompilerAt depth)
  existingActualSettlement_eq :
    existingActualSettlement = existingActualExit.actualSettlement
  paymentRootOccurrenceExact :
    existingActualExit.paymentOccurrence.rootOccurrence =
      M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (temporalVisitAt depth)
  rootConsumer : RenewalResponsibilityConsumerAt
    existingActualExit.paymentOccurrence.installed.operationalAuthority
  rootFactorization :
    existingActualExit.paymentOccurrence.installed.RootAnswerAndNextFactorizes
  witnessReturn : EssentialAccessChannelWitnessReturnAt channel

def sourceGeneratedContributionCapacityEssentialAccessChannelAt
    (depth : Nat) (channel : EssentialAccessChannel)
    (existingActualExit : PeriodicActualServiceExitAt depth) :
    SourceGeneratedContributionCapacityEssentialAccessChannelAt depth channel
      existingActualExit where
  relationInterest := channelInterest channel
  phaseGenerated := channelPhase_relationGenerated channel
  targetRoleGenerated := channelTargetRole_relationGenerated channel
  serviceReceipt := channelServiceReceiptAt depth channel
  serviceReceiptExact := rfl
  feasible := channelFeasibleExitAt depth channel
  feasibleExact := rfl
  existingPaymentOccurrence := existingActualExit.paymentOccurrence
  existingPaymentOccurrence_eq := rfl
  existingActualSettlement := existingActualExit.actualSettlement
  existingActualSettlement_eq := rfl
  paymentRootOccurrenceExact :=
    existingActualExit.paymentOccurrence.rootOccurrence_eq
  rootConsumer :=
    existingActualExit.paymentOccurrence.installed.rootResponsibilityConsumer
  rootFactorization := existingActualExit.rootFactorization
  witnessReturn := essentialAccessChannelWitnessReturnAt channel

namespace SourceGeneratedContributionCapacityEssentialAccessChannelAt

variable {depth : Nat} {channel : EssentialAccessChannel}
  {existingActualExit : PeriodicActualServiceExitAt depth}
  (generated : SourceGeneratedContributionCapacityEssentialAccessChannelAt
    depth channel existingActualExit)

def actor := channelActor channel

def relation := channelRelation channel

def phase := channelPhase channel

def targetRole := channelTargetRole channel

def paymentReceipt := generated.feasible.paymentReceipt

def routeReceipt := generated.feasible.routeReceipt

theorem paymentOccurrence_eq_input :
    generated.existingPaymentOccurrence =
      existingActualExit.paymentOccurrence :=
  generated.existingPaymentOccurrence_eq

theorem actualSettlement_eq_input :
    generated.existingActualSettlement = existingActualExit.actualSettlement :=
  generated.existingActualSettlement_eq

theorem witnessReturn_exact :
    generated.witnessReturn.1.actor essentialAccessRelationCompiler =
        channelActor channel ∧
      essentialAccessRelationCompiler.relationOf generated.witnessReturn.1 =
        channelRelation channel :=
  ⟨generated.witnessReturn.2.1.down, generated.witnessReturn.2.2.down⟩

end SourceGeneratedContributionCapacityEssentialAccessChannelAt

theorem essentialAccessChannels_sameVisible_differentPhase :
    protectedInterestReadout tenureAuthority =
        protectedInterestReadout healthAuthority ∧
      channelPhase tenureAuthority ≠ channelPhase healthAuthority :=
  ⟨protectedInterestReadout_same, sectorPhaseReadout_different⟩

theorem contributionCapacityEssentialAccessChannel_hasNoCallerPayload
    (depth : Nat) (channel : EssentialAccessChannel)
    (existingActualExit : PeriodicActualServiceExitAt depth) : True := by
  let generated :=
    sourceGeneratedContributionCapacityEssentialAccessChannelAt depth channel
      existingActualExit
  fail_if_success exact generated.participant
  fail_if_success exact generated.label
  fail_if_success exact generated.registry
  fail_if_success exact generated.schedule
  fail_if_success exact generated.future
  trivial

end
end M14SourceGeneratedContributionCapacityEssentialAccessChannel
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityEssentialAccessChannel.sourceGeneratedContributionCapacityEssentialAccessChannelAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityEssentialAccessChannel.SourceGeneratedContributionCapacityEssentialAccessChannelAt.witnessReturn_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityEssentialAccessChannel.essentialAccessChannels_sameVisible_differentPhase
