import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Celebration.Producer.SourceGeneratedContributionCapacityPostSettlementFutureBirth

/-!
# Root-generated post-settlement essential-access channel

At one exact macro future-birth occurrence, the existing post-settlement root
projects a dependent tenure or health channel.  Relation identity, actor,
phase and target role come from the existing exact relation seed; payment,
route and service come from the occurrence-selected actual exit.  The token is
field-free and stores no channel registry, schedule, participant label, second
root or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open M3FiniteExchangeFixture
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14UBIPeriodicActualServiceCapacity
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityEssentialAccessChannel

def contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Nat :=
  contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit sourceIndex
    index

def contributionCapacityPostSettlementEssentialAccessChannelActualExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
        oldVisit sourceIndex index) :=
  contributionCapacityPostSettlementFutureBirthActualExitAt oldVisit
    sourceIndex index

/-- The installed face at the exact post-root visit. -/
def contributionCapacityPostSettlementEssentialAccessChannelFaceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :
    SourceNativeRootSemanticFaceAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index) :=
  M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot.contributionCapacityPostSettlementEssentialAccessChannelFaceAt
    oldVisit sourceIndex
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index) channel

/-- Authority is read from the installed root face, never reconstructed from
the protected-interest readout. -/
def contributionCapacityPostSettlementInstalledEssentialAccessChannelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :=
  contributionCapacityPostSettlementRootGeneratedEssentialAccessChannelAt
    oldVisit sourceIndex
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index) channel

def contributionCapacityPostSettlementEssentialAccessChannelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :
    SourceGeneratedContributionCapacityEssentialAccessChannelAt
      (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
        oldVisit sourceIndex index)
      channel
      (contributionCapacityPostSettlementEssentialAccessChannelActualExitAt
        oldVisit sourceIndex index) :=
  Classical.choice
    (contributionCapacityPostSettlementInstalledEssentialAccessChannelAt
      oldVisit sourceIndex index channel).down

/-- One root-installed channel occurrence.  Its only constructor is private;
all payload is regenerated through the exact root projection above. -/
inductive SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) : Type 21
  | private generated

def sourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :
    SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
      oldVisit sourceIndex index channel :=
  .generated

namespace SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  {channel : EssentialAccessChannel}
  (generated :
    SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
      oldVisit sourceIndex index channel)

theorem eq_generated :
    generated =
      sourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
        oldVisit sourceIndex index channel := by
  cases generated
  rfl

def macroFutureBirth :
    SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex index := by
  cases generated
  exact sourceGeneratedContributionCapacityPostSettlementFutureBirthAt
    oldVisit sourceIndex index

def postRootEvent := (macroFutureBirth generated).postRootEvent

def actualExit : PeriodicActualServiceExitAt
    (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
      oldVisit sourceIndex index) := by
  cases generated
  exact contributionCapacityPostSettlementEssentialAccessChannelActualExitAt
    oldVisit sourceIndex index

def postPayment := (macroFutureBirth generated).postPayment

def actualNext := (macroFutureBirth generated).nextPaidOccurrence

def installedFace := by
  cases generated
  exact contributionCapacityPostSettlementEssentialAccessChannelFaceAt
    oldVisit sourceIndex index channel

def installedAuthority := by
  cases generated
  exact contributionCapacityPostSettlementInstalledEssentialAccessChannelAt
    oldVisit sourceIndex index channel

def channelCarrier :
    SourceGeneratedContributionCapacityEssentialAccessChannelAt
      (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
        oldVisit sourceIndex index)
      channel (actualExit generated) := by
  cases generated
  exact contributionCapacityPostSettlementEssentialAccessChannelAt oldVisit
    sourceIndex index channel

def actor := channelActor channel

def relation := channelRelation channel

def phase := channelPhase channel

def targetRole := channelTargetRole channel

def relationInterest := (channelCarrier generated).relationInterest

def targetRoleGenerated := (channelCarrier generated).targetRoleGenerated

def paymentReceipt := (channelCarrier generated).paymentReceipt

def routeReceipt := (channelCarrier generated).routeReceipt

def serviceReceipt := (channelCarrier generated).serviceReceipt

def rootConsumer := (channelCarrier generated).rootConsumer

def rootFactorization := (channelCarrier generated).rootFactorization

def witnessReturn := (channelCarrier generated).witnessReturn

theorem channelCarrierPayment_exact :
    (channelCarrier generated).existingPaymentOccurrence =
      (actualExit generated).paymentOccurrence :=
  (channelCarrier generated).paymentOccurrence_eq_input

theorem channelCarrierSettlement_exact :
    (channelCarrier generated).existingActualSettlement =
      (actualExit generated).actualSettlement :=
  (channelCarrier generated).actualSettlement_eq_input

theorem channelCarrierPostPayment_exact :
    (channelCarrier generated).existingPaymentOccurrence =
      (Classical.choice (postPayment generated).write.down).paymentOccurrence := by
  rw [channelCarrierPayment_exact]
  exact congrArg PeriodicActualServiceExitAt.paymentOccurrence
    (macroFutureBirth generated).actualExitFromNativeWrite_exact

theorem paymentRootOccurrence_exact :
    (actualExit generated).paymentOccurrence.rootOccurrence =
      M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (temporalVisitAt
          (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
            oldVisit sourceIndex index)) :=
  (channelCarrier generated).paymentRootOccurrenceExact

theorem relationWitness_returns_exactSource :
    (witnessReturn generated).1.actor essentialAccessRelationCompiler =
        channelActor channel ∧
      essentialAccessRelationCompiler.relationOf (witnessReturn generated).1 =
        channelRelation channel :=
  (channelCarrier generated).witnessReturn_exact

/-- Channel consumption returns to the payment compiler's actual next, not a
channel-local continuation table. -/
@[simp] theorem actualNext_exact :
    actualNext generated =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
            oldVisit sourceIndex index +
          1) :=
  (macroFutureBirth generated).nextPaidOccurrence_exact

theorem postPaymentNext_eq_actualNext :
    (postPayment generated).nextPaidBy = actualNext generated :=
  rfl

theorem rootOccurrence_matchesPostRootEvent :
    (postRootEvent generated).occurrence =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
          oldVisit sourceIndex index) :=
  rfl

end SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt

theorem contributionCapacityPostSettlementEssentialAccessChannel_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) : True := by
  let generated :=
    sourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
      oldVisit sourceIndex index channel
  fail_if_success exact generated.participant
  fail_if_success exact generated.label
  fail_if_success exact generated.registry
  fail_if_success exact generated.schedule
  fail_if_success exact generated.future
  fail_if_success exact generated.next
  trivial

end
end M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel.sourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel.SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt.actualNext_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel.SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt.relationWitness_returns_exactSource
