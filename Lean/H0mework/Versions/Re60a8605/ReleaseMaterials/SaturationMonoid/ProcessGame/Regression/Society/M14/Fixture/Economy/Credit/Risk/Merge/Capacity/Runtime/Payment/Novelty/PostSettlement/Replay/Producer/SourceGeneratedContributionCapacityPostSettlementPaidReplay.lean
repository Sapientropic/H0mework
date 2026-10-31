import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Celebration.Pulse.Producer.SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Preservation.PostSettlement.Step.Consumer.ProofCarryingContributionCapacityPostSettlementCanonicalPaidStep

/-!
# Source-generated post-settlement paid replay

One exact post-root index regenerates its actual future-birth occurrence,
native Payment, consumed canonical paid step, every installed channel and the
singleton finite-frontier pulse.  The replay is a zero-field token: it accepts
no path, normal form, authority value, coverage witness or future table.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityPostSettlementPaidReplay

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityFutureBirthPulse
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep
open M14ProofCarryingContributionCapacityPostSettlementCanonicalPaidStep

/-- One exact paid path through the already installed post-root runtime. -/
inductive SourceGeneratedContributionCapacityPostSettlementPaidReplayAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 26
  | private generated

/-- Sole producer.  The exact temporal index is the only varying input. -/
def sourceGeneratedContributionCapacityPostSettlementPaidReplayAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedContributionCapacityPostSettlementPaidReplayAt oldVisit
      sourceIndex index :=
  .generated

namespace SourceGeneratedContributionCapacityPostSettlementPaidReplayAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (replay : SourceGeneratedContributionCapacityPostSettlementPaidReplayAt
    oldVisit sourceIndex index)

theorem eq_generated :
    replay =
      sourceGeneratedContributionCapacityPostSettlementPaidReplayAt oldVisit
        sourceIndex index := by
  cases replay
  rfl

def current : Nat := by
  cases replay
  exact contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
    sourceIndex index

def futureBirth :
    SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex index := by
  cases replay
  exact sourceGeneratedContributionCapacityPostSettlementFutureBirthAt
    oldVisit sourceIndex index

/-- The complete actual path occurrence, not a branch tag or naked index. -/
def actualPath :
    AnyContributionCapacityPostSettlementFutureBirth oldVisit sourceIndex :=
  ⟨index, futureBirth replay⟩

def rootEvent := (futureBirth replay).postRootEvent

def payment :
    CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex index :=
  (futureBirth replay).postPayment

/-- The exact rich Payment is consumed by the canonical paid-step invariant. -/
def paidStep :
    ConsumedContributionCapacityPostSettlementCanonicalPaidStepAt oldVisit
      sourceIndex index (payment replay) :=
  proofCarryingContributionCapacityPostSettlementCanonicalPaidStepAt oldVisit
    sourceIndex index (payment replay)

/-- Each existing relation-generated channel is independently consumed at
this same replay occurrence. -/
def channel (channelKind : EssentialAccessChannel) :
    ConsumedContributionCapacityPostSettlementChannelAt oldVisit sourceIndex
      index channelKind := by
  cases replay
  exact proofCarryingContributionCapacityPostSettlementChannelAt oldVisit
    sourceIndex index channelKind

def witnessReturn (channelKind : EssentialAccessChannel) :=
  ((SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.channel
      replay channelKind).2.relationWitnessReturn)

/-- Real finite-frontier readout at this replay, specialized to one actual
occurrence. -/
def singletonPulse : ContributionCapacityFutureBirthPulse :=
  by
    cases replay
    exact sourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
      oldVisit sourceIndex index 1

/-- Responsibility-relevant authority of this actual service occurrence. -/
def authorityK : AnyPeriodicActualServiceExit :=
  by
    cases replay
    exact periodicActualServiceExitOccurrenceAt
      (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
        sourceIndex index)

def nextPaidBy := (payment replay).nextPaidBy

@[simp] theorem current_exact :
    SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.current
        replay =
      contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex +
        index :=
  M14SourceGeneratedContributionCapacityPostSettlementFutureBirth.SourceGeneratedContributionCapacityPostSettlementFutureBirthAt.current_exact
    (oldVisit := oldVisit) (sourceIndex := sourceIndex) (index := index)

@[simp] theorem singletonPulse_eq_one :
    SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.singletonPulse
        replay = 1 := by
  cases replay
  exact contributionCapacityPostSettlementFutureBirthPulse_eq_horizon
    oldVisit sourceIndex index 1

theorem paidStep_consumes_exactPayment :
    (paidStep replay).2.sourcePayment = payment replay :=
  rfl

theorem actualAuthority_isFutureBirthActualExit :
    (futureBirth replay).actualExit =
      (SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.authorityK
        replay).2.actualExit :=
  periodicActualServiceExitAt_eq_canonical (futureBirth replay).actualExit

theorem channelPayment_exact (channelKind : EssentialAccessChannel) :
    (SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.channel
        replay channelKind).2.rootReadCarrier.existingPaymentOccurrence =
      (futureBirth replay).actualExit.paymentOccurrence :=
  (SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.channel replay
    channelKind).2.paymentOccurrence_exact

theorem channelSettlement_exact (channelKind : EssentialAccessChannel) :
    (SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.channel
        replay channelKind).2.rootReadCarrier.existingActualSettlement =
      (futureBirth replay).actualExit.actualSettlement :=
  (SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.channel replay
    channelKind).2.actualSettlement_exact

theorem channelWitnessReturnsToSource (channelKind : EssentialAccessChannel) :
    (SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.witnessReturn
        replay channelKind).1.actor
          M14EssentialAccessRelationFixture.essentialAccessRelationCompiler =
        channelActor channelKind ∧
      M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationOf
          (SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.witnessReturn
            replay channelKind).1 = channelRelation channelKind :=
  (SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.channel replay
    channelKind).2.relationWitnessReturn_exact

theorem paymentNext_isCanonicalTarget :
    HEq (payment replay).nextPaidBy
      (M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent.SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
        (paidStep replay).2.targetCurrent).occurrence :=
  (paidStep replay).2.paidNext_isTargetCanonicalOccurrence

end SourceGeneratedContributionCapacityPostSettlementPaidReplayAt

/-- Open dependent carrier of all actually generated paid replays. -/
abbrev AnyContributionCapacityPostSettlementPaidReplay
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  Sigma fun index : Nat =>
    SourceGeneratedContributionCapacityPostSettlementPaidReplayAt oldVisit
      sourceIndex index

def contributionCapacityPostSettlementPaidReplayAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex :=
  ⟨index,
    sourceGeneratedContributionCapacityPostSettlementPaidReplayAt oldVisit
      sourceIndex index⟩

@[simp] theorem contributionCapacityPostSettlementPaidReplayAt_actualPath_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        index).2.actualPath =
      contributionCapacityPostSettlementFutureBirthOccurrenceAt oldVisit
        sourceIndex index :=
  rfl

@[simp] theorem contributionCapacityPostSettlementPaidReplayAt_pulse_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        index).2.singletonPulse =
      sourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
        oldVisit sourceIndex index 1 :=
  rfl

@[simp] theorem contributionCapacityPostSettlementPaidReplayAt_authorityK_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        index).2.authorityK =
      periodicActualServiceExitOccurrenceAt
        (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
          sourceIndex index) :=
  rfl

theorem contributionCapacityPostSettlementPaidReplayAt_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex) := by
  intro left right equality
  exact congrArg Sigma.fst equality

theorem contributionCapacityPostSettlementPaidReplay_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let replay :=
    sourceGeneratedContributionCapacityPostSettlementPaidReplayAt oldVisit
      sourceIndex index
  fail_if_success exact replay.path
  fail_if_success exact replay.normalForm
  fail_if_success exact replay.authority
  fail_if_success exact replay.coverage
  fail_if_success exact replay.next
  fail_if_success exact replay.future
  fail_if_success exact replay.registry
  trivial

end
end M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementPaidReplay.sourceGeneratedContributionCapacityPostSettlementPaidReplayAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementPaidReplay.SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.paidStep_consumes_exactPayment
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementPaidReplay.SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.channelWitnessReturnsToSource
