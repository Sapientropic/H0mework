import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Consumer.SourceGeneratedContributionCapacityJointSettlementConsumer

/-!
# Source-generated survivor runtime payment

The canonical survivor root writes two carried debt rows at every reachable
current.  Its native write is now indexed by the actual-service witness carried
by that same emitted event.  This module exposes the exact event, write and
complete row dispositions used by runtime depths 10--12.  It introduces no
payment registry, successor, target, action, terminal receipt or debt-settlement
claim.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySettlementSurvivorRuntimePayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementActionSource
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorRoot
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedContributionCapacityJointSettlementConsumer

abbrev CanonicalSettlementSourceEvent :=
  CanonicalContributionCapacitySettlementSourceEventAt canonicalOldVisit 1

abbrev CanonicalSettlementSurvivorRoot :=
  CanonicalContributionCapacitySettlementSurvivorRootAt canonicalOldVisit 1

abbrev CanonicalSettlementSurvivorCompiler :=
  contributionCapacitySettlementSurvivorLedgerCompiler canonicalOldVisit 1
    CanonicalSettlementSourceEvent

def contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt
    (index : Nat) : Nat :=
  show Nat from
    (contributionCapacitySettlementSurvivorVisitAt canonicalOldVisit 1
      index).current

@[simp] theorem contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt_exact
    (index : Nat) :
    contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt index =
      10 + index := by
  unfold contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt
  simpa only [contributionCapacitySettlementSurvivorInitialCurrentAt_one] using
    (contributionCapacitySettlementSurvivorVisit_current_exact canonicalOldVisit
      1 index)

def contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt
    (index : Nat) :
    ExactTemporalCausalRootEventAt
      CanonicalSettlementSurvivorRoot.toAuthoritativeRoot.toLedgerRoot
      (contributionCapacitySettlementSurvivorVisitAt canonicalOldVisit 1
        index) :=
  CanonicalSettlementSurvivorRoot.toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt
      (contributionCapacitySettlementSurvivorVisitAt canonicalOldVisit 1 index)

@[simp] theorem contributionCapacitySettlementSurvivorRuntimePaymentRootEvent_occurrence_exact
    (index : Nat) :
    (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
      ).occurrence =
      contributionCapacitySettlementSurvivorEmitted canonicalOldVisit 1
        CanonicalSettlementSourceEvent
        (contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt index) :=
  rfl

/-- Payment is extracted from the exact root event.  It is not reconstructed
from `periodicActualServiceExitAt` or from a numerical current alone. -/
def contributionCapacitySettlementSurvivorRuntimePaymentAt
    (index : Nat) :
    ContributionCapacitySettlementSurvivorExactWholeLedgerPaymentAt
      (contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt index) :=
  PLift.up
    (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
      ).occurrence.2.periodicExitGenerated

def contributionCapacitySettlementSurvivorRuntimePaymentRowEvolutionAt
    (index : Nat) (entryIndex : Fin 2) :=
  (contributionCapacitySettlementSurvivorEvolution canonicalOldVisit 1
    CanonicalSettlementSourceEvent
    (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
      ).occurrence).destination
        (contributionCapacitySettlementSurvivorEntryAt canonicalOldVisit
          entryIndex) |>.2

theorem contributionCapacitySettlementSurvivorRuntimePaymentCompiler_nativeWrite_exact
    (index : Nat) :
    CanonicalSettlementSurvivorCompiler.compile
        (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
          ).occurrence =
      .nativeWrite
        (contributionCapacitySettlementSurvivorRuntimePaymentAt index) rfl
        (contributionCapacitySettlementSurvivorEmitted canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt index +
            1))
        (contributionCapacitySettlementSurvivorEvolution canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
            ).occurrence) :=
  rfl

theorem contributionCapacitySettlementSurvivorRuntimePaymentRootReceipt_nativeWrite_exact
    (index : Nat) :
    (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
      ).wholeLedgerWriteBack =
      .nativeWrite
        (contributionCapacitySettlementSurvivorRuntimePaymentAt index) rfl
        (contributionCapacitySettlementSurvivorEmitted canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt index +
            1))
        (contributionCapacitySettlementSurvivorEvolution canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
            ).occurrence) :=
  contributionCapacitySettlementSurvivorRuntimePaymentCompiler_nativeWrite_exact
    index

/-- All two live rows are evolved by the same event that generated the payment
write.  In particular the payment write does not terminally settle either old
debt. -/
theorem contributionCapacitySettlementSurvivorRuntimePayment_everyRow_evolved
    (index : Nat) (entryIndex : Fin 2) :
    (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacitySettlementSurvivorEntryAt canonicalOldVisit
          entryIndex) =
      .evolved
        (contributionCapacitySettlementSurvivorRuntimePaymentRowEvolutionAt
          index entryIndex) :=
  by
    rw [contributionCapacitySettlementSurvivorRuntimePaymentRootReceipt_nativeWrite_exact]
    rfl

structure SourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt
    (index : Nat) : Prop where
  private mk ::
  currentExact :
    contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt index =
      10 + index
  rootReceiptNativeWriteExact :
    (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
      ).wholeLedgerWriteBack =
      CanonicalSettlementSurvivorCompiler.compile
        (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
          ).occurrence
  compilerNativeWriteExact :
    CanonicalSettlementSurvivorCompiler.compile
        (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
          ).occurrence =
      .nativeWrite
        (contributionCapacitySettlementSurvivorRuntimePaymentAt index) rfl
        (contributionCapacitySettlementSurvivorEmitted canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt index +
            1))
        (contributionCapacitySettlementSurvivorEvolution canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
            ).occurrence)
  everyRowEvolved : ∀ entryIndex : Fin 2,
    (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacitySettlementSurvivorEntryAt canonicalOldVisit
          entryIndex) =
      .evolved
        (contributionCapacitySettlementSurvivorRuntimePaymentRowEvolutionAt
          index entryIndex)

theorem sourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt
    (index : Nat) :
    SourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt
      index where
  currentExact :=
    contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt_exact index
  rootReceiptNativeWriteExact := rfl
  compilerNativeWriteExact :=
    contributionCapacitySettlementSurvivorRuntimePaymentCompiler_nativeWrite_exact
      index
  everyRowEvolved :=
    contributionCapacitySettlementSurvivorRuntimePayment_everyRow_evolved index

@[simp] theorem contributionCapacitySettlementSurvivorRuntimeDepthTen_rootEvent_exact :
    eleventhTick.receipt.1 =
      contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt 0 :=
  rfl

@[simp] theorem contributionCapacitySettlementSurvivorRuntimeDepthEleven_rootEvent_exact :
    twelfthTick.receipt.1 =
      contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt 1 :=
  rfl

@[simp] theorem contributionCapacitySettlementSurvivorRuntimeDepthTwelve_rootEvent_exact :
    canonicalContributionCapacityJointSettlementSearchTick.receipt.1 =
      contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt 2 :=
  rfl

theorem contributionCapacitySettlementSurvivorRuntimePayment_hasNoNextOrTarget
    (index : Nat) : True := by
  let payment :=
    contributionCapacitySettlementSurvivorRuntimePaymentAt index
  fail_if_success exact payment.next
  fail_if_success exact payment.target
  fail_if_success exact payment.future
  trivial

end
end M14SourceGeneratedContributionCapacitySettlementSurvivorRuntimePayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorRuntimePayment.sourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorRuntimePayment.contributionCapacitySettlementSurvivorRuntimeDepthTwelve_rootEvent_exact
