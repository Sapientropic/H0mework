import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Runtime.Payment.Producer.SourceGeneratedContributionCapacitySettlementSurvivorRuntimePayment

/-!
# Direct consumer of survivor runtime payment

Runtime depths 10--12 are ordinary survivor answers.  Each exact tick reads a
native write paid by its own current-indexed actual-service witness while the
two old debt rows remain evolved, not terminally settled.  Runtime next is read
only from the existing answer-and-next and sealed tick successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacitySettlementSurvivorRuntimePayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityJointSettlementState
open M14SourceGeneratedContributionCapacitySettlementSurvivorRuntimePayment

def contributionCapacitySettlementSurvivorRuntimeDepthTenAnswerAndNext :=
  eleventhTick.receipt.2.2

def contributionCapacitySettlementSurvivorRuntimeDepthElevenAnswerAndNext :=
  twelfthTick.receipt.2.2

def contributionCapacitySettlementSurvivorRuntimeDepthTwelveAnswerAndNext :=
  canonicalContributionCapacityJointSettlementSearchTick.receipt.2.2

@[simp] theorem contributionCapacitySettlementSurvivorRuntimeDepthTen_nextState_exact :
    (jointRuntime.stateAt 11).engine = eleventhTick.next :=
  rfl

@[simp] theorem contributionCapacitySettlementSurvivorRuntimeDepthEleven_nextState_exact :
    (jointRuntime.stateAt 12).engine = twelfthTick.next :=
  rfl

@[simp] theorem contributionCapacitySettlementSurvivorRuntimeDepthTwelve_nextState_exact :
    (jointRuntime.stateAt 13).engine =
      canonicalContributionCapacityJointSettlementSearchTick.next :=
  rfl

theorem contributionCapacitySettlementSurvivorRuntimeDepthTen_answerAndNext_exact :
    contributionCapacitySettlementSurvivorRuntimeDepthTenAnswerAndNext.nextCurrent =
      CanonicalSettlementSurvivorRoot.generatedNextCurrentAt
        (contributionCapacitySettlementSurvivorVisitAt canonicalOldVisit 1 0) :=
  SourceNativeLivingCausalEntryAnswerAndNextAt.nextCurrent_eq _

theorem contributionCapacitySettlementSurvivorRuntimeDepthEleven_answerAndNext_exact :
    contributionCapacitySettlementSurvivorRuntimeDepthElevenAnswerAndNext.nextCurrent =
      CanonicalSettlementSurvivorRoot.generatedNextCurrentAt
        (contributionCapacitySettlementSurvivorVisitAt canonicalOldVisit 1 1) :=
  SourceNativeLivingCausalEntryAnswerAndNextAt.nextCurrent_eq _

theorem contributionCapacitySettlementSurvivorRuntimeDepthTwelve_answerAndNext_exact :
    contributionCapacitySettlementSurvivorRuntimeDepthTwelveAnswerAndNext.nextCurrent =
      CanonicalSettlementSurvivorRoot.generatedNextCurrentAt
        (contributionCapacitySettlementSurvivorVisitAt canonicalOldVisit 1 2) :=
  SourceNativeLivingCausalEntryAnswerAndNextAt.nextCurrent_eq _

set_option linter.defProp false in
def contributionCapacitySettlementSurvivorRuntimeDepthTen_next_erasesToGenerated :=
  eleventhTick.next_erases_to_generated

set_option linter.defProp false in
def contributionCapacitySettlementSurvivorRuntimeDepthEleven_next_erasesToGenerated :=
  twelfthTick.next_erases_to_generated

set_option linter.defProp false in
def contributionCapacitySettlementSurvivorRuntimeDepthTwelve_next_erasesToGenerated :=
  canonicalContributionCapacityJointSettlementSearchTick.next_erases_to_generated

theorem contributionCapacitySettlementSurvivorRuntimeDepthTen_rootReceipt_exact :
    eleventhTick.receipt.1.wholeLedgerWriteBack =
      CanonicalSettlementSurvivorCompiler.compile
        (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt 0
          ).occurrence := by
  rw [contributionCapacitySettlementSurvivorRuntimeDepthTen_rootEvent_exact]
  rfl

theorem contributionCapacitySettlementSurvivorRuntimeDepthEleven_rootReceipt_exact :
    twelfthTick.receipt.1.wholeLedgerWriteBack =
      CanonicalSettlementSurvivorCompiler.compile
        (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt 1
          ).occurrence := by
  rw [contributionCapacitySettlementSurvivorRuntimeDepthEleven_rootEvent_exact]
  rfl

theorem contributionCapacitySettlementSurvivorRuntimeDepthTwelve_rootReceipt_exact :
    canonicalContributionCapacityJointSettlementSearchTick.receipt.1.wholeLedgerWriteBack =
      CanonicalSettlementSurvivorCompiler.compile
        (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt 2
          ).occurrence := by
  rw [contributionCapacitySettlementSurvivorRuntimeDepthTwelve_rootEvent_exact]
  rfl

theorem contributionCapacitySettlementSurvivorRuntimeDepthTen_nativeWrite_exact :
    eleventhTick.receipt.1.wholeLedgerWriteBack =
      .nativeWrite
        (contributionCapacitySettlementSurvivorRuntimePaymentAt 0) rfl
        (contributionCapacitySettlementSurvivorEmitted canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt 0 + 1))
        (contributionCapacitySettlementSurvivorEvolution canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt 0
            ).occurrence) := by
  rw [contributionCapacitySettlementSurvivorRuntimeDepthTen_rootEvent_exact]
  exact
    contributionCapacitySettlementSurvivorRuntimePaymentRootReceipt_nativeWrite_exact
      0

theorem contributionCapacitySettlementSurvivorRuntimeDepthEleven_nativeWrite_exact :
    twelfthTick.receipt.1.wholeLedgerWriteBack =
      .nativeWrite
        (contributionCapacitySettlementSurvivorRuntimePaymentAt 1) rfl
        (contributionCapacitySettlementSurvivorEmitted canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt 1 + 1))
        (contributionCapacitySettlementSurvivorEvolution canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt 1
            ).occurrence) := by
  rw [contributionCapacitySettlementSurvivorRuntimeDepthEleven_rootEvent_exact]
  exact
    contributionCapacitySettlementSurvivorRuntimePaymentRootReceipt_nativeWrite_exact
      1

theorem contributionCapacitySettlementSurvivorRuntimeDepthTwelve_nativeWrite_exact :
    canonicalContributionCapacityJointSettlementSearchTick.receipt.1.wholeLedgerWriteBack =
      .nativeWrite
        (contributionCapacitySettlementSurvivorRuntimePaymentAt 2) rfl
        (contributionCapacitySettlementSurvivorEmitted canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt 2 + 1))
        (contributionCapacitySettlementSurvivorEvolution canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt 2
            ).occurrence) := by
  rw [contributionCapacitySettlementSurvivorRuntimeDepthTwelve_rootEvent_exact]
  exact
    contributionCapacitySettlementSurvivorRuntimePaymentRootReceipt_nativeWrite_exact
      2

/-- An evolved disposition is the exact negative control required here: the
actual-service payment authorizes continuation but does not terminally pay an
old survivor debt. -/
theorem contributionCapacitySettlementSurvivorRuntimeEveryRow_notTerminal
    (index : Nat) (entryIndex : Fin 2) :
    (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacitySettlementSurvivorEntryAt canonicalOldVisit
          entryIndex) =
      .evolved
        (contributionCapacitySettlementSurvivorRuntimePaymentRowEvolutionAt
          index entryIndex) :=
  contributionCapacitySettlementSurvivorRuntimePayment_everyRow_evolved index
    entryIndex

structure ProofCarryingContributionCapacitySettlementSurvivorRuntimePayment :
    Prop where
  depthTenPayment :
    SourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt 0
  depthElevenPayment :
    SourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt 1
  depthTwelvePayment :
    SourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt 2
  depthTenNativeWriteExact :
    eleventhTick.receipt.1.wholeLedgerWriteBack =
      .nativeWrite
        (contributionCapacitySettlementSurvivorRuntimePaymentAt 0) rfl
        (contributionCapacitySettlementSurvivorEmitted canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt 0 + 1))
        (contributionCapacitySettlementSurvivorEvolution canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt 0
            ).occurrence)
  depthElevenNativeWriteExact :
    twelfthTick.receipt.1.wholeLedgerWriteBack =
      .nativeWrite
        (contributionCapacitySettlementSurvivorRuntimePaymentAt 1) rfl
        (contributionCapacitySettlementSurvivorEmitted canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt 1 + 1))
        (contributionCapacitySettlementSurvivorEvolution canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt 1
            ).occurrence)
  depthTwelveNativeWriteExact :
    canonicalContributionCapacityJointSettlementSearchTick.receipt.1.wholeLedgerWriteBack =
      .nativeWrite
        (contributionCapacitySettlementSurvivorRuntimePaymentAt 2) rfl
        (contributionCapacitySettlementSurvivorEmitted canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentCurrentAt 2 + 1))
        (contributionCapacitySettlementSurvivorEvolution canonicalOldVisit 1
          CanonicalSettlementSourceEvent
          (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt 2
            ).occurrence)
  everyOldDebtRemainsEvolved : ∀ index : Fin 3, ∀ entryIndex : Fin 2,
    (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index.val
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacitySettlementSurvivorEntryAt canonicalOldVisit
          entryIndex) =
      .evolved
        (contributionCapacitySettlementSurvivorRuntimePaymentRowEvolutionAt
          index.val entryIndex)
  depthTwelveIsSearch :
    canonicalContributionCapacityJointSettlementSearchTick.resolution =
      .directlyAnswered
        (contributionCapacitySettlementSurvivorAnswerFaceAt canonicalOldVisit
          1 2)
        (contributionCapacitySettlementSurvivorAnswerConsumerAt
          canonicalOldVisit 1 2)
  depthTwelveSearchIsNotJointAction :
    (contributionCapacityJointSettlementActionStateAt canonicalOldVisit 1
      ).compileInquiry () ≠
      (contributionCapacitySettlementSurvivorStateAt canonicalOldVisit 1 2
        ).compileInquiry ()
  paymentsAreExactEventWitnesses : ∀ index : Fin 3,
    contributionCapacitySettlementSurvivorRuntimePaymentAt index.val =
      PLift.up
        (contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt
          index.val).occurrence.2.periodicExitGenerated

theorem proofCarryingContributionCapacitySettlementSurvivorRuntimePayment :
    ProofCarryingContributionCapacitySettlementSurvivorRuntimePayment where
  depthTenPayment :=
    sourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt 0
  depthElevenPayment :=
    sourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt 1
  depthTwelvePayment :=
    sourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt 2
  depthTenNativeWriteExact :=
    contributionCapacitySettlementSurvivorRuntimeDepthTen_nativeWrite_exact
  depthElevenNativeWriteExact :=
    contributionCapacitySettlementSurvivorRuntimeDepthEleven_nativeWrite_exact
  depthTwelveNativeWriteExact :=
    contributionCapacitySettlementSurvivorRuntimeDepthTwelve_nativeWrite_exact
  everyOldDebtRemainsEvolved := fun index entryIndex =>
    contributionCapacitySettlementSurvivorRuntimeEveryRow_notTerminal index.val
      entryIndex
  depthTwelveIsSearch :=
    canonicalContributionCapacityJointSettlementSearchTick_exact
  depthTwelveSearchIsNotJointAction :=
    jointSettlementActualPlay_search_compilations_distinct canonicalOldVisit 1
  paymentsAreExactEventWitnesses := fun _ => rfl

end
end M14ProofCarryingContributionCapacitySettlementSurvivorRuntimePayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacitySettlementSurvivorRuntimePayment.proofCarryingContributionCapacitySettlementSurvivorRuntimePayment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacitySettlementSurvivorRuntimePayment.contributionCapacitySettlementSurvivorRuntimeDepthTwelve_next_erasesToGenerated
