import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Payment.Producer.SourceGeneratedContributionCapacityU8RuntimePayment
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.SourceGeneratedContributionCapacityU8Revision

/-!
# Payment-bearing U8 revision receipt

The rooted self-U8 branch is not renamed as an ordinary native payment.  Its
existing dependent revision receipt instead consumes two source-native U8
payments: current zero pays the literal revised-root first write, and current
one pays the answer-and-next that generates the macro landing at current two.
No new branch grammar or outcome sum is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityU8RevisionNoFreeReceipt

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open TypedSemanticWorldNetworkU8
open TypedSemanticWorldNetworkU8Lifecycle
open TypedSemanticWorldNetworkU8Recovery
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8Revision
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityU8RuntimePayment

abbrev ContributionCapacityU8CanonicalRevisionAt
    (oldVisit : OldVisit) :=
  (generatedContributionCapacityU8CoreAt oldVisit).revision

/-- Macro next read from the current-one payment successor, not stored in the
revision receipt. -/
def contributionCapacityU8RevisionNextPaidBy
    (oldVisit : OldVisit) :
    SourceNativeAuthoritativeRootCurrentAt (CapacityU8NAt oldVisit) :=
  ⟨CapacityU8VAt oldVisit,
    (CapacityU8RootAt oldVisit).toAuthoritativeRoot,
    (contributionCapacityU8TemporalVisitAt oldVisit 1).next
      (contributionCapacityU8RuntimePaymentSuccessorAt oldVisit 1).next_eq⟩

structure SourceGeneratedContributionCapacityU8RevisionNoFreeReceiptAt
    (oldVisit : OldVisit) : Prop where
  private mk ::
  firstWritePayment :
    SourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit 0
  answerAndNextPayment :
    SourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit 1
  initialOccurrenceExact :
    (ContributionCapacityU8CanonicalRevisionAt oldVisit).generate.initialRestructuringGenerated.occurrence =
      (contributionCapacityU8RuntimePaymentRootEventAt oldVisit 0).occurrence
  initialWholeLedgerWriteExact :
    (ContributionCapacityU8CanonicalRevisionAt oldVisit).generate.initialRestructuringGenerated.wholeLedgerWriteBack =
      (contributionCapacityU8RuntimePaymentRootEventAt oldVisit 0
        ).wholeLedgerWriteBack
  firstWriteSuccessorExact :
    (ContributionCapacityU8CanonicalRevisionAt oldVisit).generate.firstWrite =
      contributionCapacityU8RuntimePaymentSuccessorAt oldVisit 0
  oldAnswerVisitExact :
    (oldFirstWriteSuccessor
      (ContributionCapacityU8CanonicalRevisionAt oldVisit)).targetVisit =
      contributionCapacityU8TemporalVisitAt oldVisit 1
  newAnswerVisitExact :
    (newFirstWriteSuccessor
      (ContributionCapacityU8CanonicalRevisionAt oldVisit)).targetVisit =
      contributionCapacityU8TemporalVisitAt oldVisit 1
  macroNextPaidByExact :
    (generatedNewTargetAnswerAndNext
      (ContributionCapacityU8CanonicalRevisionAt oldVisit)).nextCurrent =
      contributionCapacityU8RevisionNextPaidBy oldVisit

theorem sourceGeneratedContributionCapacityU8RevisionNoFreeReceiptAt
    (oldVisit : OldVisit) :
    SourceGeneratedContributionCapacityU8RevisionNoFreeReceiptAt oldVisit where
  firstWritePayment :=
    sourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit 0
  answerAndNextPayment :=
    sourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit 1
  initialOccurrenceExact := rfl
  initialWholeLedgerWriteExact := rfl
  firstWriteSuccessorExact := rfl
  oldAnswerVisitExact := rfl
  newAnswerVisitExact := rfl
  macroNextPaidByExact := rfl

end
end M14SourceGeneratedContributionCapacityU8RevisionNoFreeReceipt
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8RevisionNoFreeReceipt.sourceGeneratedContributionCapacityU8RevisionNoFreeReceiptAt
