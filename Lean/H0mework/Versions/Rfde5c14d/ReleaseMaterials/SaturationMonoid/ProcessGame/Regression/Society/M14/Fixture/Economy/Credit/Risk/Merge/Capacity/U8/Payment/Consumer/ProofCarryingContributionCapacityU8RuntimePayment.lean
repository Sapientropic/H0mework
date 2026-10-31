import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Payment.Producer.SourceGeneratedContributionCapacityU8RuntimePayment
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime

/-!
# Direct consumer of U8-root runtime payment

Runtime depth four is no longer a `Unit`-paid inquiry continuation.  Its exact
U8 current-two event generates the global depth-four actual-service write,
complete Fin-3 disposition and same-root successor.  Depth five reads a fresh
current-three payment event before generating the cross-root reopening action;
that macro action remains a separate authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityU8RuntimePayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityU8RuntimePayment
open M14SourceGeneratedSequentialContributionCapacityReopening

def contributionCapacityU8RuntimeNextPaidBy
    (oldVisit : OldVisit) (index : Nat) :=
  (contributionCapacityU8RuntimePaymentSuccessorAt oldVisit index
    ).targetOccurrence

@[simp] theorem contributionCapacityU8RuntimeNextPaidBy_exact
    (oldVisit : OldVisit) (index : Nat) :
    contributionCapacityU8RuntimeNextPaidBy oldVisit index =
      contributionCapacityU8Emitted oldVisit
        (contributionCapacityU8RuntimePaymentCurrentAt oldVisit index + 1) :=
  rfl

def contributionCapacityU8RuntimePaidOccurrenceAt
    (oldVisit : OldVisit) (index : Nat) :
    Sigma fun current : Nat =>
      (contributionCapacityU8Source oldVisit).toRootSource.actual.OccurrenceAt
        current :=
  ⟨contributionCapacityU8RuntimePaymentCurrentAt oldVisit index,
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index).occurrence⟩

theorem contributionCapacityU8RuntimePaidOccurrences_injective
    (oldVisit : OldVisit) :
    Function.Injective
      (contributionCapacityU8RuntimePaidOccurrenceAt oldVisit) := by
  intro left right occurrenceEquality
  have currentEquality := congrArg Sigma.fst occurrenceEquality
  change
    contributionCapacityU8RuntimePaymentCurrentAt oldVisit left =
      contributionCapacityU8RuntimePaymentCurrentAt oldVisit right at currentEquality
  rw [contributionCapacityU8RuntimePaymentCurrentAt_exact,
    contributionCapacityU8RuntimePaymentCurrentAt_exact] at currentEquality
  exact currentEquality

@[simp] theorem depthFour_U8PaymentRootEvent_exact :
    fifthTick.receipt.1 =
      contributionCapacityU8RuntimePaymentRootEventAt canonicalOldVisit 2 :=
  rfl

@[simp] theorem depthFive_U8PaidSourceEvent_exact :
    sixthTick.receipt.1 =
      contributionCapacityU8RuntimePaymentRootEventAt canonicalOldVisit 3 :=
  rfl

@[simp] theorem depthFour_resolution_is_directAnswer :
    fifthTick.resolution =
      .directlyAnswered
        (contributionCapacityU8AnswerFaceAt canonicalOldVisit 0)
        (contributionCapacityU8AnswerConsumerAt canonicalOldVisit 0) :=
  fifthTick_is_generated_selfU8_target_answer

@[simp] theorem depthFive_resolution_is_reopeningAction :
    sixthTick.resolution =
      .actualAction
        (generatedContributionCapacityReopeningActionAt canonicalOldVisit 1) :=
  sixthTick_resolution_is_contributionCapacityReopening

@[simp] theorem depthFour_runtimeNextEngine_exact :
    (jointRuntime.stateAt 5).engine = fifthTick.next :=
  rfl

theorem bareAnswerConsumer_orUnit_cannot_retype_asU8RuntimePayment : True := by
  fail_if_success
    exact (() : SourceGeneratedContributionCapacityU8RuntimePaymentAt
      canonicalOldVisit 2)
  fail_if_success
    exact (contributionCapacityU8AnswerConsumerAt canonicalOldVisit 0 :
      SourceGeneratedContributionCapacityU8RuntimePaymentAt canonicalOldVisit
        2)
  trivial

structure ProofCarryingContributionCapacityU8RuntimePayment : Prop where
  everyCurrentPaid : ∀ index : Nat,
    SourceGeneratedContributionCapacityU8RuntimePaymentAt canonicalOldVisit
      index
  paidOccurrencesInjective : Function.Injective
    (contributionCapacityU8RuntimePaidOccurrenceAt canonicalOldVisit)
  depthFourRootEventExact :
    fifthTick.receipt.1 =
      contributionCapacityU8RuntimePaymentRootEventAt canonicalOldVisit 2
  depthFivePaidSourceEventExact :
    sixthTick.receipt.1 =
      contributionCapacityU8RuntimePaymentRootEventAt canonicalOldVisit 3
  depthFourResolutionExact :
    fifthTick.resolution =
      .directlyAnswered
        (contributionCapacityU8AnswerFaceAt canonicalOldVisit 0)
        (contributionCapacityU8AnswerConsumerAt canonicalOldVisit 0)
  depthFiveActionExact :
    sixthTick.resolution =
      .actualAction
        (generatedContributionCapacityReopeningActionAt canonicalOldVisit 1)
  depthFourNextPaidByExact :
    contributionCapacityU8RuntimeNextPaidBy canonicalOldVisit 2 =
      contributionCapacityU8Emitted canonicalOldVisit
        (contributionCapacityU8RuntimePaymentCurrentAt canonicalOldVisit 2 + 1)
  depthFourPaymentDepthExact :
    contributionCapacityU8PaymentDepthAtCurrent 2 = 4
  depthFivePaymentDepthExact :
    contributionCapacityU8PaymentDepthAtCurrent 3 = 5

theorem proofCarryingContributionCapacityU8RuntimePayment :
    ProofCarryingContributionCapacityU8RuntimePayment where
  everyCurrentPaid :=
    sourceGeneratedContributionCapacityU8RuntimePaymentAt canonicalOldVisit
  paidOccurrencesInjective :=
    contributionCapacityU8RuntimePaidOccurrences_injective canonicalOldVisit
  depthFourRootEventExact := depthFour_U8PaymentRootEvent_exact
  depthFivePaidSourceEventExact := depthFive_U8PaidSourceEvent_exact
  depthFourResolutionExact := depthFour_resolution_is_directAnswer
  depthFiveActionExact := depthFive_resolution_is_reopeningAction
  depthFourNextPaidByExact :=
    contributionCapacityU8RuntimeNextPaidBy_exact canonicalOldVisit 2
  depthFourPaymentDepthExact :=
    contributionCapacityU8PaymentDepthAtCurrent_two
  depthFivePaymentDepthExact :=
    contributionCapacityU8PaymentDepthAtCurrent_three

end
end M14ProofCarryingContributionCapacityU8RuntimePayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityU8RuntimePayment.proofCarryingContributionCapacityU8RuntimePayment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityU8RuntimePayment.depthFour_U8PaymentRootEvent_exact
