import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Payment.Producer.SourceGeneratedContributionCapacityReopeningRuntimePayment

/-!
# Direct consumer of reopening runtime payment

Every positive reopening current has a compiler-native actual-service write,
complete Fin-3 row disposition and a compiler-generated same-root successor.
Depths six and seven consume that successor directly.  Depth eight exposes
the same paid source event but its cross-root settlement action remains a
separate authority and is not certified here as paid by the micro-successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityReopeningRuntimePayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningState
open M14SourceGeneratedContributionCapacityReopeningRuntimePayment
open M14SourceGeneratedSequentialContributionCapacitySettlement

def contributionCapacityReopeningRuntimePaymentSuccessorAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
        sourceIndex index).occurrence
      (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
        sourceIndex index).wholeLedgerWriteBack :=
  PUnit.unit

/-- `NextPaidBy` is read only from the source compiler image. -/
def contributionCapacityReopeningRuntimeNextPaidBy
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  (contributionCapacityReopeningRuntimePaymentSuccessorAt oldVisit sourceIndex
    index).targetOccurrence

@[simp] theorem contributionCapacityReopeningRuntimeNextPaidBy_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    contributionCapacityReopeningRuntimeNextPaidBy oldVisit sourceIndex index =
      contributionCapacityReopeningEmitted oldVisit sourceIndex
        (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
          oldVisit sourceIndex)
        (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
          sourceIndex index + 1) :=
  rfl

/-- Existing dependent occurrence family, used only to prove no replay across
positive currents. -/
def contributionCapacityReopeningRuntimePaidOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Sigma fun current : Nat =>
      (contributionCapacityReopeningSource oldVisit sourceIndex
        (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
          oldVisit sourceIndex)
        ).toRootSource.actual.OccurrenceAt current :=
  ⟨contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit sourceIndex
      index,
    (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit sourceIndex
      index).occurrence⟩

theorem contributionCapacityReopeningRuntimePaidOccurrences_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (contributionCapacityReopeningRuntimePaidOccurrenceAt oldVisit
        sourceIndex) := by
  intro left right occurrenceEquality
  have currentEquality := congrArg Sigma.fst occurrenceEquality
  change
    contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit sourceIndex
        left =
      contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit sourceIndex
        right at currentEquality
  rw [contributionCapacityReopeningRuntimePaymentCurrentAt_exact,
    contributionCapacityReopeningRuntimePaymentCurrentAt_exact] at currentEquality
  omega

set_option linter.unusedVariables false in
theorem bareUnit_cannot_retype_asReopeningRuntimePayment
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  fail_if_success
    exact (() : SourceGeneratedContributionCapacityReopeningRuntimePaymentAt
      oldVisit sourceIndex index)
  trivial

structure ProofCarryingContributionCapacityReopeningRuntimePaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  everyPositivePayment : ∀ index : Nat,
    SourceGeneratedContributionCapacityReopeningRuntimePaymentAt oldVisit
      sourceIndex index
  everyWholeLedgerSuccessor : ∀ index : Nat,
    Nonempty
      (SourceNativeLedgerGeneratedSuccessorAt
        (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
          sourceIndex index).occurrence
        (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
          sourceIndex index).wholeLedgerWriteBack)
  everyNextPaidByExact : ∀ index : Nat,
    contributionCapacityReopeningRuntimeNextPaidBy oldVisit sourceIndex index =
      contributionCapacityReopeningEmitted oldVisit sourceIndex
        (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
          oldVisit sourceIndex)
        (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
          sourceIndex index + 1)
  paidOccurrencesInjective : Function.Injective
    (contributionCapacityReopeningRuntimePaidOccurrenceAt oldVisit sourceIndex)

theorem proofCarryingContributionCapacityReopeningRuntimePayment
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityReopeningRuntimePaymentAt oldVisit
      sourceIndex where
  everyPositivePayment :=
    sourceGeneratedContributionCapacityReopeningRuntimePaymentAt oldVisit
      sourceIndex
  everyWholeLedgerSuccessor := fun index =>
    ⟨contributionCapacityReopeningRuntimePaymentSuccessorAt oldVisit sourceIndex
      index⟩
  everyNextPaidByExact :=
    contributionCapacityReopeningRuntimeNextPaidBy_exact oldVisit sourceIndex
  paidOccurrencesInjective :=
    contributionCapacityReopeningRuntimePaidOccurrences_injective oldVisit
      sourceIndex

structure CanonicalContributionCapacityReopeningRuntimePaymentCertificate :
    Prop where
  wholePositiveHistory :
    ProofCarryingContributionCapacityReopeningRuntimePaymentAt canonicalOldVisit
      1
  depthSixRootEventExact :
    seventhTick.receipt.1 =
      contributionCapacityReopeningRuntimePaymentRootEventAt canonicalOldVisit
        1 0
  depthSevenRootEventExact :
    eighthTick.receipt.1 =
      contributionCapacityReopeningRuntimePaymentRootEventAt canonicalOldVisit
        1 1
  depthEightPaidSourceEventExact :
    ninthTick.receipt.1 =
      contributionCapacityReopeningRuntimePaymentRootEventAt canonicalOldVisit
        1 2
  depthSixAnswerExact :
    seventhTick.resolution =
      .directlyAnswered
        (contributionCapacityReopenedAnswerFaceAt canonicalOldVisit 1 0)
        (contributionCapacityReopenedAnswerConsumerAt canonicalOldVisit 1 0)
  depthSevenAnswerExact :
    eighthTick.resolution =
      .directlyAnswered
        (contributionCapacityReopenedAnswerFaceAt canonicalOldVisit 1 1)
        (contributionCapacityReopenedAnswerConsumerAt canonicalOldVisit 1 1)
  depthEightActionExact :
    ninthTick.resolution =
      .actualAction
        (generatedContributionCapacitySettlementActionAt canonicalOldVisit 1)

theorem canonicalContributionCapacityReopeningRuntimePaymentCertificate :
    CanonicalContributionCapacityReopeningRuntimePaymentCertificate where
  wholePositiveHistory :=
    proofCarryingContributionCapacityReopeningRuntimePayment canonicalOldVisit 1
  depthSixRootEventExact :=
    canonicalRuntimeDepthSix_reopeningPaymentRootEvent_exact
  depthSevenRootEventExact :=
    canonicalRuntimeDepthSeven_reopeningPaymentRootEvent_exact
  depthEightPaidSourceEventExact :=
    canonicalRuntimeDepthEight_reopeningPaymentRootEvent_exact
  depthSixAnswerExact := seventhTick_is_generated_reopening_target_answer
  depthSevenAnswerExact :=
    eighthTick_is_next_generated_reopening_target_answer
  depthEightActionExact :=
    ninthTick_resolution_is_contributionCapacitySettlement

end
end M14ProofCarryingContributionCapacityReopeningRuntimePayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityReopeningRuntimePayment.proofCarryingContributionCapacityReopeningRuntimePayment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityReopeningRuntimePayment.canonicalContributionCapacityReopeningRuntimePaymentCertificate
