import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Action.SourceGeneratedContributionCapacityReopeningState
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Payment.Producer.SourceGeneratedContributionCapacityU8RuntimePayment

/-!
# Cross-root payment for the capacity-reopening action

The exact capacity-U8 source event, its action receipt and the action-generated
reopening root all carry an actual-service authority at the same dependent
global depth.  This module locks the source payment and receipt-selected actual
exit to the target current-zero native write and its complete first successor.
The paid next is not stored: it is read only from the action target's existing
macro answer-and-next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityReopeningActionPayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacityReopeningActionSource
open M14SourceGeneratedSequentialContributionCapacityReopening
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8RuntimePayment
open M14SourceGeneratedContributionCapacityU8TargetState
open M14UBIPeriodicActualServiceCapacity

abbrev CanonicalContributionCapacityReopeningActionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  generatedContributionCapacityReopeningActionAt oldVisit sourceIndex

/-- Exact current-zero event of the action-generated target root. -/
def contributionCapacityReopeningActionTargetRootEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ExactTemporalCausalRootEventAt
      (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
        ).target.targetRoot.toAuthoritativeRoot.toLedgerRoot
      (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
        ).target.targetInitialVisit :=
  (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
    ).target.targetRoot.toAuthoritativeRoot.toLedgerRoot
      |>.exactTemporalCausalEventAt
        (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
          ).target.targetInitialVisit

@[simp] theorem contributionCapacityReopeningActionTargetRootEvent_occurrence_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityReopeningActionTargetRootEventAt oldVisit sourceIndex
      ).occurrence =
      contributionCapacityReopeningEmitted oldVisit sourceIndex
        (contributionCapacityReopeningActionExactSourceEventAt oldVisit
          sourceIndex) 0 :=
  rfl

/-- The target write is extracted from the exact target event. -/
def contributionCapacityReopeningActionTargetWriteAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ContributionCapacityReopeningExactWholeLedgerPaymentAt sourceIndex 0 :=
  PLift.up
    (contributionCapacityReopeningActionTargetRootEventAt oldVisit sourceIndex
      ).occurrence.2.periodicExitGenerated

def contributionCapacityReopeningActionTargetRowEvolutionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 3) :=
  (contributionCapacityReopeningEvolution oldVisit sourceIndex
    (contributionCapacityReopeningActionExactSourceEventAt oldVisit sourceIndex)
    (contributionCapacityReopeningActionTargetRootEventAt oldVisit sourceIndex
      ).occurrence).destination
        (contributionCapacityReopeningCurrentEntryAt oldVisit 0 entryIndex) |>.2

theorem contributionCapacityReopeningActionTargetWholeLedger_nativeWrite_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityReopeningActionTargetRootEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack =
      .nativeWrite
        (contributionCapacityReopeningActionTargetWriteAt oldVisit sourceIndex)
        rfl
        (contributionCapacityReopeningEmitted oldVisit sourceIndex
          (contributionCapacityReopeningActionExactSourceEventAt oldVisit
            sourceIndex) 1)
        (contributionCapacityReopeningEvolution oldVisit sourceIndex
          (contributionCapacityReopeningActionExactSourceEventAt oldVisit
            sourceIndex)
          (contributionCapacityReopeningActionTargetRootEventAt oldVisit
            sourceIndex).occurrence) :=
  rfl

theorem contributionCapacityReopeningActionTargetEveryRow_evolved
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 3) :
    (contributionCapacityReopeningActionTargetRootEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityReopeningCurrentEntryAt oldVisit 0 entryIndex) =
      .evolved
        (contributionCapacityReopeningActionTargetRowEvolutionAt oldVisit
          sourceIndex entryIndex) := by
  rw [contributionCapacityReopeningActionTargetWholeLedger_nativeWrite_exact]
  rfl

theorem contributionCapacityReopeningActionSourcePaymentDepth_exact
    (sourceIndex : Nat) :
    contributionCapacityU8PaymentDepthAtCurrent (sourceIndex + 2) =
      contributionCapacityReopeningDepthAt sourceIndex := by
  unfold contributionCapacityU8PaymentDepthAtCurrent
  unfold contributionCapacityReopeningDepthAt
  omega

theorem contributionCapacityReopeningActionSourceRuntimePaymentDepth_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    contributionCapacityU8PaymentDepthAtCurrent
        (contributionCapacityU8RuntimePaymentCurrentAt oldVisit
          (sourceIndex + 2)) =
      contributionCapacityReopeningDepthAt sourceIndex := by
  rw [contributionCapacityU8RuntimePaymentCurrentAt_exact]
  exact contributionCapacityReopeningActionSourcePaymentDepth_exact sourceIndex

abbrev contributionCapacityReopeningActionSourceActualExitAuthorityAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceWrite : ContributionCapacityU8ExactWholeLedgerPaymentAt
      (contributionCapacityU8RuntimePaymentCurrentAt oldVisit
        (sourceIndex + 2))) :
    Nonempty (PeriodicActualServiceExitAt
      (contributionCapacityReopeningDepthAt sourceIndex)) :=
  Eq.mp
    (congrArg (fun depth => Nonempty (PeriodicActualServiceExitAt depth))
      (contributionCapacityReopeningActionSourceRuntimePaymentDepth_exact
        oldVisit sourceIndex))
    sourceWrite.down

/-- Private three-way cross-root seal.  Each `ActualExit` field is a genuine
`Type 16` witness selected from its own source-native authority.  Their
equalities therefore compare underlying actual-service values, not
proof-irrelevant `Nonempty` terms.  No next, target current, future table,
coverage input or second receipt is stored. -/
structure ContributionCapacityReopeningActionPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Type 18 where
  private mk ::
  sourceEvent : ExactTemporalCausalRootEventAt
    (CapacityU8RootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
    (contributionCapacityReopeningActionSourceVisitAt oldVisit sourceIndex)
  sourceEventExact : sourceEvent =
    contributionCapacityU8RuntimePaymentRootEventAt oldVisit (sourceIndex + 2)
  sourcePayment : SourceGeneratedContributionCapacityU8RuntimePaymentAt
    oldVisit (sourceIndex + 2)
  sourceWrite : ContributionCapacityU8ExactWholeLedgerPaymentAt
    (contributionCapacityU8RuntimePaymentCurrentAt oldVisit
      (sourceIndex + 2))
  sourceWriteExact : sourceWrite =
    contributionCapacityU8RuntimePaymentAt oldVisit (sourceIndex + 2)
  targetEvent : ExactTemporalCausalRootEventAt
    (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
      ).target.targetRoot.toAuthoritativeRoot.toLedgerRoot
    (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
      ).target.targetInitialVisit
  targetEventExact : targetEvent =
    contributionCapacityReopeningActionTargetRootEventAt oldVisit sourceIndex
  targetWrite : ContributionCapacityReopeningExactWholeLedgerPaymentAt
    sourceIndex 0
  targetWriteExact : targetWrite =
    PLift.up targetEvent.occurrence.2.periodicExitGenerated
  sourceActualExit : PeriodicActualServiceExitAt
    (contributionCapacityReopeningDepthAt sourceIndex)
  sourceActualExitChoiceExact : sourceActualExit =
    Classical.choice
      (contributionCapacityReopeningActionSourceActualExitAuthorityAt oldVisit
        sourceIndex sourceWrite)
  receiptActualExit : PeriodicActualServiceExitAt
    (contributionCapacityReopeningDepthAt sourceIndex)
  receiptActualExitChoiceExact : receiptActualExit =
    Classical.choice
      (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
        ).receipt.periodicActualExitGenerated
  targetActualExit : PeriodicActualServiceExitAt
    (contributionCapacityReopeningDepthAt sourceIndex)
  targetActualExitChoiceExact : targetActualExit =
    Classical.choice targetWrite.down
  sourceReceiptActualExitExact : sourceActualExit = receiptActualExit
  receiptTargetActualExitExact : receiptActualExit = targetActualExit
  targetWholeLedgerNativeWriteExact : targetEvent.wholeLedgerWriteBack =
    .nativeWrite targetWrite rfl
      (contributionCapacityReopeningEmitted oldVisit sourceIndex
        (contributionCapacityReopeningActionExactSourceEventAt oldVisit
          sourceIndex) 1)
      (contributionCapacityReopeningEvolution oldVisit sourceIndex
        (contributionCapacityReopeningActionExactSourceEventAt oldVisit
          sourceIndex) targetEvent.occurrence)
  everyTargetRowEvolved : ∀ entryIndex : Fin 3,
    targetEvent.wholeLedgerWriteBack.entryDisposition
        (contributionCapacityReopeningCurrentEntryAt oldVisit 0 entryIndex) =
      .evolved
        (contributionCapacityReopeningActionTargetRowEvolutionAt oldVisit
          sourceIndex entryIndex)
  firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    targetEvent.occurrence targetEvent.wholeLedgerWriteBack
  firstSuccessorExact : HEq firstSuccessor
    (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
      ).target.firstSuccessor

def sourceGeneratedContributionCapacityReopeningActionPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ContributionCapacityReopeningActionPaymentAt oldVisit sourceIndex := by
  let action :=
    CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
  let sourceEvent :=
    contributionCapacityU8RuntimePaymentRootEventAt oldVisit (sourceIndex + 2)
  let sourceWrite :=
    contributionCapacityU8RuntimePaymentAt oldVisit (sourceIndex + 2)
  let targetEvent :=
    contributionCapacityReopeningActionTargetRootEventAt oldVisit sourceIndex
  let targetWrite :=
    contributionCapacityReopeningActionTargetWriteAt oldVisit sourceIndex
  let sourceActualExit :=
    Classical.choice
      (contributionCapacityReopeningActionSourceActualExitAuthorityAt oldVisit
        sourceIndex sourceWrite)
  let receiptActualExit :=
    Classical.choice action.receipt.periodicActualExitGenerated
  let targetActualExit := Classical.choice targetWrite.down
  exact
    { sourceEvent := sourceEvent
      sourceEventExact := rfl
      sourcePayment :=
        sourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit
          (sourceIndex + 2)
      sourceWrite := sourceWrite
      sourceWriteExact := rfl
      targetEvent := targetEvent
      targetEventExact := rfl
      targetWrite := targetWrite
      targetWriteExact := rfl
      sourceActualExit := sourceActualExit
      sourceActualExitChoiceExact := rfl
      receiptActualExit := receiptActualExit
      receiptActualExitChoiceExact := rfl
      targetActualExit := targetActualExit
      targetActualExitChoiceExact := rfl
      sourceReceiptActualExitExact :=
        (periodicActualServiceExitAt_eq_canonical sourceActualExit).trans
          (periodicActualServiceExitAt_eq_canonical receiptActualExit).symm
      receiptTargetActualExitExact :=
        (periodicActualServiceExitAt_eq_canonical receiptActualExit).trans
          (periodicActualServiceExitAt_eq_canonical targetActualExit).symm
      targetWholeLedgerNativeWriteExact :=
        contributionCapacityReopeningActionTargetWholeLedger_nativeWrite_exact
          oldVisit sourceIndex
      everyTargetRowEvolved :=
        contributionCapacityReopeningActionTargetEveryRow_evolved oldVisit
          sourceIndex
      firstSuccessor := PUnit.unit
      firstSuccessorExact := HEq.rfl }

namespace ContributionCapacityReopeningActionPaymentAt

/-- Paid next is only the existing action-target macro next. -/
def nextPaidBy
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (_payment : ContributionCapacityReopeningActionPaymentAt oldVisit
      sourceIndex) :=
  (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
    ).target.targetAnswerAndNext.nextCurrent

@[simp] theorem nextPaidBy_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
      sourceIndex).nextPaidBy =
      ⟨(CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
          ).target.TargetV,
        (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
          ).target.targetRoot.toAuthoritativeRoot,
        (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
          ).target.targetVisit⟩ :=
  generatedContributionCapacityReopening_macroNext_exact oldVisit sourceIndex

end ContributionCapacityReopeningActionPaymentAt

end
end M14SourceGeneratedContributionCapacityReopeningActionPayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningActionPayment.sourceGeneratedContributionCapacityReopeningActionPaymentAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningActionPayment.ContributionCapacityReopeningActionPaymentAt.nextPaidBy_exact
