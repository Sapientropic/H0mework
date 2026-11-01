import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Consumer.SourceGeneratedContributionCapacityJointSettlementConsumer

/-!
# Joint-settlement actual-action Payment

The exact survivor-current-twelve occurrence carries its own actual-service
native payment.  That same event indexes the already generated joint-settlement
actual action, its ingress receipt and the action target's first successor.
The payment stores no macro next or target; `NextPaidBy` is projected only from
the generated action authority.  The same-depth service axis retained by the
material is not used as a substitute source occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityJointSettlementCrossRootPayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorRoot
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14SourceGeneratedContributionCapacityJointSettlementCompiler
open M14SourceGeneratedContributionCapacityJointSettlementRoot
open M14SourceGeneratedSequentialContributionCapacityJointSettlement
open M14SourceGeneratedContributionCapacityJointSettlementState
open M14SourceGeneratedContributionCapacityJointSettlementConsumer

abbrev ContributionCapacityJointSettlementPaidMaterialAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  CanonicalJointMaterialAt oldVisit sourceIndex

abbrev ContributionCapacityJointSettlementPaidSourceEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacityJointSettlementSurvivorSourceEventAt oldVisit sourceIndex

abbrev ContributionCapacityJointSettlementPaidSourceCurrentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  show Nat from
    (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex
      ).current

abbrev ContributionCapacityJointSettlementSourceWholeLedgerPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ContributionCapacitySettlementSurvivorExactWholeLedgerPaymentAt
    (ContributionCapacityJointSettlementPaidSourceCurrentAt oldVisit
      sourceIndex)

/-- Payment extracted from the survivor source event itself. -/
def contributionCapacityJointSettlementSourcePaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ContributionCapacityJointSettlementSourceWholeLedgerPaymentAt oldVisit
      sourceIndex :=
  PLift.up
    (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit sourceIndex
      ).occurrence.2.periodicExitGenerated

def contributionCapacityJointSettlementSourceActualExitAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  Classical.choice
    (contributionCapacityJointSettlementSourcePaymentAt oldVisit sourceIndex
      ).down

abbrev ContributionCapacityJointSettlementPaidActionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  SourceGeneratedSequentialActualActionAt
    (contributionCapacityJointSettlementActionProgramAt oldVisit sourceIndex
      (ContributionCapacityJointSettlementPaidMaterialAt oldVisit sourceIndex))
    (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit sourceIndex)

def generatedContributionCapacityJointSettlementPaidActionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ContributionCapacityJointSettlementPaidActionAt oldVisit sourceIndex :=
  (contributionCapacityJointSettlementActionProgramAt oldVisit sourceIndex
    (ContributionCapacityJointSettlementPaidMaterialAt oldVisit sourceIndex)
    ).generate
      (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit sourceIndex)

@[simp] theorem generatedContributionCapacityJointSettlementPaidAction_eq_canonical
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    generatedContributionCapacityJointSettlementPaidActionAt oldVisit
        sourceIndex =
      generatedContributionCapacityJointSettlementActionAt oldVisit sourceIndex
        (ContributionCapacityJointSettlementPaidMaterialAt oldVisit
          sourceIndex) :=
  rfl

def contributionCapacityJointSettlementSourceCompilerAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacitySettlementSurvivorLedgerCompiler oldVisit sourceIndex
    (CanonicalContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)

theorem contributionCapacityJointSettlementSourceCompiler_nativeWrite_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityJointSettlementSourceCompilerAt oldVisit sourceIndex
      ).compile
        (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit
          sourceIndex).occurrence =
      .nativeWrite
        (contributionCapacityJointSettlementSourcePaymentAt oldVisit sourceIndex)
        rfl
        (contributionCapacitySettlementSurvivorEmitted oldVisit sourceIndex
          (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
            sourceIndex)
          (ContributionCapacityJointSettlementPaidSourceCurrentAt oldVisit
              sourceIndex +
            1))
        (contributionCapacitySettlementSurvivorEvolution oldVisit sourceIndex
          (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
            sourceIndex)
          (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit
            sourceIndex).occurrence) :=
  rfl

theorem contributionCapacityJointSettlementSourceRootReceipt_nativeWrite_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack =
      (contributionCapacityJointSettlementSourceCompilerAt oldVisit sourceIndex
        ).compile
          (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit
            sourceIndex).occurrence :=
  rfl

def contributionCapacityJointSettlementSourceRowEvolutionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2) :=
  (contributionCapacitySettlementSurvivorEvolution oldVisit sourceIndex
    (CanonicalContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit sourceIndex
      ).occurrence).destination
        (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex) |>.2

theorem contributionCapacityJointSettlementSourceEveryRow_evolved
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2) :
    (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex) =
      .evolved
        (contributionCapacityJointSettlementSourceRowEvolutionAt oldVisit
          sourceIndex entryIndex) := by
  rw [contributionCapacityJointSettlementSourceRootReceipt_nativeWrite_exact,
    contributionCapacityJointSettlementSourceCompiler_nativeWrite_exact]
  rfl

/-- Private rich action-payment carrier.  Source payment, source write, action
and receipt are all forced to share the exact survivor occurrence. -/
structure SourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (action : ContributionCapacityJointSettlementPaidActionAt oldVisit
      sourceIndex) : Type 12 where
  private mk ::
  sourcePayment :
    ContributionCapacityJointSettlementSourceWholeLedgerPaymentAt oldVisit
      sourceIndex
  sourcePaymentWitnessExact : sourcePayment =
    PLift.up
      (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit sourceIndex
        ).occurrence.2.periodicExitGenerated
  sourceRootReceiptNativeWriteExact :
    (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack =
      (contributionCapacityJointSettlementSourceCompilerAt oldVisit sourceIndex
        ).compile
          (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit
            sourceIndex).occurrence
  everySourceRowEvolved : ∀ entryIndex : Fin 2,
    (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex) =
      .evolved
        (contributionCapacityJointSettlementSourceRowEvolutionAt oldVisit
          sourceIndex entryIndex)
  actionReceipt : action.target.Receipt action.answer
  actionReceiptExact : actionReceipt = action.receipt
  targetFirstSuccessorExact : action.target.firstSuccessor =
    contributionCapacityJointSettlementFirstSuccessor oldVisit sourceIndex
      (ContributionCapacityJointSettlementPaidMaterialAt oldVisit sourceIndex)

abbrev CanonicalContributionCapacityJointSettlementCrossRootPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  SourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt oldVisit
    sourceIndex
    (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
      sourceIndex)

def sourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    CanonicalContributionCapacityJointSettlementCrossRootPaymentAt oldVisit
      sourceIndex where
  sourcePayment :=
    contributionCapacityJointSettlementSourcePaymentAt oldVisit sourceIndex
  sourcePaymentWitnessExact := rfl
  sourceRootReceiptNativeWriteExact :=
    contributionCapacityJointSettlementSourceRootReceipt_nativeWrite_exact
      oldVisit sourceIndex
  everySourceRowEvolved :=
    contributionCapacityJointSettlementSourceEveryRow_evolved oldVisit
      sourceIndex
  actionReceipt :=
    (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
      sourceIndex).receipt
  actionReceiptExact := rfl
  targetFirstSuccessorExact := rfl

namespace SourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt

variable {oldVisit : OldVisit} {sourceIndex : Nat}
  {action : ContributionCapacityJointSettlementPaidActionAt oldVisit
    sourceIndex}

/-- Actual macro next; it is a dependent projection of action authority, never
a field of the payment carrier. -/
def nextPaidBy
    (_payment :
      SourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
        oldVisit sourceIndex action) :=
  action.target.targetAnswerAndNext.nextCurrent

theorem nextPaidBy_exact
    (payment :
      SourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
        oldVisit sourceIndex action) :
    payment.nextPaidBy =
      ⟨action.target.TargetV, action.target.targetRoot.toAuthoritativeRoot,
        action.target.targetVisit⟩ :=
  action.target.targetAnswerAndNext_next_eq

end SourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt

theorem contributionCapacityJointSettlementCrossRootPayment_hasNoStoredTarget
    (oldVisit : OldVisit) (sourceIndex : Nat) : True := by
  let payment :=
    sourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
      oldVisit sourceIndex
  fail_if_success exact payment.next
  fail_if_success exact payment.target
  fail_if_success exact payment.future
  fail_if_success exact payment.coverage
  trivial

end
end M14SourceGeneratedContributionCapacityJointSettlementCrossRootPayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementCrossRootPayment.sourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementCrossRootPayment.SourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt.nextPaidBy_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementCrossRootPayment.contributionCapacityJointSettlementSourceCompiler_nativeWrite_exact
