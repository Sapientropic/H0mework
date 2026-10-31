import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Payment.Terminal.Producer.SourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceipt
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Preservation.PostSettlement.Step.Consumer.ProofCarryingContributionCapacityPostSettlementCanonicalPaidStep

/-!
# Proof-carrying current-twelve joint paid tail

One source-generated carrier consumes the survivor source-event Payment, joint
actual action, separate faithful-terminal receipt, first post-root Payment and
the recursive post-root paid-step invariant.  Search remains a same-root
different compilation and cannot replace actual play.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityJointSettlementPaidTail

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14SourceGeneratedContributionCapacityJointSettlementCompiler
open M14SourceGeneratedContributionCapacityJointSettlementRoot
open M14SourceGeneratedSequentialContributionCapacityJointSettlement
open M14SourceGeneratedContributionCapacityJointSettlementState
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityJointSettlementCrossRootPayment
open M14SourceGeneratedContributionCapacityJointSettlementCrossRootPayment.SourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
open M14SourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceipt
open M14ProofCarryingContributionCapacityPostSettlementCanonicalPaidStep

def contributionCapacityJointSettlementFirstPostRootCurrentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeAuthoritativeRootCurrentAt (JointSettlementNAt oldVisit) :=
  ⟨PostSettlementRenewalVAt oldVisit,
    contributionCapacityPostSettlementRenewalAuthoritativeRoot oldVisit
      sourceIndex,
    contributionCapacityPostSettlementRenewalInitialVisit oldVisit sourceIndex⟩

def contributionCapacityJointSettlementFirstPostPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex 0 :=
  sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
    oldVisit sourceIndex 0

abbrev ContributionCapacityJointSettlementSourceVsMaterialServiceAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop :=
  let material := CanonicalJointMaterialAt oldVisit sourceIndex
  (Sum.inl material.sourceEvent :
      ExactTemporalCausalRootEventAt
          (ContributionCapacityJointSettlementSurvivorRootAt oldVisit
            sourceIndex).toAuthoritativeRoot.toLedgerRoot
          (contributionCapacityJointSettlementSurvivorVisitAt oldVisit
            sourceIndex) ⊕
        ExactTemporalCausalRootEventAt
          M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot
          (M14UBIPeriodicRootHistory.temporalVisitAt
            (contributionCapacityJointSettlementDepthAt sourceIndex))) ≠
    Sum.inr material.sourceActualService.paymentOccurrence.rootOccurrence

theorem contributionCapacityJointSettlementSourceOccurrence_ne_materialService
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ContributionCapacityJointSettlementSourceVsMaterialServiceAt oldVisit
      sourceIndex :=
  (contributionCapacityJointSettlement_survivorOccurrence_ne_jointRootAxes
    oldVisit sourceIndex).2.2

/-- Full actual seam.  The object fields remain distinct: action payment,
terminal receipt, post payment and post paid step are never identified. -/
structure SourceGeneratedContributionCapacityJointSettlementPaidTailAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Type 27 where
  private mk ::
  actionPayment :
    CanonicalContributionCapacityJointSettlementCrossRootPaymentAt oldVisit
      sourceIndex
  terminalReceipt :
    SourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceiptAt
      oldVisit sourceIndex
  terminalConsumesActionPaymentExact :
    terminalReceipt.sourceActionPayment = actionPayment
  firstPostPayment :
    CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex 0
  firstPostPaidStep :
    ConsumedContributionCapacityPostSettlementCanonicalPaidStepAt oldVisit
      sourceIndex 0 firstPostPayment
  sourcePaymentFromEvent : actionPayment.sourcePayment =
    contributionCapacityJointSettlementSourcePaymentAt oldVisit sourceIndex
  sourceCompilerNativeWriteExact :
    (contributionCapacityJointSettlementSourceCompilerAt oldVisit sourceIndex
      ).compile
        (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit
          sourceIndex).occurrence =
      .nativeWrite actionPayment.sourcePayment rfl
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
            sourceIndex).occurrence)
  everySourceRowEvolved : ∀ entryIndex : Fin 2,
    (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex) =
      .evolved
        (contributionCapacityJointSettlementSourceRowEvolutionAt oldVisit
          sourceIndex entryIndex)
  actionNextIsTerminalCurrent : actionPayment.nextPaidBy =
    ⟨ContributionCapacityJointSettlementVAt oldVisit,
      (CanonicalJointRootAt oldVisit sourceIndex).toAuthoritativeRoot,
      (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
        sourceIndex).target.targetVisit⟩
  everyTerminalRow : ∀ entryIndex : Fin 2,
    (contributionCapacityJointSettlementTerminalRootEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex) =
      .terminal
        ((contributionCapacityJointSettlementTerminalExactAt oldVisit
          sourceIndex).ledgerEvolution.discharge
            (contributionCapacityJointSettlementLiveEntryAt oldVisit
              entryIndex))
  terminalNextIsFirstPostCurrent :
    contributionCapacityJointSettlementTerminalNextPaidBy oldVisit sourceIndex =
      contributionCapacityJointSettlementFirstPostRootCurrentAt oldVisit
        sourceIndex
  firstPostVisitExact :
    contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex 0 =
      contributionCapacityPostSettlementRenewalInitialVisit oldVisit
        sourceIndex
  firstPostCompilerWriteExact :
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex
      ).toRootSource.actual.compile
        (contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
          0).occurrence =
      .nativeWrite firstPostPayment.write
  actualSearchCompilationsDistinct :
    (contributionCapacityJointSettlementActionStateAt oldVisit sourceIndex
      ).compileInquiry () ≠
      (contributionCapacitySettlementSurvivorStateAt oldVisit sourceIndex 2
        ).compileInquiry ()
  actualCompilationExact :
    (contributionCapacityJointSettlementActionStateAt oldVisit sourceIndex
      ).compileInquiry () =
      .actualAction
        (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
          sourceIndex)

def sourceGeneratedContributionCapacityJointSettlementPaidTailAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceGeneratedContributionCapacityJointSettlementPaidTailAt oldVisit
      sourceIndex :=
  let actionPayment :=
    sourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
      oldVisit sourceIndex
  let terminalReceipt :=
    sourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceiptAt
      oldVisit sourceIndex
  let firstPostPayment :=
    contributionCapacityJointSettlementFirstPostPaymentAt oldVisit sourceIndex
  { actionPayment := actionPayment
    terminalReceipt := terminalReceipt
    terminalConsumesActionPaymentExact := rfl
    firstPostPayment := firstPostPayment
    firstPostPaidStep :=
      proofCarryingContributionCapacityPostSettlementCanonicalPaidStepAt
        oldVisit sourceIndex 0 firstPostPayment
    sourcePaymentFromEvent := actionPayment.sourcePaymentWitnessExact
    sourceCompilerNativeWriteExact := by
      rw [actionPayment.sourcePaymentWitnessExact]
      exact
        contributionCapacityJointSettlementSourceCompiler_nativeWrite_exact
          oldVisit sourceIndex
    everySourceRowEvolved := actionPayment.everySourceRowEvolved
    actionNextIsTerminalCurrent := terminalReceipt.sourceActionNextExact
    everyTerminalRow := terminalReceipt.everyRowTerminal
    terminalNextIsFirstPostCurrent := terminalReceipt.nextPaidByExact
    firstPostVisitExact := rfl
    firstPostCompilerWriteExact := firstPostPayment.compilerWriteExact
    actualSearchCompilationsDistinct :=
      jointSettlementActualPlay_search_compilations_distinct oldVisit
        sourceIndex
    actualCompilationExact :=
      contributionCapacityJointSettlementActionState_compiles_generated
        oldVisit sourceIndex }

inductive ProofCarryingContributionCapacityJointSettlementPaidTailConsumerAt
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (tail : SourceGeneratedContributionCapacityJointSettlementPaidTailAt
      oldVisit sourceIndex) : Type 28
  | private consumed

def proofCarryingContributionCapacityJointSettlementPaidTailConsumerAt
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (tail : SourceGeneratedContributionCapacityJointSettlementPaidTailAt
      oldVisit sourceIndex) :
    ProofCarryingContributionCapacityJointSettlementPaidTailConsumerAt tail :=
  .consumed

namespace ProofCarryingContributionCapacityJointSettlementPaidTailConsumerAt

variable {oldVisit : OldVisit} {sourceIndex : Nat}
  {tail : SourceGeneratedContributionCapacityJointSettlementPaidTailAt oldVisit
    sourceIndex}
  (consumer :
    ProofCarryingContributionCapacityJointSettlementPaidTailConsumerAt tail)

def actionPayment := by cases consumer; exact tail.actionPayment

def terminalReceipt := by cases consumer; exact tail.terminalReceipt

def firstPostPayment := by cases consumer; exact tail.firstPostPayment

def firstPostPaidStep := by cases consumer; exact tail.firstPostPaidStep

theorem actionNext_isTerminalCurrent :
    (actionPayment consumer).nextPaidBy =
      ⟨ContributionCapacityJointSettlementVAt oldVisit,
        (CanonicalJointRootAt oldVisit sourceIndex).toAuthoritativeRoot,
        (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
          sourceIndex).target.targetVisit⟩ :=
  tail.actionNextIsTerminalCurrent

theorem terminalNext_isFirstPostCurrent :
    contributionCapacityJointSettlementTerminalNextPaidBy oldVisit sourceIndex =
      contributionCapacityJointSettlementFirstPostRootCurrentAt oldVisit
        sourceIndex :=
  contributionCapacityJointSettlementTerminalNextPaidBy_exact oldVisit
    sourceIndex

theorem firstPostPayment_generatesCanonicalNext :
    let consumed := firstPostPaidStep consumer
    HEq consumed.2.sourcePayment.nextPaidBy
      (M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent.SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
        consumed.2.targetCurrent).occurrence :=
  (firstPostPaidStep consumer).2.paidNext_isTargetCanonicalOccurrence

theorem actualPlay_ne_search :
    (contributionCapacityJointSettlementActionStateAt oldVisit sourceIndex
      ).compileInquiry () ≠
      (contributionCapacitySettlementSurvivorStateAt oldVisit sourceIndex 2
        ).compileInquiry () :=
  jointSettlementActualPlay_search_compilations_distinct oldVisit sourceIndex

end ProofCarryingContributionCapacityJointSettlementPaidTailConsumerAt

abbrev ConsumedContributionCapacityJointSettlementPaidTailAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  Sigma fun tail :
      SourceGeneratedContributionCapacityJointSettlementPaidTailAt oldVisit
        sourceIndex =>
    ProofCarryingContributionCapacityJointSettlementPaidTailConsumerAt tail

def proofCarryingContributionCapacityJointSettlementPaidTailAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ConsumedContributionCapacityJointSettlementPaidTailAt oldVisit sourceIndex :=
  let tail :=
    sourceGeneratedContributionCapacityJointSettlementPaidTailAt oldVisit
      sourceIndex
  ⟨tail, proofCarryingContributionCapacityJointSettlementPaidTailConsumerAt tail⟩

structure ProofCarryingContributionCapacityJointSettlementPaidTailCertificateAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  consumedTail : Nonempty
    (ConsumedContributionCapacityJointSettlementPaidTailAt oldVisit sourceIndex)
  actionNextTerminal :
    (sourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
        oldVisit sourceIndex).nextPaidBy =
      ⟨ContributionCapacityJointSettlementVAt oldVisit,
        (CanonicalJointRootAt oldVisit sourceIndex).toAuthoritativeRoot,
        (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
          sourceIndex).target.targetVisit⟩
  terminalNextPost :
    contributionCapacityJointSettlementTerminalNextPaidBy oldVisit sourceIndex =
      contributionCapacityJointSettlementFirstPostRootCurrentAt oldVisit
        sourceIndex
  actualSearchDistinct :
    (contributionCapacityJointSettlementActionStateAt oldVisit sourceIndex
      ).compileInquiry () ≠
      (contributionCapacitySettlementSurvivorStateAt oldVisit sourceIndex 2
        ).compileInquiry ()
  sourceOccurrenceDistinctFromMaterialService :
    ContributionCapacityJointSettlementSourceVsMaterialServiceAt oldVisit
      sourceIndex

theorem proofCarryingContributionCapacityJointSettlementPaidTail
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityJointSettlementPaidTailCertificateAt
      oldVisit sourceIndex where
  consumedTail :=
    ⟨proofCarryingContributionCapacityJointSettlementPaidTailAt oldVisit
      sourceIndex⟩
  actionNextTerminal :=
    contributionCapacityJointSettlementActionNext_isTerminalCurrent oldVisit
      sourceIndex
  terminalNextPost :=
    contributionCapacityJointSettlementTerminalNextPaidBy_exact oldVisit
      sourceIndex
  actualSearchDistinct :=
    jointSettlementActualPlay_search_compilations_distinct oldVisit sourceIndex
  sourceOccurrenceDistinctFromMaterialService :=
    contributionCapacityJointSettlementSourceOccurrence_ne_materialService
      oldVisit sourceIndex

set_option linter.unusedVariables false in
theorem jointPaidTail_negativeControls
    (oldVisit : OldVisit) (sourceIndex : Nat) : True := by
  let material := CanonicalJointMaterialAt oldVisit sourceIndex
  let actionPayment :=
    sourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
      oldVisit sourceIndex
  let terminalReceipt :=
    sourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceiptAt
      oldVisit sourceIndex
  let postPayment :=
    contributionCapacityJointSettlementFirstPostPaymentAt oldVisit sourceIndex
  fail_if_success exact
    (material.sourceActualService :
      ContributionCapacityJointSettlementSourceWholeLedgerPaymentAt oldVisit
        sourceIndex)
  fail_if_success exact
    (canonicalContributionCapacityJointSettlementSearchTick :
      CanonicalContributionCapacityJointSettlementCrossRootPaymentAt oldVisit
        sourceIndex)
  fail_if_success exact
    (actionPayment.sourcePayment :
      CanonicalContributionCapacityJointSettlementCrossRootPaymentAt oldVisit
        sourceIndex)
  fail_if_success exact
    (terminalReceipt :
      CanonicalContributionCapacityJointSettlementCrossRootPaymentAt oldVisit
        sourceIndex)
  fail_if_success exact
    (postPayment :
      SourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceiptAt
        oldVisit sourceIndex)
  trivial

end
end M14ProofCarryingContributionCapacityJointSettlementPaidTail
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityJointSettlementPaidTail.proofCarryingContributionCapacityJointSettlementPaidTail
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityJointSettlementPaidTail.ProofCarryingContributionCapacityJointSettlementPaidTailConsumerAt.firstPostPayment_generatesCanonicalNext
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityJointSettlementPaidTail.jointPaidTail_negativeControls
