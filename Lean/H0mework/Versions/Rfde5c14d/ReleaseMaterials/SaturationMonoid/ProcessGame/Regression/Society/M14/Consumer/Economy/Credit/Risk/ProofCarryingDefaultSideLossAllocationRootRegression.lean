import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Credit.Risk.ProofCarryingDefaultSideLossAllocationConsumers
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Credit.PeriodicClearingCreditClaimLifecycle

/-!
# Root consumer for the default-side loss-allocation action

This certificate consumes the unique joint U8 core, its in-place richer
revision, the source-fixed first whole-ledger compiler image, and the ordinary
canonical-runtime first-tick continuation.  The two child consumers remain in their smaller
receipt-indexed module; this file only proves that their central split is the
actual root update and that no merge, fourth row, or bearer collapse is hidden
beside it.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingDefaultSideLossAllocationRootRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalU8RevisedLedger
open M9ProofCarryingRenewalU8RevisedWorld
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedLossAllocationCompiler
open M14SourceGeneratedLossAllocationRestructuring
open M14PeriodicClearingCreditClaimLifecycle

abbrev OldVisit :=
  RootVisit M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toRoot
abbrev revisionAt (visit : OldVisit) := generatedTypedRevisionAt visit
abbrev actionAt (visit : OldVisit) :=
  generatedDefaultSideLossAllocationAt visit
abbrev lawAt (visit : OldVisit) :=
  (revisionAt visit).sourceFixedRestructuringLaw
abbrev occurrenceAt (visit : OldVisit) :=
  (revisionAt visit).initialRestructuringGenerated.occurrence
abbrev firstEvolutionAt (visit : OldVisit) :=
  (actionAt visit).successor.ledgerEvolution

/-! ## Exact finite geometry controls -/

/-- The first whole-ledger destination map is injective on its two source
rows.  Hence the richer first write is a split, not a simultaneous merge. -/
theorem firstDestination_injective_at
    (visit : OldVisit)
    (left right : (lossAllocationInitialLedger (rootedAt visit)).Entry)
    (destination_eq :
      ((lossAllocationFirstEvolution (rootedAt visit)
        (revisedEmittedAt visit 0)).destination
          left).1 =
        ((lossAllocationFirstEvolution (rootedAt visit)
          (revisedEmittedAt visit 0)).destination
          right).1) :
    left = right := by
  rcases lossAllocationInitialEntry_cases (rootedAt visit) left with
      left_eq | left_eq <;>
    rcases lossAllocationInitialEntry_cases (rootedAt visit) right with
      right_eq | right_eq
  · exact left_eq.trans right_eq.symm
  · subst left
    subst right
    exact False.elim
      (lossAllocationTargetObstruction_ne_childA (rootedAt visit) <|
      (lossAllocationFirst_destination_obstruction (rootedAt visit)
          (revisedEmittedAt visit 0)).symm.trans
        (destination_eq.symm.trans
          (lossAllocationFirst_destination_parent (rootedAt visit)
            (revisedEmittedAt visit 0))))
  · subst left
    subst right
    exact False.elim
      (lossAllocationTargetObstruction_ne_childA (rootedAt visit) <|
      (lossAllocationFirst_destination_obstruction (rootedAt visit)
          (revisedEmittedAt visit 0)).symm.trans
        (destination_eq.trans
          (lossAllocationFirst_destination_parent (rootedAt visit)
            (revisedEmittedAt visit 0))))
  · exact left_eq.trans right_eq.symm

/-- No genuine merge coverage can accompany the actual first whole-ledger
image.  The coverage value is arbitrary; the repeated-destination premise
already forces the two source entries to be identical. -/
theorem firstWholeLedger_genuineMerge_isEmpty_at
    (visit : OldVisit)
    (left right : (lossAllocationInitialLedger (rootedAt visit)).Entry)
    (destination_eq :
      ((lossAllocationFirstEvolution (rootedAt visit)
        (revisedEmittedAt visit 0)).destination
          left).1 =
        ((lossAllocationFirstEvolution (rootedAt visit)
          (revisedEmittedAt visit 0)).destination
          right).1) :
    IsEmpty
      (SourceNativeMergeCoverageAt (lawAt visit) (occurrenceAt visit)
          (lossAllocationFirstEvolution (rootedAt visit)
            (revisedEmittedAt visit 0))
          left right destination_eq × PLift (left ≠ right)) := by
  refine ⟨fun paired => ?_⟩
  exact paired.2.down
    (firstDestination_injective_at visit left right destination_eq)

/-- The target complete ledger has exactly the two existing-leg children and
the transferred obstruction continuation.  There is no fourth row mouth. -/
theorem firstTargetEntry_exactly_three_at
    (visit : OldVisit)
    (entry : (lossAllocationTargetLedger (rootedAt visit)).Entry) :
    entry = revisedLossChildAAt visit ∨
      entry = revisedLossChildBAt visit ∨
      entry = revisedTargetObstructionAt visit :=
  lossAllocationTargetEntry_cases (rootedAt visit) entry

/-- Same claim and responsibility do not collapse bearer identity.  The
proof-relevant exchange-leg admission generates distinct existing bearers. -/
theorem sameClaim_does_not_retype_childBearer_at (visit : OldVisit) :
    (actionAt visit).left.claim = (actionAt visit).right.claim ∧
      ((lawAt visit).obligationAt (occurrenceAt visit)
        (actionAt visit).left).content =
        ((lawAt visit).obligationAt (occurrenceAt visit)
          (actionAt visit).right).content ∧
      ((lawAt visit).obligationAt (occurrenceAt visit)
        (actionAt visit).left).bearer ≠
        ((lawAt visit).obligationAt (occurrenceAt visit)
          (actionAt visit).right).bearer :=
  ⟨rfl, rfl, (actionAt visit).bearers_distinct⟩

/-! ## One compact same-root certificate -/

structure ProofCarryingDefaultSideLossAllocationRootCertificateAtVisit
    (visit : OldVisit) : Prop where
  typedRevisionIsActionGrounding :
    typedRevisionSourceAt visit = (actionAt visit).fieldGroundedRevision
  compilerSelectsExactSplit :
    ((revisionAt visit).exactInitialRestructuringCertification
      (actionAt visit).successor).split
        (actionAt visit).left (actionAt visit).right
          (actionAt visit).origin_eq =
      SourceNativeSplitClassificationAt.split (actionAt visit).split
  firstWholeLedgerHasActualSuccessor :
    Nonempty (SourceNativeLedgerGeneratedSuccessorAt
      (revisionAt visit).initialRestructuringGenerated.occurrence
      (revisionAt visit).initialRestructuringGenerated.wholeLedgerWriteBack)
  firstWholeLedgerEvolutionExact :
    HEq (firstEvolutionAt visit)
      (lossAllocationFirstEvolution (rootedAt visit)
        (revisedEmittedAt visit 0))
  exactBudgetMatrix :
    (oldRevisedEntryAt visit).progressBudget = 2 ∧
      (newRevisedEntryAt visit).progressBudget = 0 ∧
      (revisedLossChildAAt visit).progressBudget = 1 ∧
      (revisedLossChildBAt visit).progressBudget = 1 ∧
      (revisedTargetObstructionAt visit).progressBudget = 0
  leftChildIsMaintained :
    HEq ((firstEvolutionAt visit).origin
      (revisedLossChildAAt visit)).2
      (lossAllocationParentToChildA (rootedAt visit))
  rightChildIsMaintained :
    HEq ((firstEvolutionAt visit).origin
      (revisedLossChildBAt visit)).2
      (lossAllocationParentToChildB (rootedAt visit))
  obstructionOriginExact :
    ((firstEvolutionAt visit).origin
      (revisedTargetObstructionAt visit)).1 = newRevisedEntryAt visit
  obstructionIsTransferredContinuity :
    HEq ((firstEvolutionAt visit).origin
      (revisedTargetObstructionAt visit)).2
      (lossAllocationObstructionContinuity (rootedAt visit))
  initialLedgerCovered :
    (entry : OpenResponsibilityAt
      (revisionAt visit).NewN (revisionAt visit).initialSupport) →
      Nonempty (Sigma fun oldEntry : OpenResponsibilityAt
        M9ProofCarryingRenewalU8Failure.N
          (M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toRoot.supportAt
            (rootedAt visit).oldSuccessor.next) =>
        PLift ((revisionAt visit).oldTargetOpenLedger.forward oldEntry =
          entry)) ∨
      entry = (revisionAt visit).newOnlyEntry
  targetOriginsCovered :
    (targetEntry : OpenResponsibilityAt (revisionAt visit).NewN
      ((revisionAt visit).newRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (actionAt visit).successor.targetOccurrence)) →
      Nonempty (Sigma fun oldEntry : OpenResponsibilityAt
        M9ProofCarryingRenewalU8Failure.N
          (M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toRoot.supportAt
            (rootedAt visit).oldSuccessor.next) =>
        PLift (((actionAt visit).successor.ledgerEvolution.origin
          targetEntry).1 =
          (revisionAt visit).oldTargetOpenLedger.forward oldEntry)) ∨
      ((actionAt visit).successor.ledgerEvolution.origin targetEntry).1 =
        (revisionAt visit).newOnlyEntry
  wholeMaterialProvenance :
    sourceGeneratedLossAllocationMaterial.defaultOccurrence =
        M14ClearingConsumerDeath.sourceGeneratedClearingConsumerDeath ∧
      sourceGeneratedLossAllocationMaterial.activationSeed =
        M14SourceGeneratedClearingBackstopActivation.sourceGeneratedClearingBackstopExactSeed ∧
      HEq sourceGeneratedLossAllocationMaterial.standing
        M14SourceClearingBackstopCreditStanding.sourceGeneratedClearingBackstopCreditStanding ∧
      sourceGeneratedLossAllocationMaterial.parentBearer =
        M3ExchangeSettlementPriceRegression.partialOpenB.obligation.bearer ∧
      sourceGeneratedLossAllocationMaterial.childBearerAt =
        existingLossBearerAt ∧
      sourceGeneratedLossAllocationMaterial.childBearerAt
          M3FiniteExchangeFixture.Leg.a ≠
        sourceGeneratedLossAllocationMaterial.childBearerAt
          M3FiniteExchangeFixture.Leg.b
  leftReceiptConsumer : Nonempty
    (M14ProofCarryingDefaultSideLossAllocationConsumers.SourceGeneratedDefaultSideChildConsumerAtVisit
      visit (actionAt visit).left rfl)
  rightReceiptConsumer : Nonempty
    (M14ProofCarryingDefaultSideLossAllocationConsumers.SourceGeneratedDefaultSideChildConsumerAtVisit
      visit (actionAt visit).right (actionAt visit).origin_eq.symm)
  noGenuineMerge :
    (left right : (lossAllocationInitialLedger (rootedAt visit)).Entry) →
    (destination_eq :
      ((lossAllocationFirstEvolution (rootedAt visit)
        (revisedEmittedAt visit 0)).destination
          left).1 =
        ((lossAllocationFirstEvolution (rootedAt visit)
          (revisedEmittedAt visit 0)).destination
          right).1) →
      IsEmpty
        (SourceNativeMergeCoverageAt (lawAt visit) (occurrenceAt visit)
            (lossAllocationFirstEvolution (rootedAt visit)
              (revisedEmittedAt visit 0))
            left right destination_eq × PLift (left ≠ right))
  noFourthTargetRow :
    (entry : (lossAllocationTargetLedger (rootedAt visit)).Entry) →
      entry = revisedLossChildAAt visit ∨
        entry = revisedLossChildBAt visit ∨
        entry = revisedTargetObstructionAt visit
  sameClaimDistinctBearer :
    (actionAt visit).left.claim = (actionAt visit).right.claim ∧
      ((lawAt visit).obligationAt (occurrenceAt visit)
        (actionAt visit).left).content =
        ((lawAt visit).obligationAt (occurrenceAt visit)
          (actionAt visit).right).content ∧
      ((lawAt visit).obligationAt (occurrenceAt visit)
        (actionAt visit).left).bearer ≠
        ((lawAt visit).obligationAt (occurrenceAt visit)
          (actionAt visit).right).bearer

/-- Visit-only builder certificate.  It proves the exact revised action at
the requested old-root occurrence; it does not claim that the canonical
inquiry runtime selected or resumed that occurrence. -/
theorem proofCarryingDefaultSideLossAllocationRootCertificateAtVisit
    (visit : OldVisit) :
    ProofCarryingDefaultSideLossAllocationRootCertificateAtVisit visit where
  typedRevisionIsActionGrounding := rfl
  compilerSelectsExactSplit :=
    (actionAt visit).genuineSplit.compiler_selects_exact_split
  firstWholeLedgerHasActualSuccessor := ⟨(actionAt visit).successor⟩
  firstWholeLedgerEvolutionExact := HEq.rfl
  exactBudgetMatrix := ⟨rfl, rfl, rfl, rfl, rfl⟩
  leftChildIsMaintained := HEq.rfl
  rightChildIsMaintained := HEq.rfl
  obstructionOriginExact := rfl
  obstructionIsTransferredContinuity := HEq.rfl
  initialLedgerCovered := revisedActual_initialLedger_noDormant_at visit
  targetOriginsCovered := revisedActual_targetOrigins_covered_at visit
  wholeMaterialProvenance := revisedOccurrence_whole_material_exact_at visit 0
  leftReceiptConsumer :=
    ⟨M14ProofCarryingDefaultSideLossAllocationConsumers.leftChildConsumerAt
      visit⟩
  rightReceiptConsumer :=
    ⟨M14ProofCarryingDefaultSideLossAllocationConsumers.rightChildConsumerAt
      visit⟩
  noGenuineMerge := firstWholeLedger_genuineMerge_isEmpty_at visit
  noFourthTargetRow := firstTargetEntry_exactly_three_at visit
  sameClaimDistinctBearer := sameClaim_does_not_retype_childBearer_at visit

/-- Building the exact revised action at a visit is not a runtime-resumption
receipt.  Installation authority appears only in the initial facade below. -/
theorem atVisitBuilder_has_no_runtimeInstallation_mouth
    (_visit : OldVisit) : True := by
  let certificate :=
    proofCarryingDefaultSideLossAllocationRootCertificateAtVisit _visit
  fail_if_success exact certificate.jointCoreUsesTypedRevision
  fail_if_success exact certificate.runtimeCofaceResumption
  fail_if_success exact certificate.runtimeFirstTickNextState
  fail_if_success exact certificate.creditDefaultIsWholeMaterial
  trivial

/-! ## Definitionally specialized runtime-installed facade -/

abbrev initialVisit : OldVisit :=
  M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toRoot.initialVisit
abbrev revision := revisionAt initialVisit
abbrev action := actionAt initialVisit
abbrev law := lawAt initialVisit
abbrev occurrence := occurrenceAt initialVisit
abbrev firstEvolution := firstEvolutionAt initialVisit
abbrev credit := sourceGeneratedProofCarryingPeriodicClearingCreditAt 0

theorem firstDestination_injective
    (left right : (lossAllocationInitialLedger rooted).Entry)
    (destination_eq :
      ((lossAllocationFirstEvolution rooted (revisedEmitted 0)).destination
          left).1 =
        ((lossAllocationFirstEvolution rooted (revisedEmitted 0)).destination
          right).1) :
    left = right :=
  firstDestination_injective_at initialVisit left right destination_eq

theorem firstWholeLedger_genuineMerge_isEmpty
    (left right : (lossAllocationInitialLedger rooted).Entry)
    (destination_eq :
      ((lossAllocationFirstEvolution rooted (revisedEmitted 0)).destination
          left).1 =
        ((lossAllocationFirstEvolution rooted (revisedEmitted 0)).destination
          right).1) :
    IsEmpty
      (SourceNativeMergeCoverageAt law occurrence
          (lossAllocationFirstEvolution rooted (revisedEmitted 0))
          left right destination_eq × PLift (left ≠ right)) :=
  firstWholeLedger_genuineMerge_isEmpty_at initialVisit
    left right destination_eq

theorem firstTargetEntry_exactly_three
    (entry : (lossAllocationTargetLedger rooted).Entry) :
    entry = revisedLossChildA ∨ entry = revisedLossChildB ∨
      entry = revisedTargetObstruction :=
  firstTargetEntry_exactly_three_at initialVisit entry

theorem sameClaim_does_not_retype_childBearer :
    action.left.claim = action.right.claim ∧
      (law.obligationAt occurrence action.left).content =
        (law.obligationAt occurrence action.right).content ∧
      (law.obligationAt occurrence action.left).bearer ≠
        (law.obligationAt occurrence action.right).bearer :=
  sameClaim_does_not_retype_childBearer_at initialVisit

structure ProofCarryingDefaultSideLossAllocationRootCertificate : Prop
    extends ProofCarryingDefaultSideLossAllocationRootCertificateAtVisit
      initialVisit where
  jointCoreUsesTypedRevision :
    M9ProofCarryingRenewalU8Revision.jointCore.revision = typedRevisionSource
  creditDefaultIsWholeMaterial :
    credit.defaultOccurrence =
      sourceGeneratedLossAllocationMaterial.defaultOccurrence
  creditDownsideBearerIsWholeMaterial :
    credit.downsideBearer = sourceGeneratedLossAllocationMaterial.parentBearer
  creditDebtLineageExact :
    credit.debtLineage = credit.backstop.appliedReform.debtLineage
  creditSameClaim : credit.sourceClaim = credit.futureClaim
  creditTranslatedClaimIsSplitOldParentClaim :
    revision.translation.claim.forward credit.sourceClaim =
      oldRevisedEntry.claim
  runtimeFirstTickResolutionIsJointCore :
    M9ProofCarryingRenewalInquiryRuntime.firstTick.resolution =
      .revised RootInquiryU8CompletionRegression.obstruction
        RootInquiryU8CompletionRegression.u7Gate
        RootInquiryU8CompletionRegression.failure
        M9ProofCarryingRenewalU8Revision.jointCore
  runtimeCofaceResumption :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      M9ProofCarryingRenewalU8Revision.jointCore
      M9ProofCarryingRenewalInquiryRuntime.jointRuntime 0
  runtimeFirstTickNextState :
    (M9ProofCarryingRenewalInquiryRuntime.process.successorAt
      M9ProofCarryingRenewalInquiryRuntime.ProcessState.original ()).1 =
        M9ProofCarryingRenewalInquiryRuntime.ProcessState.contributionMergeAction
  runtimeFirstTickNextNode :
    M9ProofCarryingRenewalInquiryRuntime.firstTick.next.node =
      RootInquiryProcessNode.active
        (M9ProofCarryingRenewalInquiryRuntime.processPresentation
          .contributionMergeAction)
  runtimeFirstTickPreservesActionRoot : HEq
    (M9ProofCarryingRenewalInquiryRuntime.processPresentation
      .contributionMergeAction).state.base.root
    action.fieldGroundedRevision.generate.newLivingRoot

/-- Initial visit plus the canonical first-tick seals.  Only this fixed facade
claims runtime installation. -/
theorem proofCarryingDefaultSideLossAllocationRootCertificate :
    ProofCarryingDefaultSideLossAllocationRootCertificate where
  toProofCarryingDefaultSideLossAllocationRootCertificateAtVisit :=
    proofCarryingDefaultSideLossAllocationRootCertificateAtVisit initialVisit
  jointCoreUsesTypedRevision := rfl
  creditDefaultIsWholeMaterial := rfl
  creditDownsideBearerIsWholeMaterial := rfl
  creditDebtLineageExact := credit.debtLineageExact
  creditSameClaim := credit.sameClaimFromDebtLineage
  creditTranslatedClaimIsSplitOldParentClaim := rfl
  runtimeFirstTickResolutionIsJointCore :=
    M9ProofCarryingRenewalInquiryRuntime.firstTick_resolution_is_jointCore
  runtimeCofaceResumption :=
    M9ProofCarryingRenewalInquiryRuntime.cofaceResumption
  runtimeFirstTickNextState := rfl
  runtimeFirstTickNextNode :=
    M9ProofCarryingRenewalInquiryRuntime.secondState_node_is_contributionMergeAction
  runtimeFirstTickPreservesActionRoot :=
    M9ProofCarryingRenewalInquiryRuntime.firstTick_next_preserves_revisedLivingRoot

theorem rootCertificate_has_no_submitted_target : True := by
  let certificate := proofCarryingDefaultSideLossAllocationRootCertificate
  fail_if_success exact certificate.submittedRevision
  fail_if_success exact certificate.submittedSplit
  fail_if_success exact certificate.submittedCoverage
  fail_if_success exact certificate.submittedLedger
  fail_if_success exact certificate.submittedNext
  fail_if_success exact certificate.mergeAction
  fail_if_success exact certificate.fourthRow
  trivial

end
end M14ProofCarryingDefaultSideLossAllocationRootRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingDefaultSideLossAllocationRootRegression.proofCarryingDefaultSideLossAllocationRootCertificate
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingDefaultSideLossAllocationRootRegression.proofCarryingDefaultSideLossAllocationRootCertificateAtVisit
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingDefaultSideLossAllocationRootRegression.firstWholeLedger_genuineMerge_isEmpty
