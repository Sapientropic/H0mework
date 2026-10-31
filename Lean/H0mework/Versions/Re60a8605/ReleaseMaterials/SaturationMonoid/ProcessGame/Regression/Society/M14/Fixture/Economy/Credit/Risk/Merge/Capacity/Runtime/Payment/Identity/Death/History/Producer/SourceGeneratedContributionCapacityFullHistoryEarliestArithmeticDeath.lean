import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Payment.Action.Cut.Consumer.ProofCarryingContributionCapacityCutCrossRootPayment
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Identity.Death.History.U8.Producer.SourceGeneratedContributionCapacityU8InheritedRenewalDeath
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Identity.Death.History.Reopening.Producer.SourceGeneratedContributionCapacityReopeningRenewalDeath
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Identity.Death.History.Settlement.Producer.SourceGeneratedContributionCapacitySettlementBoundaryDeath
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Consumer.SourceGeneratedContributionCapacityJointSettlementConsumer

/-!
# Full-history first arithmetic death of the contribution lineage

The capacity-cut Payment strictly debits the exact contribution row from one
to zero.  The cut target then enters the existing self-U8 revision as an old,
nonfresh debt.  The revision receipt fixes its literal first whole-ledger write
to U8 current zero; that same event carries the inherited row from zero to zero,
so its exact strict-renewal fibre is empty.  Every later U8 and reopening
Payment preserves the same arithmetic death.

The carrier below is zero-choice.  It stores no date, history, coverage table,
target, future or death registry.  Its locus is the exact first-write event;
runtime tick and actual-service depth are separate observer coordinates.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutRoot
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityCutCrossRootPayment
open M14ProofCarryingContributionCapacityCutCrossRootPayment
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8RuntimePayment
open M14SourceGeneratedContributionCapacityU8Revision
open M14SourceGeneratedContributionCapacityU8RevisionNoFreeReceipt
open M14ProofCarryingContributionCapacityU8RevisionNoFreeReceipt
open M14SourceGeneratedContributionCapacityTargetOriginOrBirth
open M14SourceGeneratedContributionCapacityU8InheritedRenewalDeath
open M14SourceGeneratedContributionCapacityReopeningRenewalDeath
open M14SourceGeneratedContributionCapacitySettlementBoundaryDeath
open M14SourceGeneratedContributionCapacitySettlementCompiler
open M14SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceipt
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementConsumer

/-- Zero-choice certificate carrier for the already generated paid prefix. -/
structure SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath :
    Type 24 where
  private mk ::

def sourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath :
    SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath :=
  ⟨⟩

namespace SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath

/-! ## Exact predecessor and causal first write -/

def predecessorPayment
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    CanonicalContributionCapacityCutCrossRootPayment :=
  canonicalContributionCapacityCutCrossRootPayment

theorem predecessorDisposition_isStrictDebit
    (death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    death.predecessorPayment.targetEvent.wholeLedgerWriteBack.entryDisposition
        (initialContribution
          (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)) =
      .evolved death.predecessorPayment.actionReceipt.strictDebit :=
  canonicalContributionCapacityCutCrossRootPayment.strictDebitDispositionExact

theorem predecessorSourceBudget_eq_one
    (death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    (initialContribution
      (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
      ).progressBudget = 1 :=
  death.predecessorPayment.actionReceipt.sourceBudgetOne

theorem predecessorTargetBudget_eq_zero
    (death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    (contributionCapacityCutTargetContribution
      (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
      ).progressBudget = 0 :=
  death.predecessorPayment.actionReceipt.targetBudgetZero

theorem revisionReceipt
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    SourceGeneratedContributionCapacityU8RevisionNoFreeReceiptAt
      canonicalOldVisit :=
  sourceGeneratedContributionCapacityU8RevisionNoFreeReceiptAt
    canonicalOldVisit

/-- The locus authority is the exact event, not its numeric readout. -/
def locusRootEvent
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :=
  contributionCapacityU8RuntimePaymentRootEventAt canonicalOldVisit 0

theorem predecessorNext_isRuntimeStateThree
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    thirdTick.next = (jointRuntime.stateAt 3).engine :=
  depthTwo_runtimeNextEngine_exact.symm

theorem revisionTick_isRuntimeStateThreeTick
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    fourthTick = jointRuntime.tickAt 3 :=
  rfl

theorem revisionResolution_isRootedSelfU8
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    fourthTick.resolution =
      .revised
        (contributionCapacityResidual M9ProofCarryingRenewalU8Failure.rooted)
        (contributionCapacityU7Gate M9ProofCarryingRenewalU8Failure.rooted)
        (contributionCapacityOperationalFailure
          M9ProofCarryingRenewalU8Failure.rooted)
        (generatedContributionCapacityU8CoreAt canonicalOldVisit) :=
  depthThree_resolution_is_rootedSelfU8

theorem locusOccurrence_isRevisionFirstWrite
    (death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    (ContributionCapacityU8CanonicalRevisionAt canonicalOldVisit
      ).generate.initialRestructuringGenerated.occurrence =
      death.locusRootEvent.occurrence :=
  death.revisionReceipt.initialOccurrenceExact

theorem locusWholeLedger_isRevisionFirstWrite
    (death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    (ContributionCapacityU8CanonicalRevisionAt canonicalOldVisit
      ).generate.initialRestructuringGenerated.wholeLedgerWriteBack =
      death.locusRootEvent.wholeLedgerWriteBack :=
  death.revisionReceipt.initialWholeLedgerWriteExact

theorem locusPayment_isRevisionFirstWrite
    (death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    death.revisionReceipt.firstWritePayment =
      sourceGeneratedContributionCapacityU8RuntimePaymentAt
        canonicalOldVisit 0 :=
  rfl

/-! ## Old origin, first empty fibre, and stable later emptiness -/

def inheritedOldOrigin
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :=
  contributionCapacityU8InheritedContributionOrigin canonicalOldVisit

theorem inheritedOrigin_isCapacityCutTarget
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    (contributionCapacityU8InheritedContributionOrigin canonicalOldVisit).1 =
      contributionCapacityU8EmbeddedOldEntry canonicalOldVisit
        (contributionCapacityCutTargetContribution
          (capacityActionRootedAt canonicalOldVisit)) :=
  contributionCapacityU8InheritedOrigin_isCutTarget canonicalOldVisit

theorem inheritedOrigin_notFresh
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    IsEmpty
      (RootDebtFreshAt (CapacityU8NAt canonicalOldVisit)
        (contributionCapacityU8PreRevisionLedger canonicalOldVisit).support
        (contributionCapacityU8InheritedContribution canonicalOldVisit)) :=
  contributionCapacityU8InheritedOrigin_notFresh canonicalOldVisit

theorem firstExactRenewalFibre_isEmpty
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    IsEmpty
      (ExactContributionCapacityU8InheritedRenewalPaymentAt
        canonicalOldVisit 0) :=
  exactContributionCapacityU8InheritedRenewalPayment_isEmpty
    canonicalOldVisit 0

theorem everyU8ExactRenewalFibre_isEmpty
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath)
    (index : Nat) :
    IsEmpty
      (ExactContributionCapacityU8InheritedRenewalPaymentAt
        canonicalOldVisit index) :=
  exactContributionCapacityU8InheritedRenewalPayment_isEmpty
    canonicalOldVisit index

theorem reopeningIngressExactRenewalFibre_isEmpty
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    IsEmpty
      (ExactContributionCapacityReopeningActionRenewalPaymentAt
        canonicalOldVisit 1) :=
  exactContributionCapacityReopeningActionRenewalPayment_isEmpty
    canonicalOldVisit 1

theorem everyReopeningRuntimeExactRenewalFibre_isEmpty
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath)
    (index : Nat) :
    IsEmpty
      (ExactContributionCapacityReopeningRuntimeRenewalPaymentAt
        canonicalOldVisit 1 index) :=
  exactContributionCapacityReopeningRuntimeRenewalPayment_isEmpty
    canonicalOldVisit 1 index

/-! ## Settlement boundary, terminal separation, and later finality -/

def settlementBoundary
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    SourceGeneratedContributionCapacitySettlementBoundaryAt
      canonicalOldVisit 1 :=
  sourceGeneratedContributionCapacitySettlementBoundaryAt canonicalOldVisit 1

theorem settlementIngressStrictRenewalFibre_isEmpty
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    IsEmpty
      (ExactContributionCapacitySettlementIngressStrictRenewalAt
        canonicalOldVisit 1) :=
  exactContributionCapacitySettlementIngressStrictRenewal_isEmpty
    canonicalOldVisit 1

theorem settlementTerminalNativePaymentEdge_isEmpty
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    IsEmpty ((SettlementVAt canonicalOldVisit).NativeWriteAt true) :=
  contributionCapacitySettlementTerminalNativeWrite_isEmpty canonicalOldVisit

theorem settlementTerminalFaithful_inhabited
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    Nonempty ((SettlementVAt canonicalOldVisit).FaithfulTerminalAt true) :=
  contributionCapacitySettlementTerminalFaithful_inhabited canonicalOldVisit

theorem settlementTerminal_noLocalLedgerSuccessor
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    IsEmpty
      (SourceNativeLedgerGeneratedSuccessorAt
        (contributionCapacitySettlementTerminalRootEventAt canonicalOldVisit 1
          ).occurrence
        (contributionCapacitySettlementTerminalRootEventAt canonicalOldVisit 1
          ).wholeLedgerWriteBack) :=
  contributionCapacitySettlementBoundaryTerminal_noLocalSuccessor
    canonicalOldVisit 1

theorem settlementTerminalContributionFinalSettlement_isEmpty
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    IsEmpty
      (SourceNativeRootDebtSettlementAt
        (contributionCapacitySettlementBoundaryTerminalContributionCurrentAt
          canonicalOldVisit 1)) :=
  contributionCapacitySettlementBoundaryTerminalContributionSettlement_isEmpty
    canonicalOldVisit 1

/-- The later A14 joint terminal really is final settlement of its exact
contribution debt.  It is intentionally not identified with the first
arithmetic-empty U8 Payment occurrence. -/
def laterJointContributionFinalSettlement
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    SourceNativeRootDebtSettlementAt
      (contributionCapacityJointSettlementDebtCurrentAt canonicalOldVisit 1
        (0 : Fin 2)) :=
  generatedContributionCapacityJointDebtSettlementAt canonicalOldVisit 1 0

theorem laterJointContributionFinalSettlement_inhabited
    (death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    Nonempty
      (SourceNativeRootDebtSettlementAt
        (contributionCapacityJointSettlementDebtCurrentAt canonicalOldVisit 1
          (0 : Fin 2))) :=
  ⟨death.laterJointContributionFinalSettlement⟩

/-! ## Three non-authoritative numeric coordinates -/

def rootLocalCurrent
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    Nat :=
  0

def actualServiceDepth
    (death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    Nat :=
  contributionCapacityU8PaymentDepthAtCurrent death.rootLocalCurrent

def observerRuntimeTick
    (_death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    Nat :=
  3

@[simp] theorem rootLocalCurrent_eq_zero
    (death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    death.rootLocalCurrent = 0 :=
  rfl

@[simp] theorem actualServiceDepth_eq_two
    (death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    death.actualServiceDepth = 2 :=
  rfl

@[simp] theorem observerRuntimeTick_eq_three
    (death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    death.observerRuntimeTick = 3 :=
  rfl

theorem numericCoordinates_pairwiseDistinct
    (death :
      SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath) :
    death.rootLocalCurrent ≠ death.actualServiceDepth ∧
      death.rootLocalCurrent ≠ death.observerRuntimeTick ∧
      death.actualServiceDepth ≠ death.observerRuntimeTick := by
  simp

end SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath

theorem fullHistoryEarliestArithmeticDeath_hasNoCallerDateHistoryOrFuture :
    True := by
  let death :=
    sourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath
  fail_if_success exact death.date
  fail_if_success exact death.history
  fail_if_success exact death.coverage
  fail_if_success exact death.target
  fail_if_success exact death.future
  fail_if_success exact death.deathRegistry
  trivial

end
end M14SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath.sourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath.SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath.firstExactRenewalFibre_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath.SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath.numericCoordinates_pairwiseDistinct
