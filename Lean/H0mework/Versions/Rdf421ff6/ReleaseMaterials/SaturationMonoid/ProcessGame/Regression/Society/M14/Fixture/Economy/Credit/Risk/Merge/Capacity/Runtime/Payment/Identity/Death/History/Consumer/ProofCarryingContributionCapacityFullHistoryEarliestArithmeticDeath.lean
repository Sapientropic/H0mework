import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Identity.Death.History.Producer.SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Identity.Death.Publication.Consumer.ProofCarryingContributionCapacityDeathFieldPublication

/-!
# Direct consumer of the full-history first arithmetic death

The canonical paid prefix now has one source-generated answer.  The d2
capacity-cut Payment really performs `1 -> 0`.  The causally adjacent d3
self-U8 revision fixes its first write to an exact Payment occurrence whose
old, nonfresh contribution row can only be carried `0 -> 0`; the strict
renewal fibre is therefore empty there and remains empty through U8,
reopening and settlement ingress.

The d9 faithful terminal is not another Payment and is not final settlement
of that contribution: the installed handoff contains a same-debt d10 target.
The later joint terminal is final.  Arithmetic standing death, visible debt
carry and substantive terminal discharge are thus three typed facts rather
than one observer label.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityFullHistoryEarliestArithmeticDeath

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityCutCrossRootPayment
open M14ProofCarryingContributionCapacityCutCrossRootPayment
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8RuntimePayment
open M14SourceGeneratedContributionCapacityU8RevisionNoFreeReceipt
open M14ProofCarryingContributionCapacityU8RevisionNoFreeReceipt
open M14SourceGeneratedContributionCapacityTargetOriginOrBirth
open M14SourceGeneratedContributionCapacityU8InheritedRenewalDeath
open M14SourceGeneratedContributionCapacityReopeningActionPayment
open M14SourceGeneratedContributionCapacityReopeningRuntimePayment
open M14SourceGeneratedContributionCapacityReopeningRenewalDeath
open M14SourceGeneratedContributionCapacitySettlementCompiler
open M14SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceipt
open M14SourceGeneratedContributionCapacitySettlementBoundaryDeath
open M14SourceGeneratedContributionCapacitySettlementSurvivorRuntimePayment
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityEntityRenewalArithmeticDeath
open M14SourceGeneratedContributionCapacityPersistentUnsettledEntity
open M14ProofCarryingContributionCapacityDeathFieldPublication
open M14SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath
open M14SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath.SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath

abbrev CanonicalFullHistoryEarliestArithmeticDeath :=
  SourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath

def canonicalFullHistoryEarliestArithmeticDeath :
    CanonicalFullHistoryEarliestArithmeticDeath :=
  sourceGeneratedContributionCapacityFullHistoryEarliestArithmeticDeath

structure ProofCarryingContributionCapacityFullHistoryEarliestArithmeticDeathCertificate :
    Prop where
  generated : Nonempty CanonicalFullHistoryEarliestArithmeticDeath
  cutRuntime : ProofCarryingContributionCapacityCutCrossRootPayment
  predecessorPayment : Nonempty
    CanonicalContributionCapacityCutCrossRootPayment
  predecessorStrictDisposition :
    (canonicalFullHistoryEarliestArithmeticDeath.predecessorPayment.targetEvent
      ).wholeLedgerWriteBack.entryDisposition
          (initialContribution
            (capacityActionRootedAt
              CanonicalContributionCapacityCutOldVisit)) =
      LedgerEntryDispositionAt.evolved
        (canonicalFullHistoryEarliestArithmeticDeath.predecessorPayment
          ).actionReceipt.strictDebit
  predecessorBudgetOne :
    (initialContribution
      (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
      ).progressBudget = 1
  predecessorTargetBudgetZero :
    (contributionCapacityCutTargetContribution
      (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
      ).progressBudget = 0
  predecessorNextIsRevisionSource :
    thirdTick.next = (jointRuntime.stateAt 3).engine
  revisionRuntime :
    ProofCarryingContributionCapacityU8RevisionNoFreeReceipt
  revisionTickExact : fourthTick = jointRuntime.tickAt 3
  locusOccurrenceIsFirstWrite :
    (ContributionCapacityU8CanonicalRevisionAt canonicalOldVisit
      ).generate.initialRestructuringGenerated.occurrence =
      canonicalFullHistoryEarliestArithmeticDeath.locusRootEvent.occurrence
  locusWholeLedgerIsFirstWrite :
    (ContributionCapacityU8CanonicalRevisionAt canonicalOldVisit
      ).generate.initialRestructuringGenerated.wholeLedgerWriteBack =
      (canonicalFullHistoryEarliestArithmeticDeath.locusRootEvent
        ).wholeLedgerWriteBack
  inheritedOriginIsCutTarget :
    (contributionCapacityU8InheritedContributionOrigin canonicalOldVisit).1 =
      contributionCapacityU8EmbeddedOldEntry canonicalOldVisit
        (contributionCapacityCutTargetContribution
          (capacityActionRootedAt canonicalOldVisit))
  inheritedOriginNotFresh : IsEmpty
    (RootDebtFreshAt (CapacityU8NAt canonicalOldVisit)
      (contributionCapacityU8PreRevisionLedger canonicalOldVisit).support
      (contributionCapacityU8InheritedContribution canonicalOldVisit))
  firstActualPayment : Nonempty
    (SourceGeneratedContributionCapacityU8RuntimePaymentAt
      canonicalOldVisit 0)
  firstExactRenewalEmpty : IsEmpty
    (ExactContributionCapacityU8InheritedRenewalPaymentAt
      canonicalOldVisit 0)
  everyU8ActualPayment : ∀ index : Nat,
    SourceGeneratedContributionCapacityU8RuntimePaymentAt
      canonicalOldVisit index
  everyU8ExactRenewalEmpty : ∀ index : Nat,
    IsEmpty
      (ExactContributionCapacityU8InheritedRenewalPaymentAt
        canonicalOldVisit index)
  reopeningActionPayment : Nonempty
    (ContributionCapacityReopeningActionPaymentAt canonicalOldVisit 1)
  reopeningActionStrictRenewalEmpty : IsEmpty
    (ExactContributionCapacityReopeningActionRenewalPaymentAt
      canonicalOldVisit 1)
  everyReopeningRuntimePayment : ∀ index : Nat,
    SourceGeneratedContributionCapacityReopeningRuntimePaymentAt
      canonicalOldVisit 1 index
  everyReopeningRuntimeStrictRenewalEmpty : ∀ index : Nat,
    IsEmpty
      (ExactContributionCapacityReopeningRuntimeRenewalPaymentAt
        canonicalOldVisit 1 index)
  settlementBoundary :
    ProofCarryingCanonicalContributionCapacitySettlementBoundaryDeath
  settlementIngressStrictRenewalEmpty : IsEmpty
    (ExactContributionCapacitySettlementIngressStrictRenewalAt
      canonicalOldVisit 1)
  terminalNativePaymentEdgeEmpty : IsEmpty
    ((SettlementVAt canonicalOldVisit).NativeWriteAt true)
  terminalFaithfulInhabited : Nonempty
    ((SettlementVAt canonicalOldVisit).FaithfulTerminalAt true)
  terminalNoLocalLedgerSuccessor : IsEmpty
    (SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacitySettlementTerminalRootEventAt canonicalOldVisit 1
        ).occurrence
      (contributionCapacitySettlementTerminalRootEventAt canonicalOldVisit 1
        ).wholeLedgerWriteBack)
  terminalSameDebtTargetInhabited : Nonempty
    (SourceNativeRootDebtTargetAt
      (contributionCapacitySettlementBoundaryTerminalContributionCurrentAt
        canonicalOldVisit 1))
  terminalContributionFinalSettlementEmpty : IsEmpty
    (SourceNativeRootDebtSettlementAt
      (contributionCapacitySettlementBoundaryTerminalContributionCurrentAt
        canonicalOldVisit 1))
  laterJointContributionFinalSettlementInhabited : Nonempty
    (SourceNativeRootDebtSettlementAt
      (contributionCapacityJointSettlementDebtCurrentAt canonicalOldVisit 1
        (0 : Fin 2)))
  coordinatesRemainDistinct :
    canonicalFullHistoryEarliestArithmeticDeath.rootLocalCurrent ≠
        canonicalFullHistoryEarliestArithmeticDeath.actualServiceDepth ∧
      canonicalFullHistoryEarliestArithmeticDeath.rootLocalCurrent ≠
        canonicalFullHistoryEarliestArithmeticDeath.observerRuntimeTick ∧
      canonicalFullHistoryEarliestArithmeticDeath.actualServiceDepth ≠
        canonicalFullHistoryEarliestArithmeticDeath.observerRuntimeTick
  survivorTailActualPayment : ∀ index : Nat,
    SourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt index
  survivorTailStrictRenewalEmpty : ∀ index : Nat,
    IsEmpty
      (ExactContributionEntityRenewalPaymentAt
        (sourceGeneratedPersistentUnsettledContributionEntityAt index))
  standingArithmeticDeath :
    ProofCarryingContributionEntityRenewalArithmeticDeathCertificate
  laterSubstantiveDeathPublication :
    ProofCarryingContributionCapacityDeathFieldPublicationCertificate

theorem proofCarryingContributionCapacityFullHistoryEarliestArithmeticDeath :
    ProofCarryingContributionCapacityFullHistoryEarliestArithmeticDeathCertificate := by
  let death := canonicalFullHistoryEarliestArithmeticDeath
  exact
    { generated := ⟨death⟩
      cutRuntime := proofCarryingContributionCapacityCutCrossRootPayment
      predecessorPayment := ⟨death.predecessorPayment⟩
      predecessorStrictDisposition :=
        death.predecessorDisposition_isStrictDebit
      predecessorBudgetOne := death.predecessorSourceBudget_eq_one
      predecessorTargetBudgetZero := death.predecessorTargetBudget_eq_zero
      predecessorNextIsRevisionSource :=
        death.predecessorNext_isRuntimeStateThree
      revisionRuntime :=
        proofCarryingContributionCapacityU8RevisionNoFreeReceipt
      revisionTickExact := death.revisionTick_isRuntimeStateThreeTick
      locusOccurrenceIsFirstWrite :=
        death.locusOccurrence_isRevisionFirstWrite
      locusWholeLedgerIsFirstWrite :=
        death.locusWholeLedger_isRevisionFirstWrite
      inheritedOriginIsCutTarget := death.inheritedOrigin_isCapacityCutTarget
      inheritedOriginNotFresh := death.inheritedOrigin_notFresh
      firstActualPayment :=
        ⟨sourceGeneratedContributionCapacityU8RuntimePaymentAt
          canonicalOldVisit 0⟩
      firstExactRenewalEmpty := death.firstExactRenewalFibre_isEmpty
      everyU8ActualPayment := fun index =>
        sourceGeneratedContributionCapacityU8RuntimePaymentAt
          canonicalOldVisit index
      everyU8ExactRenewalEmpty := death.everyU8ExactRenewalFibre_isEmpty
      reopeningActionPayment :=
        ⟨sourceGeneratedContributionCapacityReopeningActionPaymentAt
          canonicalOldVisit 1⟩
      reopeningActionStrictRenewalEmpty :=
        death.reopeningIngressExactRenewalFibre_isEmpty
      everyReopeningRuntimePayment := fun index =>
        sourceGeneratedContributionCapacityReopeningRuntimePaymentAt
          canonicalOldVisit 1 index
      everyReopeningRuntimeStrictRenewalEmpty :=
        death.everyReopeningRuntimeExactRenewalFibre_isEmpty
      settlementBoundary :=
        proofCarryingCanonicalContributionCapacitySettlementBoundaryDeath
      settlementIngressStrictRenewalEmpty :=
        death.settlementIngressStrictRenewalFibre_isEmpty
      terminalNativePaymentEdgeEmpty :=
        death.settlementTerminalNativePaymentEdge_isEmpty
      terminalFaithfulInhabited :=
        death.settlementTerminalFaithful_inhabited
      terminalNoLocalLedgerSuccessor :=
        death.settlementTerminal_noLocalLedgerSuccessor
      terminalSameDebtTargetInhabited :=
        ⟨contributionCapacitySettlementBoundarySurvivorContributionTargetAt
          canonicalOldVisit 1⟩
      terminalContributionFinalSettlementEmpty :=
        death.settlementTerminalContributionFinalSettlement_isEmpty
      laterJointContributionFinalSettlementInhabited :=
        death.laterJointContributionFinalSettlement_inhabited
      coordinatesRemainDistinct := death.numericCoordinates_pairwiseDistinct
      survivorTailActualPayment :=
        sourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt
      survivorTailStrictRenewalEmpty := fun index =>
        exactContributionEntityRenewalPayment_isEmpty
          (sourceGeneratedPersistentUnsettledContributionEntityAt index)
      standingArithmeticDeath :=
        proofCarryingContributionEntityRenewalArithmeticDeath
      laterSubstantiveDeathPublication :=
        proofCarryingContributionCapacityDeathFieldPublication }

/-! ## Independent negative controls -/

theorem depth_budget_payment_terminal_orSettlement_cannot_retype_asFullHistoryDeath :
    True := by
  let firstPayment :=
    sourceGeneratedContributionCapacityU8RuntimePaymentAt canonicalOldVisit 0
  let terminal :=
    sourceGeneratedContributionCapacitySettlementTerminalNoFreeReceiptAt
      canonicalOldVisit 1
  let finalSettlement :=
    canonicalFullHistoryEarliestArithmeticDeath
      |>.laterJointContributionFinalSettlement
  fail_if_success exact
    ((3 : Nat) : CanonicalFullHistoryEarliestArithmeticDeath)
  fail_if_success exact
    ((0 : Nat) : CanonicalFullHistoryEarliestArithmeticDeath)
  fail_if_success exact
    (firstPayment : CanonicalFullHistoryEarliestArithmeticDeath)
  fail_if_success exact
    (firstPayment.actualService : CanonicalFullHistoryEarliestArithmeticDeath)
  fail_if_success exact
    (terminal : CanonicalFullHistoryEarliestArithmeticDeath)
  fail_if_success exact
    (finalSettlement : CanonicalFullHistoryEarliestArithmeticDeath)
  trivial

theorem firstEmpty_doesNotEraseActualPayment :
    Nonempty
        (SourceGeneratedContributionCapacityU8RuntimePaymentAt
          canonicalOldVisit 0) ∧
      IsEmpty
        (ExactContributionCapacityU8InheritedRenewalPaymentAt
          canonicalOldVisit 0) :=
  ⟨⟨sourceGeneratedContributionCapacityU8RuntimePaymentAt canonicalOldVisit 0⟩,
    canonicalFullHistoryEarliestArithmeticDeath
      |>.firstExactRenewalFibre_isEmpty⟩

theorem d9Terminal_doesNotEraseSameDebtTarget :
    Nonempty ((SettlementVAt canonicalOldVisit).FaithfulTerminalAt true) ∧
      Nonempty
        (SourceNativeRootDebtTargetAt
          (contributionCapacitySettlementBoundaryTerminalContributionCurrentAt
            canonicalOldVisit 1)) ∧
      IsEmpty
        (SourceNativeRootDebtSettlementAt
          (contributionCapacitySettlementBoundaryTerminalContributionCurrentAt
            canonicalOldVisit 1)) :=
  ⟨contributionCapacitySettlementTerminalFaithful_inhabited canonicalOldVisit,
    ⟨contributionCapacitySettlementBoundarySurvivorContributionTargetAt
      canonicalOldVisit 1⟩,
    contributionCapacitySettlementBoundaryTerminalContributionSettlement_isEmpty
      canonicalOldVisit 1⟩

end
end M14ProofCarryingContributionCapacityFullHistoryEarliestArithmeticDeath
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityFullHistoryEarliestArithmeticDeath.proofCarryingContributionCapacityFullHistoryEarliestArithmeticDeath
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityFullHistoryEarliestArithmeticDeath.depth_budget_payment_terminal_orSettlement_cannot_retype_asFullHistoryDeath
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityFullHistoryEarliestArithmeticDeath.firstEmpty_doesNotEraseActualPayment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityFullHistoryEarliestArithmeticDeath.d9Terminal_doesNotEraseSameDebtTarget
