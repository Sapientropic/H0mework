import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Producer.SourceGeneratedContributionCapacityNewCompatibleFutureBirth
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Payment.Action.Producer.SourceGeneratedContributionCapacitySettlementCrossRootPayment
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Consumer.SourceGeneratedContributionCapacitySettlementConsumer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Payment.Producer.SourceGeneratedContributionCapacityPostSettlementOccurrencePayment

/-!
# Post-settlement compatible future birth

The canonical macro branch leaves reopening current three through the actual
settlement action, consumes the generated-residual terminal receipt, settles
both inherited survivor rows, and enters the existing empty-ledger
post-settlement root.  Every reachable post-root event then generates its own
payment, external liability, successor and bearer-aligned independent exit.

The future-birth token is field-free.  It introduces no actor, root, ledger,
receipt registry, schedule or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityPostSettlementFutureBirth

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open UBI.Capacity
open M3FiniteExchangeFixture
open M14UBIExitCapacityFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth
open M14SourceGeneratedContributionCapacitySettlementCrossRootPayment
open M14SourceGeneratedContributionCapacitySettlementConsumer
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14UBIPeriodicActualServiceCapacity

def contributionCapacityPostSettlementFutureBirthCurrentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Nat :=
  contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
    index

def contributionCapacityPostSettlementFutureBirthRootEventAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
    index

def contributionCapacityPostSettlementFutureBirthActualExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
        sourceIndex index) :=
  contributionCapacityPostSettlementActualExitOfRootEventAt oldVisit
    sourceIndex index
    (contributionCapacityPostSettlementFutureBirthRootEventAt oldVisit
      sourceIndex index)

/-- Installed face at the exact reachable post-root visit. -/
def contributionCapacityPostSettlementFutureBirthBearerExitFaceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeRootSemanticFaceAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index) :=
  contributionCapacityPostSettlementBirthBearerExitFaceAt oldVisit
    sourceIndex
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index)

/-- The bearer exit is read only from the existing post-root projection. -/
def contributionCapacityPostSettlementFutureBirthInstalledBearerExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  contributionCapacityPostSettlementRootGeneratedBirthBearerExitAt oldVisit
    sourceIndex
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index)

def contributionCapacityPostSettlementFutureBirthBearerExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  Classical.choice
    (contributionCapacityPostSettlementFutureBirthInstalledBearerExitAt
      oldVisit sourceIndex index).down

/-- One actual macro-branch future birth after both settlement stages. -/
inductive SourceGeneratedContributionCapacityPostSettlementFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 20
  | private generated

def sourceGeneratedContributionCapacityPostSettlementFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex index :=
  .generated

namespace SourceGeneratedContributionCapacityPostSettlementFutureBirthAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (futureBirth :
    SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex index)

theorem eq_generated :
    futureBirth =
      sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index := by
  cases futureBirth
  rfl

/-- The source of the macro bridge is the actual reopening-current-three
future birth, not an unchosen micro successor. -/
def reopeningFutureBirth :
    SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
      sourceIndex 2 := by
  cases futureBirth
  exact sourceGeneratedContributionCapacityNewCompatibleFutureBirthAt
    oldVisit sourceIndex 2

def settlementCrossRootPayment :
    CanonicalContributionCapacitySettlementCrossRootPaymentAt oldVisit
      sourceIndex := by
  cases futureBirth
  exact sourceGeneratedContributionCapacitySettlementCrossRootPaymentAt
    oldVisit sourceIndex

/-- The future birth at reopening current three and the settlement action
consume one compiler-native payment object, not two parallel witnesses. -/
theorem reopeningBirthPayment_eq_settlementActionSource :
    (reopeningFutureBirth futureBirth).runtimePayment =
      (settlementCrossRootPayment futureBirth).sourcePayment :=
  rfl

/-- The paid macro next is exactly the action-generated settlement root. -/
theorem settlementActionMacroNext_exact :
    (settlementCrossRootPayment futureBirth).nextPaidBy =
      ⟨(generatedContributionCapacitySettlementPaidActionAt oldVisit
          sourceIndex).target.TargetV,
        (generatedContributionCapacitySettlementPaidActionAt oldVisit
          sourceIndex).target.targetRoot.toAuthoritativeRoot,
        (generatedContributionCapacitySettlementPaidActionAt oldVisit
          sourceIndex).target.targetVisit⟩ :=
  (settlementCrossRootPayment futureBirth).nextPaidBy_exact

/-- Exact prior residual settlement.  The post-root token consumes this
receipt instead of continuing to report the residual as carried. -/
def residualSettlement :
    SourceNativeRootDebtSettlementAt
      (settlementResidualCurrentAt oldVisit sourceIndex) := by
  cases futureBirth
  exact generatedResidualSettlementAt oldVisit sourceIndex

def residualTerminalReceipt :
    LedgerEntryTerminalAt (ReopeningNAt oldVisit)
      (settlementResidualCurrentAt oldVisit sourceIndex).entry := by
  cases futureBirth
  exact generatedResidualTerminalReceiptAt oldVisit sourceIndex

/-- The receipt closes the exact row that the source future birth still saw
as carried at reopening current three. -/
theorem carriedResidual_eq_settlementOrigin :
    (reopeningFutureBirth futureBirth).residualCarry.sourceEntry =
      (settlementResidualCurrentAt oldVisit sourceIndex).entry :=
  rfl

theorem residualTerminalReceipt_exact :
    residualTerminalReceipt futureBirth =
      (residualSettlement futureBirth).receipt :=
  rfl

/-- Both inherited survivor rows also receive their own terminal receipts
before the empty handoff. -/
def survivorDebtSettlement (entryIndex : Fin 2) :
    SourceNativeRootDebtSettlementAt
      (contributionCapacityJointSettlementDebtCurrentAt oldVisit sourceIndex
        entryIndex) := by
  cases futureBirth
  exact generatedContributionCapacityJointDebtSettlementAt oldVisit
    sourceIndex entryIndex

theorem jointSettlementComplete
    (_futureBirth :
      SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index) :
    ProofCarryingContributionCapacityJointSettlementCertificateAt oldVisit
      sourceIndex := by
  exact generatedContributionCapacityJointSettlement_closesBoth_renewsSociety
    oldVisit sourceIndex

def postRootEvent := by
  cases futureBirth
  exact contributionCapacityPostSettlementFutureBirthRootEventAt oldVisit
    sourceIndex index

def actualExit : PeriodicActualServiceExitAt
    (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
      sourceIndex index) := by
  cases futureBirth
  exact contributionCapacityPostSettlementFutureBirthActualExitAt oldVisit
    sourceIndex index

def postPayment :
    CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex index := by
  cases futureBirth
  exact sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
    oldVisit sourceIndex index

def installedBearerExitFace := by
  cases futureBirth
  exact contributionCapacityPostSettlementFutureBirthBearerExitFaceAt
    oldVisit sourceIndex index

def installedBearerExitAuthority := by
  cases futureBirth
  exact contributionCapacityPostSettlementFutureBirthInstalledBearerExitAt
    oldVisit sourceIndex index

def bearerExit := by
  cases futureBirth
  exact contributionCapacityPostSettlementFutureBirthBearerExitAt oldVisit
    sourceIndex index

set_option linter.defProp false in
def externalLiability := (postPayment futureBirth).liability

def nextPaidOccurrence := (postPayment futureBirth).nextPaidBy

@[simp] theorem current_exact :
    contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
        sourceIndex index =
      contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex +
        index :=
  contributionCapacityPostSettlementReachableCurrentAt_exact oldVisit
    sourceIndex index

theorem actualExitFromNativeWrite_exact :
    actualExit futureBirth =
      Classical.choice (postPayment futureBirth).write.down :=
  (postPayment futureBirth).actualExitFromWrite

theorem bearerExit_fromInstalledFace :
    bearerExit futureBirth =
      Classical.choice (installedBearerExitAuthority futureBirth).down :=
  rfl

theorem bearerExitPayment_exact :
    (bearerExit futureBirth).existingPaymentOccurrence =
      (actualExit futureBirth).paymentOccurrence :=
  (bearerExit futureBirth).existingPaymentOccurrence_eq

theorem bearerExitService_exact :
    (bearerExit futureBirth).existingActualSettlement =
      (actualExit futureBirth).actualSettlement :=
  (bearerExit futureBirth).existingActualSettlement_eq

/-- Payment counterparty, exit worker and the original admitted birth bearer
remain the same existing `.t1` across the empty handoff. -/
theorem paymentWorkerBirthBearer_exact :
    PurchasingPowerStandingAt.counterparty
        birthBearerExitCapacityProgram.purchasingPowerStanding =
        birthBearerWorker ∧
      exchangeLaw.bearerOfActor birthBearerWorker =
        ((reopeningFutureBirth futureBirth).birthAdmission).obligation.bearer :=
  (reopeningFutureBirth futureBirth).paymentWorkerBirthBearer_exact

theorem refusalCapable_nonWork_contract
    (_futureBirth :
      SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index) :
    ExitFutureCode.work ∉
        birthBearerExitRelationCompiler.futureCodesAt
          birthBearerEmploymentRelation .target ∧
      birthBearerEmploymentRelation ≠
        birthBearerIndependentExitRelation ∧
      Nonempty (birthBearerExitRelationCompiler.FutureContinuationAt
        birthBearerIndependentExitRelation.1 .target ExitFutureCode.leave) ∧
      ¬ birthBearerExitRelationCompiler.futureIdle ExitFutureCode.leave ∧
      ¬ birthBearerNoCapture.Captures ExitFutureCode.leave ∧
      ExitFutureCode.leave ≠ ExitFutureCode.work :=
  M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth.SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt.refusalCapable_nonWork_contract

theorem exitCapacityOne_captureZero
    (_futureBirth :
      SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index) :
    (birthBearerGeometryCompilerAt
        (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
          sourceIndex index)).actionableExitCapacity = 1 ∧
      (birthBearerCapturedGeometryCompilerAt
        (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
          sourceIndex index)).actionableExitCapacity = 0 :=
  ⟨(bearerExit _futureBirth).exactCapacity,
    (bearerExit _futureBirth).capturedCapacity⟩

theorem localLedgerEmpty :
    IsEmpty
      (OpenResponsibilityAt (JointSettlementNAt oldVisit)
        (postRootEvent futureBirth).occurrence.1) :=
  (postPayment futureBirth).occurrenceLocalLedgerEmpty

theorem externalLiabilityPresent :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (actualExit futureBirth)) :=
  ⟨(externalLiability futureBirth).sourceOwnedResidual,
    (externalLiability futureBirth).rootConsumer⟩

@[simp] theorem nextPaidOccurrence_exact :
    nextPaidOccurrence futureBirth =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
            sourceIndex index +
          1) :=
  rfl

/-- The reopening-current-three birth occurrence is not replayed after the
two settlement stages. -/
theorem reopeningAndPostSettlementActualExitOccurrences_distinct :
    periodicActualServiceExitOccurrenceAt
        (contributionCapacityFutureBirthDepth sourceIndex 2) ≠
      periodicActualServiceExitOccurrenceAt
        (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
          sourceIndex index) := by
  intro equality
  have depth_eq := periodicActualServiceExitOccurrenceAt_injective equality
  rw [current_exact] at depth_eq
  unfold contributionCapacityFutureBirthDepth at depth_eq
  unfold contributionCapacityPostSettlementRenewalInitialCurrentAt at depth_eq
  unfold contributionCapacitySettlementSurvivorInitialCurrentAt at depth_eq
  unfold contributionCapacityReopeningDepthAtCurrent at depth_eq
  unfold contributionCapacityReopeningDepthAt at depth_eq
  omega

end SourceGeneratedContributionCapacityPostSettlementFutureBirthAt

/-! ## Pointwise canonical macro-history cofinality -/

/-- A generated later birth beyond one arbitrary absolute macro-history
boundary.  This is a pointwise carrier, not a stored future table. -/
structure SourceGeneratedLaterContributionCapacityMacroFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 21 where
  private mk ::
  index : Nat
  futureBirth :
    SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex index
  later : boundary <
    contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
      sourceIndex index

def sourceGeneratedLaterContributionCapacityMacroFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedLaterContributionCapacityMacroFutureBirthAt oldVisit
      sourceIndex boundary where
  index := boundary + 1
  futureBirth :=
    sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex (boundary + 1)
  later := by
    unfold contributionCapacityPostSettlementFutureBirthCurrentAt
    rw [contributionCapacityPostSettlementReachableCurrentAt_exact]
    omega

/-- Every finite absolute macro-history boundary has a strictly later actual
post-settlement future birth. -/
theorem sourceGeneratedContributionCapacityFutureBirth_cofinalOnCanonicalMacroHistory
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ∀ boundary : Nat,
      Nonempty
        (SourceGeneratedLaterContributionCapacityMacroFutureBirthAt oldVisit
          sourceIndex boundary) :=
  fun boundary =>
    ⟨sourceGeneratedLaterContributionCapacityMacroFutureBirthAt oldVisit
      sourceIndex boundary⟩

theorem contributionCapacityPostSettlementFutureBirth_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let futureBirth :=
    sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex index
  fail_if_success exact futureBirth.actor
  fail_if_success exact futureBirth.bearer
  fail_if_success exact futureBirth.participant
  fail_if_success exact futureBirth.score
  fail_if_success exact futureBirth.target
  fail_if_success exact futureBirth.future
  fail_if_success exact futureBirth.schedule
  fail_if_success exact futureBirth.registry
  trivial

end
end M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementFutureBirth.sourceGeneratedContributionCapacityPostSettlementFutureBirthAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementFutureBirth.SourceGeneratedContributionCapacityPostSettlementFutureBirthAt.paymentWorkerBirthBearer_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementFutureBirth.sourceGeneratedContributionCapacityFutureBirth_cofinalOnCanonicalMacroHistory
