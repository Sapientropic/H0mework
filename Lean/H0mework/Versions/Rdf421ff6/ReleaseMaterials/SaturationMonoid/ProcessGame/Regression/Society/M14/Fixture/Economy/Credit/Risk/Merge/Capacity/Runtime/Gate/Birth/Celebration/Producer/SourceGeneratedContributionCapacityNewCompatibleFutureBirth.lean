import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Producer.SourceGeneratedContributionCapacityTargetOriginOrBirth
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Bearer.Producer.SourceGeneratedContributionCapacityBirthBearerExit
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Payment.Action.Reopening.Producer.SourceGeneratedContributionCapacityReopeningActionPayment
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Payment.Producer.SourceGeneratedContributionCapacityReopeningRuntimePayment

/-!
# New compatible future birth from one admitted residual

The capacity-U8 residual is first admitted with its complete birth authority.
The existing sequential reopening action then transports that exact row into
the generated reopening root.  At each positive reopening current, one exact
event simultaneously generates:

* a compiler-native actual-service payment and successor;
* the canonical carried disposition of the residual row;
* the later residual authority and independent answer consumer; and
* an employment-independent, uncaptured exit for the residual's existing
  `.t1` bearer.

The token is field-free and source-indexed.  It contains no participant,
score, target choice, future table, second root, or second ledger.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open UBI.Capacity
open M3FiniteExchangeFixture
open M14UBIExitCapacityFixture
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityTargetOriginOrBirth
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacityReopeningActionSource
open M14SourceGeneratedSequentialContributionCapacityReopening
open M14SourceGeneratedContributionCapacityReopeningState
open M14SourceGeneratedContributionCapacityReopeningResidualCarry
open M14SourceGeneratedContributionCapacityReopeningActionPayment
open M14SourceGeneratedContributionCapacityReopeningRuntimePayment
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14UBIPeriodicActualServiceCapacity

def contributionCapacityFutureBirthDepth
    (sourceIndex index : Nat) : Nat :=
  contributionCapacityReopeningDepthAtCurrent sourceIndex (index + 1)

/-- The actual exit is selected only from the native write of this exact
positive reopening event.  Subsingleton uniqueness later removes proof-choice
ambiguity without storing a schedule. -/
def contributionCapacityFutureBirthActualExitAt
    (_oldVisit : OldVisit) (sourceIndex index : Nat) :
    PeriodicActualServiceExitAt
      (contributionCapacityFutureBirthDepth sourceIndex index) :=
  periodicActualServiceExitAt
    (contributionCapacityFutureBirthDepth sourceIndex index)

/-- Installed dependent face of the exact positive reopening occurrence.
The bearer-aligned exit is therefore root authority, not a post-hoc join. -/
def contributionCapacityFutureBirthBearerExitFaceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeRootSemanticFaceAt
      (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningRootAt
        oldVisit sourceIndex)
      (contributionCapacityReopenedVisitAt oldVisit sourceIndex index) where
  projection := ContributionCapacityReopeningProjection.birthBearerExit
  active := PUnit.unit
  classifier_eq := rfl

def contributionCapacityFutureBirthInstalledBearerExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PLift (Nonempty
      (SourceGeneratedContributionCapacityBirthBearerExitAt
        (contributionCapacityFutureBirthDepth sourceIndex index)
        (contributionCapacityFutureBirthActualExitAt oldVisit sourceIndex
          index))) := by
  have installed :=
    contributionCapacityReopeningRootGeneratedBirthBearerExitAt oldVisit
      sourceIndex
      (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
        oldVisit sourceIndex)
      (contributionCapacityReopenedVisitAt oldVisit sourceIndex index)
  have current_eq :
      (contributionCapacityReopenedVisitAt oldVisit sourceIndex
        index).current = index + 1 :=
    contributionCapacityReopeningVisit_current_exact oldVisit sourceIndex
      (index + 1)
  rw [current_eq] at installed
  simpa [contributionCapacityFutureBirthDepth,
    contributionCapacityFutureBirthActualExitAt] using installed

def contributionCapacityFutureBirthResidualCarryAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedReopeningResidualCarryAt oldVisit sourceIndex
      (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
        oldVisit sourceIndex) index :=
  contributionCapacityReopeningRuntimeResidualCarryAt oldVisit sourceIndex
    index

def contributionCapacityFutureBirthBearerExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedContributionCapacityBirthBearerExitAt
      (contributionCapacityFutureBirthDepth sourceIndex index)
      (contributionCapacityFutureBirthActualExitAt oldVisit sourceIndex
        index) :=
  Classical.choice
    (contributionCapacityFutureBirthInstalledBearerExitAt oldVisit sourceIndex
      index).down

/-- One later, residual-accounted and bearer-aligned compatible future.
All authority is recomputed from the three numeric source indices. -/
inductive SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 20
  | private generated

def sourceGeneratedContributionCapacityNewCompatibleFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
      sourceIndex index :=
  .generated

namespace SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (futureBirth :
    SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
      sourceIndex index)

theorem eq_generated :
    futureBirth =
      sourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
        sourceIndex index := by
  cases futureBirth
  rfl

def birthAdmission :
    ExactGeneratedContributionCapacityResidualBirthAdmissionAt oldVisit := by
  cases futureBirth
  exact sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit

/-- The already certified cross-root action is the only bridge from the U8
birth world into the reopening world. -/
def reopeningActionPayment :
    ContributionCapacityReopeningActionPaymentAt oldVisit sourceIndex := by
  cases futureBirth
  exact sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
    sourceIndex

set_option linter.defProp false in
def runtimePayment :
    SourceGeneratedContributionCapacityReopeningRuntimePaymentAt oldVisit
      sourceIndex index := by
  cases futureBirth
  exact sourceGeneratedContributionCapacityReopeningRuntimePaymentAt oldVisit
    sourceIndex index

def laterRootEvent := by
  cases futureBirth
  exact contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
    sourceIndex index

def actualExit : PeriodicActualServiceExitAt
    (contributionCapacityFutureBirthDepth sourceIndex index) := by
  cases futureBirth
  exact contributionCapacityFutureBirthActualExitAt oldVisit sourceIndex index

theorem runtimePaymentGeneratesActualExit
    (_futureBirth :
      SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
        sourceIndex index) :
    Nonempty (PeriodicActualServiceExitAt
      (contributionCapacityFutureBirthDepth sourceIndex index)) := by
  have generated :=
    (contributionCapacityReopeningRuntimePaymentAt oldVisit sourceIndex
      index).down
  rw [contributionCapacityReopeningRuntimePaymentCurrentAt_exact] at generated
  exact generated

theorem runtimePaymentChoice_eq_actualExit :
    Classical.choice (runtimePaymentGeneratesActualExit futureBirth) =
      actualExit futureBirth :=
  periodicActualServiceExitAt_eq_canonical _

def bearerExit :
    SourceGeneratedContributionCapacityBirthBearerExitAt
      (contributionCapacityFutureBirthDepth sourceIndex index)
      (actualExit futureBirth) := by
  cases futureBirth
  exact contributionCapacityFutureBirthBearerExitAt oldVisit sourceIndex index

def installedBearerExitFace := by
  cases futureBirth
  exact contributionCapacityFutureBirthBearerExitFaceAt oldVisit sourceIndex
    index

def installedBearerExitAuthority :
    PLift (Nonempty
      (SourceGeneratedContributionCapacityBirthBearerExitAt
        (contributionCapacityFutureBirthDepth sourceIndex index)
        (actualExit futureBirth))) := by
  cases futureBirth
  exact contributionCapacityFutureBirthInstalledBearerExitAt oldVisit
    sourceIndex index

theorem bearerExit_fromInstalledFace :
    bearerExit futureBirth =
      Classical.choice (installedBearerExitAuthority futureBirth).down :=
  rfl

def residualCarry :
    SourceGeneratedReopeningResidualCarryAt oldVisit sourceIndex
      (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
        oldVisit sourceIndex) index := by
  cases futureBirth
  exact contributionCapacityFutureBirthResidualCarryAt oldVisit sourceIndex
    index

def laterAuthority := by
  cases futureBirth
  exact contributionCapacityReopenedAuthorityAt oldVisit sourceIndex index

def laterConsumer := by
  cases futureBirth
  exact contributionCapacityReopenedAnswerConsumerAt oldVisit sourceIndex index

def laterCompilation := by
  cases futureBirth
  exact contributionCapacityReopenedCompilationAt oldVisit sourceIndex index

def paymentOccurrence := (actualExit futureBirth).paymentOccurrence

def actualService := (actualExit futureBirth).actualSettlement

def feasibleExit := (bearerExit futureBirth).feasibleEdge

def actionableRenewal := (bearerExit futureBirth).actionableRenewal

def nextPaidOccurrence := by
  cases futureBirth
  exact contributionCapacityReopeningEmitted oldVisit sourceIndex
    (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
      oldVisit sourceIndex)
    (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit sourceIndex
      index + 1)

@[simp] theorem current_exact :
    contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit sourceIndex
        index =
      index + 1 :=
  contributionCapacityReopeningRuntimePaymentCurrentAt_exact oldVisit
    sourceIndex index

@[simp] theorem globalDepth_exact :
    contributionCapacityFutureBirthDepth sourceIndex index =
      contributionCapacityReopeningDepthAt sourceIndex + (index + 1) :=
  rfl

theorem runtimePayment_contains_residualCarry
    (_futureBirth :
      SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
        sourceIndex index) :
    Nonempty
      (SourceGeneratedReopeningResidualCarryAt oldVisit sourceIndex
        (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
          oldVisit sourceIndex) index) :=
  (runtimePayment _futureBirth).residualCarry

theorem laterRootEvent_entry_eq_residualCarry :
      contributionCapacityReopeningCurrentEntryAt oldVisit
        (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
          sourceIndex index) (2 : Fin 3) =
      (residualCarry futureBirth).sourceEntry := by
  rfl

theorem residualCompilerDisposition_exact :
    ((contributionCapacityReopeningLedgerCompiler oldVisit sourceIndex
      (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
          oldVisit sourceIndex)).compile
      (residualCarry futureBirth).sourceOccurrence).entryDisposition
        (residualCarry futureBirth).sourceEntry =
      .evolved (residualCarry futureBirth).evolution :=
  (residualCarry futureBirth).compilerDisposition_exact

theorem residualFoldDestination_exact :
    (reopeningResidualCarryWholeEvolutionAt oldVisit sourceIndex
      (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
        oldVisit sourceIndex) index).destination
        (residualCarry futureBirth).sourceEntry =
      ⟨(residualCarry futureBirth).targetEntry,
        (residualCarry futureBirth).evolution⟩ :=
  (residualCarry futureBirth).foldDestination_exact

theorem residualLineage_preserved :
    (ReopeningNAt oldVisit).lineageAt
        (residualCarry futureBirth).sourceOccurrence.1 =
      (ReopeningNAt oldVisit).lineageAt
        (contributionCapacityReopeningEmitted oldVisit sourceIndex
          (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
            oldVisit sourceIndex) (index + 2)).1 :=
  (residualCarry futureBirth).lineage_preserved

theorem residualClaim_preserved :
    (residualCarry futureBirth).sourceEntry.claim =
      (residualCarry futureBirth).targetEntry.claim :=
  (residualCarry futureBirth).claim_preserved

theorem residualBudgets_zero :
    (residualCarry futureBirth).sourceEntry.progressBudget = 0 ∧
      (residualCarry futureBirth).targetEntry.progressBudget = 0 :=
  ⟨(residualCarry futureBirth).sourceEntry_budget_zero,
    (residualCarry futureBirth).targetEntry_budget_zero⟩

/-- The person who receives the payment standing, the exit worker and the
birth obligation bearer are one existing `.t1` actor/bearer. -/
theorem paymentWorkerBirthBearer_exact :
    PurchasingPowerStandingAt.counterparty
        birthBearerExitCapacityProgram.purchasingPowerStanding =
        birthBearerWorker ∧
      exchangeLaw.bearerOfActor birthBearerWorker =
        (birthAdmission futureBirth).obligation.bearer := by
  exact ⟨birthBearerProgramStanding_counterparty_exact,
    birthBearerWorker_bearer_exact.trans
      (birthAdmission futureBirth).bearerExisting.symm⟩

theorem actualExitPayment_exact :
    (bearerExit futureBirth).existingPaymentOccurrence =
      (actualExit futureBirth).paymentOccurrence :=
  (bearerExit futureBirth).existingPaymentOccurrence_eq

theorem actualService_exact :
    (bearerExit futureBirth).existingActualSettlement =
      (actualExit futureBirth).actualSettlement :=
  (bearerExit futureBirth).existingActualSettlement_eq

/-- Structural voluntariness: the generated future is a non-idle,
uncaptured `leave` continuation in a relation distinct from employment after
the employment `work` continuation is absent.  No affective state is claimed. -/
theorem refusalCapable_nonWork_contract :
    ExitFutureCode.work ∉
        birthBearerExitRelationCompiler.futureCodesAt
          birthBearerEmploymentRelation .target ∧
      birthBearerEmploymentRelation ≠
        birthBearerIndependentExitRelation ∧
      Nonempty (birthBearerExitRelationCompiler.FutureContinuationAt
        birthBearerIndependentExitRelation.1 .target ExitFutureCode.leave) ∧
      ¬ birthBearerExitRelationCompiler.futureIdle ExitFutureCode.leave ∧
      ¬ birthBearerNoCapture.Captures ExitFutureCode.leave ∧
      ExitFutureCode.leave ≠ ExitFutureCode.work := by
  exact ⟨birthBearerWork_target_absent,
    birthBearerEmployment_ne_independentExit, ⟨PUnit.unit⟩,
    by simp [birthBearerExitRelationCompiler],
    by simp [birthBearerNoCapture], by decide⟩

theorem exitCapacityOne_captureZero
    (_futureBirth :
      SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
        sourceIndex index) :
    (birthBearerGeometryCompilerAt
        (contributionCapacityFutureBirthDepth sourceIndex index)
      ).actionableExitCapacity = 1 ∧
      (birthBearerCapturedGeometryCompilerAt
        (contributionCapacityFutureBirthDepth sourceIndex index)
      ).actionableExitCapacity = 0 :=
  ⟨(bearerExit _futureBirth).exactCapacity,
    (bearerExit _futureBirth).capturedCapacity⟩

/-- The action-period exit cannot be replayed as this later future birth. -/
theorem actionAndFutureActualExitOccurrences_distinct :
    periodicActualServiceExitOccurrenceAt
        (contributionCapacityReopeningDepthAt sourceIndex) ≠
      periodicActualServiceExitOccurrenceAt
        (contributionCapacityFutureBirthDepth sourceIndex index) := by
  intro equality
  have depth_eq := periodicActualServiceExitOccurrenceAt_injective equality
  unfold contributionCapacityFutureBirthDepth at depth_eq
  unfold contributionCapacityReopeningDepthAtCurrent at depth_eq
  omega

end SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt

theorem contributionCapacityNewCompatibleFutureBirth_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let futureBirth :=
    sourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
      sourceIndex index
  fail_if_success exact futureBirth.participant
  fail_if_success exact futureBirth.score
  fail_if_success exact futureBirth.target
  fail_if_success exact futureBirth.future
  fail_if_success exact futureBirth.schedule
  fail_if_success exact futureBirth.registry
  trivial

end
end M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth.sourceGeneratedContributionCapacityNewCompatibleFutureBirthAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth.SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt.paymentWorkerBirthBearer_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth.SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt.refusalCapable_nonWork_contract
