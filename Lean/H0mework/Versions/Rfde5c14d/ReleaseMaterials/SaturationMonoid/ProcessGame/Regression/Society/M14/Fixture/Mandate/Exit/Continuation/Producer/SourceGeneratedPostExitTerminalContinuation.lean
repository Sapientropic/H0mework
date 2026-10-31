import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.Exit.Continuation.Root.SourceGeneratedMandateExitTargetHistory

/-!
# Source-generated post-exit terminal continuation

The exit action's generated macro next is consumed immediately as a new
target-root occurrence.  The sole mandate coordinate still reads the exited
history and terminal responsibility disposition; the old mandate is not
reopened.  The same occurrence also installs the existing source-backed UBI
Payment and performs the target root's whole-ledger write.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostExitTerminalContinuation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Renewal Election Relations Power UBI
open M8ActualElectionMandateRenewalRegression
open M9ProofCarryingRenewalInquiryRoot
open M9SourceSuppliedMandateSuffix
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceMandateRenewal
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14SourceGeneratedMandateExitTargetRoot
open M14SourceGeneratedSequentialMandateExit
open M14SourceGeneratedMandateExitTargetHistory

def installedPostExitMandateAt : SourceInstalledRenewalAt
    mandateExitTargetRecognition (mandateExitTargetTemporalVisitAt 1) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def installedPostExitMandateLocalFace : SourceMandateExitRenewalFace :=
  installedPostExitMandateAt.localFace
    (fun _ exactSeed =>
      lineageCompiler.controllerOf exactSeed.1.controllerSeed)
    (mandateStandingOf sourceMandateExitHistory lineageCompiler)

def installedPostExitUBIAt : SourceInstalledRenewalAt
    mandateExitTargetUBIRecognition (mandateExitTargetTemporalVisitAt 1) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

/-- Visit-indexed payment occurrence.  The local receipt may have the same
visible value as another period, while authority identity includes this exact
post-exit root visit. -/
structure PostExitSourceBackedPaymentAt : Type 3 where
  private mk ::
  installed : SourceInstalledRenewalAt mandateExitTargetUBIRecognition
    (mandateExitTargetTemporalVisitAt 1)
  exactRestriction : installed.payload.consumer =
    sourceGeneratedUBIRootRestriction
  rootOccurrence : ExactTemporalCausalRootEventAt
    mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
      (mandateExitTargetTemporalVisitAt 1)
  rootOccurrenceExact : rootOccurrence =
    (mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
      ).exactTemporalCausalEventAt (mandateExitTargetTemporalVisitAt 1)
  paymentReceipt : SourceBackedUBIPaymentReceiptAt
    exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave
  rootFactorization : installed.RootAnswerAndNextFactorizes

def postExitSourceBackedPaymentAt : PostExitSourceBackedPaymentAt where
  installed := installedPostExitUBIAt
  exactRestriction := rfl
  rootOccurrence := mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt (mandateExitTargetTemporalVisitAt 1)
  rootOccurrenceExact := rfl
  paymentReceipt := SourceBackedUBIPaymentReceiptAt.generate
  rootFactorization := installedPostExitUBIAt.rootAnswerAndNext_factorizes

/-- The post-exit occurrence is produced only from the already generated
canonical cycle and depth.  No visit, terminal verdict, Payment, row, next,
or successor controller enters the mouth. -/
structure SourceGeneratedPostExitTerminalContinuationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Type 3 where
  private mk ::
  macroNextExact :
    (generatedMandateExitActionAt initial depth
      ).target.targetAnswerAndNext.nextCurrent =
      ⟨(generatedMandateExitActionAt initial depth).target.TargetV,
        (generatedMandateExitActionAt initial depth
          ).target.targetRoot.toAuthoritativeRoot,
        mandateExitTargetTemporalVisitAt 1⟩
  postExitVisitDistinct : mandateExitTargetTemporalVisitAt 1 ≠
    mandateExitTargetTemporalVisitAt 0
  rootOccurrence : ExactTemporalCausalRootEventAt
    mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
      (mandateExitTargetTemporalVisitAt 1)
  rootOccurrenceExact : rootOccurrence =
    (mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
      ).exactTemporalCausalEventAt (mandateExitTargetTemporalVisitAt 1)
  installedMandate : SourceInstalledRenewalAt mandateExitTargetRecognition
    (mandateExitTargetTemporalVisitAt 1)
  mandateFace : SourceMandateExitRenewalFace
  mandateFaceExact : mandateFace = sourceMandateExitFace
  exitedTraceRetained : sourceMandateHistory.current ∈
    sourceMandateExitHistory.occurrence.trace
  powerLost : mandateFace.responsibilityConsumer.1.1.freedomChange.kind =
    FreedomChangeKind.lost
  phaseExit :
    (officeControllerRelationCompiler sourceMandateExitHistory lineageCompiler
      ).phaseStep
        (generatedOfficeControllerRelation sourceMandateExitHistory
          lineageCompiler) = MandatePhase.exit
  roleExited :
    (officeControllerRelationCompiler sourceMandateExitHistory lineageCompiler
      ).roleAt
        (generatedOfficeControllerRelation sourceMandateExitHistory
          lineageCompiler) .target = MandateRole.exited
  terminalDisposition : ∃ archive,
    mandateFace.exactDisposition.1.target.slots[
        (mandateSlot lineageCompiler
          sourceMandateExitHistory.current).val]? =
      some (.terminal archive)
  oldMandateCannotReopen : IsEmpty (NoMandateReopen Nat)
  mandateRootFactorization : installedMandate.RootAnswerAndNextFactorizes
  payment : PostExitSourceBackedPaymentAt
  wholeLedgerWriteBack : SourceNativeLedgerEvolutionAt
    mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot.source.source
    (mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit
        (mandateExitTargetTemporalVisitAt 1)).occurrence
  wholeLedgerWriteBackExact : wholeLedgerWriteBack =
    (mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit
        (mandateExitTargetTemporalVisitAt 1)).wholeLedgerWriteBack
  generatedNextVisitExact :
    (mandateExitTargetRoot.generatedNextCurrentAt
      (mandateExitTargetTemporalVisitAt 1)).visit =
        mandateExitTargetTemporalVisitAt 2
  oneMandateCoordinate :
    mandateProjectionFor sourceMandateExitHistory ≠
      recognitionWitnessProjectionFor sourceMandateExitHistory

def sourceGeneratedPostExitTerminalContinuationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceGeneratedPostExitTerminalContinuationAt initial depth :=
  let occurrence := mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt (mandateExitTargetTemporalVisitAt 1)
  let installed := installedPostExitMandateAt
  let face := installedPostExitMandateLocalFace
  { macroNextExact :=
      generatedMandateExitAction_macroNext_is_targetDepthOne initial depth
    postExitVisitDistinct := by
      exact Ne.symm (mandateExitTargetAdjacentVisits_distinct 0)
    rootOccurrence := occurrence
    rootOccurrenceExact := rfl
    installedMandate := installed
    mandateFace := face
    mandateFaceExact := rfl
    exitedTraceRetained := sourceMandate_exit_retains_prior_trace
    powerLost := sourceMandate_exit_power_is_lost
    phaseExit := rfl
    roleExited := sourceMandate_exit_role_is_exited
    terminalDisposition := sourceMandate_exit_disposition_is_terminal
    oldMandateCannotReopen := ⟨fun event => nomatch event⟩
    mandateRootFactorization := installed.rootAnswerAndNext_factorizes
    payment := postExitSourceBackedPaymentAt
    wholeLedgerWriteBack :=
      (mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          (mandateExitTargetTemporalVisitAt 1)).wholeLedgerWriteBack
    wholeLedgerWriteBackExact := rfl
    generatedNextVisitExact := rfl
    oneMandateCoordinate :=
      target_inventory_has_one_named_mandate_coordinate.1 }

theorem postExitTerminalContinuation_is_sourceGenerated
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    Nonempty (SourceGeneratedPostExitTerminalContinuationAt initial depth) :=
  ⟨sourceGeneratedPostExitTerminalContinuationAt initial depth⟩

end
end M14SourceGeneratedPostExitTerminalContinuation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostExitTerminalContinuation.sourceGeneratedPostExitTerminalContinuationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostExitTerminalContinuation.postExitTerminalContinuation_is_sourceGenerated
