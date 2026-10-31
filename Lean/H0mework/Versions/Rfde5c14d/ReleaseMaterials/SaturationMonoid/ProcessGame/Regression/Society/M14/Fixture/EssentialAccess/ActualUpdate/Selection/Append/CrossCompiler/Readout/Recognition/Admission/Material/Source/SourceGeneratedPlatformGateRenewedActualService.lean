import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Bearer.Source.SourceGeneratedPlatformGateAffectedBearerIncidence
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Incidence.Source.SourceGeneratedActualRelationThreeCycle
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Recurrence.SourceGeneratedCrossCompilerRelationAppendUBI
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Recurrence.SourceGeneratedCrossCompilerRelationAppendPresentation

/-!
# Renewed actual service for the platform gate

The gate occurrence at `platformCycleBaseAfter boundary` generates the
platform lineage and affected bearer.  The next occurrence of that same
lineage is three macro actions later.  It is provably a different actual
occurrence, while its exact relation seed and actor are the renewed platform
seed and actor.

That later source action generates one real maintenance debit and a fulfilled
terminal disposition in the existing actor-lifecycle vocabulary.  Its own
root action receipt supplies the whole write and next.  This is an independent
service-capacity occurrence: it does not reuse either slot of the old
two-service Payment and it does not ask U8 to manufacture material.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPlatformGateRenewedActualService

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange
open M3FiniteExchangeFixture
open M14EssentialAccessRelationFixture
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedCrossCompilerRelationCurrentRecurrence
open M14SourceGeneratedCrossCompilerRelationAppendStage
open M14SourceGeneratedCrossCompilerRelationAppendStage.CrossCompilerRelationAppendStageAt
open M14SourceGeneratedSequentialCrossCompilerRelationAppend
open M14SourceGeneratedCrossCompilerRelationAppendUBI
open M14SourceGeneratedCrossCompilerRelationAppendPresentation
open M14SourceGeneratedActualRelationThreeCycle
open M14SourceGeneratedCycleMemoryPlatformGateObstruction
open M14SourceGeneratedPlatformChannelRevisionCandidate
open M14SourceGeneratedPlatformGateAffectedBearerIncidence

/-! ## The later renewed platform occurrence -/

def platformGateMaterialDepthAt (boundary : Nat) : Nat :=
  platformGateAffectedBearerDepthAt boundary + 3

theorem platformGateMaterialDepth_later (boundary : Nat) :
    platformGateAffectedBearerDepthAt boundary <
      platformGateMaterialDepthAt boundary := by
  simp [platformGateMaterialDepthAt]

theorem platformGateMaterialSeed_renewsGate (boundary : Nat) :
    actualRelationSeedAt (platformGateMaterialDepthAt boundary) =
      actualRelationSeedAt (platformGateAffectedBearerDepthAt boundary) := by
  simpa [platformGateMaterialDepthAt] using
    crossCompilerCurrentStageAt_targetSeed_add_three
      (platformGateAffectedBearerDepthAt boundary)

theorem platformGateMaterialSeed_platform (boundary : Nat) :
    actualRelationSeedAt (platformGateMaterialDepthAt boundary) =
      exactEssentialAccessSeed .platform :=
  (platformGateMaterialSeed_renewsGate boundary).trans
    (platformCycleBaseAfter_seed_platform boundary)

theorem platformGateMaterialSelectedEvent_platform (boundary : Nat) :
    crossCompilerSelectedEventAt (platformGateMaterialDepthAt boundary) =
      .platform := by
  exact congrArg
    (fun seed : essentialAccessRelationCompiler.ExactRelationSeed =>
      (show EssentialAccessEvent from seed.1))
    (platformGateMaterialSeed_platform boundary)

theorem platformGateMaterialOccurrence_distinctFromGate (boundary : Nat) :
    (crossCompilerActionPresentationAt (platformGateMaterialDepthAt boundary)
      ).erase ≠
      (crossCompilerActionPresentationAt
        (platformGateAffectedBearerDepthAt boundary)).erase := by
  simpa [platformGateMaterialDepthAt] using
    (sourceGeneratedActualRelationThreeCycleAt
      (platformGateAffectedBearerDepthAt boundary)).renewedOccurrenceDistinct

def platformGateMaterialSeedAt (boundary : Nat) :
    essentialAccessRelationCompiler.ExactRelationSeed :=
  actualRelationSeedAt (platformGateMaterialDepthAt boundary)

def platformGateMaterialBearerOfSeed
    (seed : essentialAccessRelationCompiler.ExactRelationSeed) :
    Lifecycle.ActorBearer :=
  exchangeLaw.bearerOfActor (seed.actor essentialAccessRelationCompiler)

def platformGateMaterialBearerAt (boundary : Nat) : Lifecycle.ActorBearer :=
  platformGateMaterialBearerOfSeed (platformGateMaterialSeedAt boundary)

/-! ## One source-owned material-service debit -/

inductive PlatformGateMaterialBoundaryKind
  | maintain
  | fulfill
  deriving DecidableEq

structure PlatformGateMaterialReviewAt
    (obligation : AdmittedObligation Lifecycle.LifecycleVocabulary) where
  seed : essentialAccessRelationCompiler.ExactRelationSeed
  sourceExact : obligation.admission.sourceEvent = .after
  bearerExact : obligation.bearer = platformGateMaterialBearerOfSeed seed
  kind : PlatformGateMaterialBoundaryKind

def platformGateMaterialServiceProcess :
    NativeResponsibilityProcess Lifecycle.LifecycleVocabulary where
  AdmissionEvent := essentialAccessRelationCompiler.ExactRelationSeed
  admissionPayload :=
    criticalRelationAdmissionPayload platformGateMaterialBearerOfSeed
  BoundaryEvent := PlatformGateMaterialReviewAt
  boundarySource := fun _review => .after
  boundary_anchor_eq := fun review => by
    rw [review.sourceExact]
  boundary_incidence_eq := fun _review => rfl
  boundaryDisposition := fun review =>
    match review.kind with
    | .maintain => .carry (.maintained ())
    | .fulfill => .terminal (.final (.fulfilled ()))
  ReopenEvent := fun _archive => PEmpty
  reopenPayload := fun event => nomatch event

def platformGateMaterialServiceObligationAt (boundary : Nat) :
    AdmittedObligation Lifecycle.LifecycleVocabulary :=
  criticalRelationObligation platformGateMaterialBearerOfSeed
    (platformGateMaterialSeedAt boundary)

def platformGateMaterialAdmissionEdgeAt (boundary : Nat) :
    platformGateMaterialServiceProcess.Edge
      (ResponsibilityState.empty Lifecycle.LifecycleVocabulary) :=
  .admit (platformGateMaterialSeedAt boundary)

def platformGateMaterialServiceSourceStateAt (boundary : Nat) :=
  (platformGateMaterialAdmissionEdgeAt boundary).target

def platformGateMaterialServiceSlotAt (boundary : Nat) :
    Fin (platformGateMaterialServiceSourceStateAt boundary).slots.length :=
  ⟨0, by
    simp [platformGateMaterialServiceSourceStateAt,
      platformGateMaterialAdmissionEdgeAt,
      NativeResponsibilityProcess.Edge.target]⟩

theorem platformGateMaterialServiceSource_present (boundary : Nat) :
    (platformGateMaterialServiceSourceStateAt boundary).slots.get
        (platformGateMaterialServiceSlotAt boundary) =
      .live (platformGateMaterialServiceObligationAt boundary) :=
  rfl

def platformGateMaterialMaintenanceReviewAt (boundary : Nat) :
    PlatformGateMaterialReviewAt
      (platformGateMaterialServiceObligationAt boundary) where
  seed := platformGateMaterialSeedAt boundary
  sourceExact := rfl
  bearerExact := rfl
  kind := .maintain

def platformGateMaterialMaintenanceEdgeAt (boundary : Nat) :
    platformGateMaterialServiceProcess.Edge
      (platformGateMaterialServiceSourceStateAt boundary) :=
  .cross (platformGateMaterialServiceSlotAt boundary)
    (platformGateMaterialServiceObligationAt boundary)
    (platformGateMaterialServiceSource_present boundary)
    (platformGateMaterialMaintenanceReviewAt boundary)

def platformGateMaterialPostServiceStateAt (boundary : Nat) :=
  (platformGateMaterialMaintenanceEdgeAt boundary).target

def platformGateMaterialPostServiceSlotAt (boundary : Nat) :
    Fin (platformGateMaterialPostServiceStateAt boundary).slots.length :=
  ⟨0, by
    have targetAt := NativeResponsibilityProcess.cross_target_slot
      (P := platformGateMaterialServiceProcess)
      (platformGateMaterialServiceSlotAt boundary)
      (platformGateMaterialServiceObligationAt boundary)
      (platformGateMaterialServiceSource_present boundary)
      (platformGateMaterialMaintenanceReviewAt boundary)
    change
      (platformGateMaterialPostServiceStateAt boundary).slots[0]? =
        some (.live
          (platformGateMaterialServiceObligationAt boundary)) at targetAt
    exact (List.getElem?_eq_some_iff.mp targetAt).choose⟩

theorem platformGateMaterialPostService_present (boundary : Nat) :
    (platformGateMaterialPostServiceStateAt boundary).slots.get
        (platformGateMaterialPostServiceSlotAt boundary) =
      .live (platformGateMaterialServiceObligationAt boundary) :=
  rfl

def platformGateMaterialFulfillmentReviewAt (boundary : Nat) :
    PlatformGateMaterialReviewAt
      (platformGateMaterialServiceObligationAt boundary) where
  seed := platformGateMaterialSeedAt boundary
  sourceExact := rfl
  bearerExact := rfl
  kind := .fulfill

def platformGateMaterialFulfillmentEdgeAt (boundary : Nat) :
    platformGateMaterialServiceProcess.Edge
      (platformGateMaterialPostServiceStateAt boundary) :=
  .cross (platformGateMaterialPostServiceSlotAt boundary)
    (platformGateMaterialServiceObligationAt boundary)
    (platformGateMaterialPostService_present boundary)
    (platformGateMaterialFulfillmentReviewAt boundary)

theorem platformGateMaterialFulfillment_terminal (boundary : Nat) :
    ∃ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
      (platformGateMaterialFulfillmentEdgeAt boundary).target.slots[
          (platformGateMaterialPostServiceSlotAt boundary).val]? =
        some (.terminal archive) := by
  refine ⟨⟨platformGateMaterialServiceObligationAt boundary, .after,
    .fulfilled ()⟩, ?_⟩
  have targetSlot := NativeResponsibilityProcess.cross_target_slot
    (P := platformGateMaterialServiceProcess)
    (platformGateMaterialPostServiceSlotAt boundary)
    (platformGateMaterialServiceObligationAt boundary)
    (platformGateMaterialPostService_present boundary)
    (platformGateMaterialFulfillmentReviewAt boundary)
  change
    (platformGateMaterialFulfillmentEdgeAt boundary).target.slots[
        (platformGateMaterialPostServiceSlotAt boundary).val]? =
      some (.terminal
        { obligation := platformGateMaterialServiceObligationAt boundary
          sourceEvent := .after
          receipt := .fulfilled () }) at targetSlot
  exact targetSlot

theorem platformGateMaterialFulfillment_hasNoReopen
    (archive : TerminalArchive Lifecycle.LifecycleVocabulary) :
    IsEmpty (platformGateMaterialServiceProcess.ReopenEvent archive) := by
  change IsEmpty PEmpty
  exact ⟨fun event => nomatch event⟩

def platformGateMaterialBudgetAt
    (state : ResponsibilityState Lifecycle.LifecycleVocabulary)
    (_lineage : Lifecycle.DebtLineage) : Nat :=
  2 - state.history.length

@[simp] theorem platformGateMaterial_sourceBudget_eq_one (boundary : Nat) :
    platformGateMaterialBudgetAt
        (platformGateMaterialServiceSourceStateAt boundary) .debt = 1 :=
  rfl

@[simp] theorem platformGateMaterial_targetBudget_eq_zero (boundary : Nat) :
    platformGateMaterialBudgetAt
        (platformGateMaterialPostServiceStateAt boundary) .debt = 0 :=
  rfl

def platformGateMaterialMaintenanceDebitAt (boundary : Nat) :
    ActualMaintenanceDebit platformGateMaterialServiceProcess
      platformGateMaterialBudgetAt
      (platformGateMaterialMaintenanceEdgeAt boundary) .debt where
  slot := 0
  obligation := platformGateMaterialServiceObligationAt boundary
  sourceEvent := .after
  receipt := ()
  event_eq := rfl
  source_live := rfl
  target_live := rfl
  lineage_eq := rfl
  strict_debit := by
    change 0 < 1
    decide

inductive PlatformGateMaterialDebitEventAt (boundary : Nat) :
    {source : ResponsibilityState Lifecycle.LifecycleVocabulary} →
      platformGateMaterialServiceProcess.Edge source →
      Lifecycle.DebtLineage → Type
  | generated : PlatformGateMaterialDebitEventAt boundary
      (platformGateMaterialMaintenanceEdgeAt boundary) .debt

def platformGateMaterialDebitProcessAt (boundary : Nat) :
    NativeCarryDebitProcess platformGateMaterialServiceProcess where
  budgetAt := platformGateMaterialBudgetAt
  DebitEvent := PlatformGateMaterialDebitEventAt boundary
  debitReceipt := by
    intro source edge lineage event
    cases event with
    | generated =>
        exact platformGateMaterialMaintenanceDebitAt boundary

def platformGateMaterialServiceRunAt (boundary : Nat) :
    platformGateMaterialServiceProcess.Run
      (platformGateMaterialServiceSourceStateAt boundary)
      (platformGateMaterialPostServiceStateAt boundary) :=
  .step .nil (platformGateMaterialMaintenanceEdgeAt boundary)

def platformGateMaterialDebitedServiceAt (boundary : Nat) :
    NativeDebitedRun platformGateMaterialServiceProcess
      (platformGateMaterialDebitProcessAt boundary) .debt
      (platformGateMaterialServiceRunAt boundary) :=
  .step (.nil (platformGateMaterialServiceSourceStateAt boundary))
    (platformGateMaterialMaintenanceEdgeAt boundary)
    PlatformGateMaterialDebitEventAt.generated

@[simp] theorem platformGateMaterialServiceRun_events_length
    (boundary : Nat) :
    (platformGateMaterialServiceRunAt boundary).events.length = 1 :=
  rfl

def platformGateMaterialDebitSourceOwned (boundary : Nat) :
    SourceOwnsResponsibilityIncidence Lifecycle.LifecycleVocabulary .after
      (platformGateMaterialServiceObligationAt boundary) := by
  change SourceOwnsResponsibilityIncidence Lifecycle.LifecycleVocabulary
    (platformGateMaterialMaintenanceDebitAt boundary).sourceEvent
    (platformGateMaterialMaintenanceDebitAt boundary).obligation
  exact (platformGateMaterialMaintenanceDebitAt boundary).sourceOwnership

/-! ## Source occurrence, whole write, service and next in one carrier -/

inductive SourceGeneratedPlatformGateRenewedActualServiceAt
    (oldVisit : M14SourceGeneratedContributionMergeActionSource.OldVisit)
    (sourceIndex boundary : Nat) : Type 10
  | private generated

def sourceGeneratedPlatformGateRenewedActualServiceAt
    (oldVisit : M14SourceGeneratedContributionMergeActionSource.OldVisit)
    (sourceIndex boundary : Nat) :
    SourceGeneratedPlatformGateRenewedActualServiceAt oldVisit sourceIndex
      boundary :=
  .generated

namespace SourceGeneratedPlatformGateRenewedActualServiceAt

variable
  {oldVisit : M14SourceGeneratedContributionMergeActionSource.OldVisit}
  {sourceIndex boundary : Nat}
  (service : SourceGeneratedPlatformGateRenewedActualServiceAt oldVisit
    sourceIndex boundary)

include service

def gateIncidence :
    SourceGeneratedPlatformGateAffectedBearerIncidenceAt oldVisit sourceIndex
      boundary := by
  cases service
  exact sourceGeneratedPlatformGateAffectedBearerIncidenceAt oldVisit
    sourceIndex boundary

theorem renewedCycle : SourceGeneratedActualRelationThreeCycleAt
    (platformGateAffectedBearerDepthAt boundary) := by
  cases service
  exact sourceGeneratedActualRelationThreeCycleAt
    (platformGateAffectedBearerDepthAt boundary)

def sourceOccurrence := by
  cases service
  exact (appendStageAt (platformGateMaterialDepthAt boundary)).exactSource

def sourceAction := by
  cases service
  exact generatedCrossCompilerRelationAppendActionAt
    (platformGateMaterialDepthAt boundary)

def materialSeed : essentialAccessRelationCompiler.ExactRelationSeed := by
  cases service
  exact platformGateMaterialSeedAt boundary

def materialBearer : Lifecycle.ActorBearer := by
  cases service
  exact platformGateMaterialBearerAt boundary

def obligation : AdmittedObligation Lifecycle.LifecycleVocabulary := by
  cases service
  exact platformGateMaterialServiceObligationAt boundary

def debitedService :
    NativeDebitedRun platformGateMaterialServiceProcess
      (platformGateMaterialDebitProcessAt boundary) .debt
      (platformGateMaterialServiceRunAt boundary) := by
  cases service
  exact platformGateMaterialDebitedServiceAt boundary

def maintenanceDebit :
    ActualMaintenanceDebit platformGateMaterialServiceProcess
      platformGateMaterialBudgetAt
      (platformGateMaterialMaintenanceEdgeAt boundary) .debt := by
  cases service
  exact platformGateMaterialMaintenanceDebitAt boundary

def fulfillment := by
  cases service
  exact platformGateMaterialFulfillmentEdgeAt boundary

def generatedNext :=
  (sourceAction service).target.targetAnswerAndNext.nextCurrent

theorem occurrenceDistinctFromGate :
    (crossCompilerActionPresentationAt (platformGateMaterialDepthAt boundary)
      ).erase ≠
      (crossCompilerActionPresentationAt
        (platformGateAffectedBearerDepthAt boundary)).erase := by
  cases service
  exact platformGateMaterialOccurrence_distinctFromGate boundary

theorem materialSeedEqGateSeed :
    materialSeed service = (gateIncidence service).gate.seed := by
  cases service
  let incidence :=
    sourceGeneratedPlatformGateAffectedBearerIncidenceAt oldVisit sourceIndex
      boundary
  calc
    platformGateMaterialSeedAt boundary =
        actualRelationSeedAt (platformGateAffectedBearerDepthAt boundary) :=
      platformGateMaterialSeed_renewsGate boundary
    _ = (incidence.action).criticalBearer.bearerLineage.seed := by
      exact (crossCompilerSelectedAction_seed_exact
        (platformGateAffectedBearerDepthAt boundary)).symm
    _ = incidence.gate.seed := incidence.gateSeedActionExact.symm

theorem materialBearerEqAffectedBearer :
    materialBearer service = (gateIncidence service).affectedBearer := by
  cases service
  change platformGateMaterialBearerAt boundary =
    platformGateAffectedBearerAt boundary
  have materialEqPlatform :
      platformGateMaterialBearerAt boundary =
        exchangeLaw.bearerOfActor platformActor := by
    exact congrArg
      (fun seed : essentialAccessRelationCompiler.ExactRelationSeed =>
        exchangeLaw.bearerOfActor
          (seed.actor essentialAccessRelationCompiler))
      (platformGateMaterialSeed_platform boundary)
  exact materialEqPlatform.trans
    (platformGateAffectedBearer_fromPlatformActor boundary).symm

theorem obligationBearerEqAffectedBearer :
    (obligation service).bearer = (gateIncidence service).affectedBearer := by
  change platformGateMaterialBearerAt boundary =
    (gateIncidence service).affectedBearer
  exact materialBearerEqAffectedBearer service

def serviceSourceOwned :
    SourceOwnsResponsibilityIncidence Lifecycle.LifecycleVocabulary .after
      (obligation service) := by
  cases service
  exact platformGateMaterialDebitSourceOwned boundary

omit service in
theorem serviceBudgetSpent :
    platformGateMaterialBudgetAt
          (platformGateMaterialServiceSourceStateAt boundary) .debt = 1 ∧
      platformGateMaterialBudgetAt
          (platformGateMaterialPostServiceStateAt boundary) .debt = 0 ∧
      (platformGateMaterialServiceRunAt boundary).events.length = 1 :=
  ⟨platformGateMaterial_sourceBudget_eq_one boundary,
    platformGateMaterial_targetBudget_eq_zero boundary,
    platformGateMaterialServiceRun_events_length boundary⟩

theorem fulfillmentTerminal :
    ∃ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
      (fulfillment service).target.slots[
          (platformGateMaterialPostServiceSlotAt boundary).val]? =
        some (.terminal archive) := by
  cases service
  exact platformGateMaterialFulfillment_terminal boundary

theorem inheritedUBI :
    type_of% (crossCompilerUBI_directConsumer
      (platformGateMaterialDepthAt boundary)) := by
  cases service
  exact crossCompilerUBI_directConsumer _

theorem wholeActionReceipt :
    type_of% (generatedCrossCompilerRelationAppendAction_directConsumer
      (platformGateMaterialDepthAt boundary)) := by
  cases service
  exact generatedCrossCompilerRelationAppendAction_directConsumer _

theorem generatedNextExact : generatedNext service =
    ⟨(sourceAction service).target.TargetV,
      (sourceAction service).target.targetRoot.toAuthoritativeRoot,
      (sourceAction service).target.targetVisit⟩ :=
  generatedCrossCompilerRelationAppendAction_macroNext_exact _

end SourceGeneratedPlatformGateRenewedActualServiceAt

theorem platformGateRenewedActualService_directConsumer
    (oldVisit : M14SourceGeneratedContributionMergeActionSource.OldVisit)
    (sourceIndex boundary : Nat) :
    let service := sourceGeneratedPlatformGateRenewedActualServiceAt oldVisit
      sourceIndex boundary
    Nonempty (SourceGeneratedPlatformGateRenewedActualServiceAt oldVisit
        sourceIndex boundary) ∧
      platformGateAffectedBearerDepthAt boundary <
        platformGateMaterialDepthAt boundary ∧
      (crossCompilerActionPresentationAt
          (platformGateMaterialDepthAt boundary)).erase ≠
        (crossCompilerActionPresentationAt
          (platformGateAffectedBearerDepthAt boundary)).erase ∧
      service.materialSeed = service.gateIncidence.gate.seed ∧
      service.materialBearer = service.gateIncidence.affectedBearer ∧
      service.obligation.bearer = service.gateIncidence.affectedBearer ∧
      Nonempty (NativeDebitedRun platformGateMaterialServiceProcess
        (platformGateMaterialDebitProcessAt boundary) .debt
        (platformGateMaterialServiceRunAt boundary)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence
        Lifecycle.LifecycleVocabulary .after service.obligation) ∧
      platformGateMaterialBudgetAt
          (platformGateMaterialServiceSourceStateAt boundary) .debt = 1 ∧
      platformGateMaterialBudgetAt
          (platformGateMaterialPostServiceStateAt boundary) .debt = 0 ∧
      (platformGateMaterialServiceRunAt boundary).events.length = 1 ∧
      (∃ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
        service.fulfillment.target.slots[
            (platformGateMaterialPostServiceSlotAt boundary).val]? =
          some (.terminal archive)) ∧
      (∀ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
        IsEmpty
          (platformGateMaterialServiceProcess.ReopenEvent archive)) ∧
      type_of% (crossCompilerUBI_directConsumer
        (platformGateMaterialDepthAt boundary)) ∧
      type_of% (generatedCrossCompilerRelationAppendAction_directConsumer
        (platformGateMaterialDepthAt boundary)) ∧
      service.generatedNext =
        ⟨service.sourceAction.target.TargetV,
          service.sourceAction.target.targetRoot.toAuthoritativeRoot,
          service.sourceAction.target.targetVisit⟩ := by
  dsimp
  let service := sourceGeneratedPlatformGateRenewedActualServiceAt oldVisit
    sourceIndex boundary
  exact ⟨⟨service⟩,
    platformGateMaterialDepth_later boundary,
    service.occurrenceDistinctFromGate,
    service.materialSeedEqGateSeed,
    service.materialBearerEqAffectedBearer,
    service.obligationBearerEqAffectedBearer,
    ⟨service.debitedService⟩,
    ⟨service.serviceSourceOwned⟩,
    platformGateMaterial_sourceBudget_eq_one boundary,
    platformGateMaterial_targetBudget_eq_zero boundary,
    platformGateMaterialServiceRun_events_length boundary,
    service.fulfillmentTerminal,
    platformGateMaterialFulfillment_hasNoReopen,
    crossCompilerUBI_directConsumer _,
    generatedCrossCompilerRelationAppendAction_directConsumer _,
    service.generatedNextExact⟩

end
end M14SourceGeneratedPlatformGateRenewedActualService
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformGateRenewedActualService.sourceGeneratedPlatformGateRenewedActualServiceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformGateRenewedActualService.platformGateRenewedActualService_directConsumer
