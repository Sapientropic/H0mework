import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.U8.Revised.SourceGeneratedHealthTargetCriticalEventSelectionU8Compilation
import H0mework.Foundation.Cofinal.ProductiveHistory

/-!
# Revised critical-event selection boundary

The U8-revised root installs one exact health selection at its receipt-grounded
initial occurrence.  Every noninitial current carries an inactive selection
receipt.  This file rejects caller current/event substitution, free replay,
unaccounted projection coordinates and false family coverage while retaining
the old raw-occurrence and terminal no-go results.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCriticalEventSelectionRevisedRootNoGo

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14EssentialAccessRelationFixture
open M14HealthTargetCriticalEventSelectionNoGo
open M14SourceGeneratedHealthCessationTargetRoot
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedRoot

abbrev RevisedSelectionActivationAt
    (current : NewV.Current) :=
  revisedProjectionLaw.ActiveAt .selection (revisedEmitted current)

theorem revisedSelectionActivation_isEmpty_of_noninitial
    (current : NewV.Current)
    (different : current ≠ initialSelectionCurrent) :
    IsEmpty (RevisedSelectionActivationAt current) :=
  ⟨fun active => different active.down⟩

/-- Caller-shaped claim that an event was installed at a chosen revised
current.  The dependent payload still has to come from the private source
producer, so the two indices cannot be replaced independently. -/
structure CallerInstalledCriticalRenewalAt
    (current : NewV.Current) (event : EssentialAccessEvent) : Type where
  active : RevisedSelectionActivationAt current
  installed : SourceGeneratedInstalledSelectedCriticalRenewalAt
    (revisedEmitted current) active
  selectedEventExact : installed.selected.selectedEvent = event

theorem callerInstalledCriticalRenewal_isEmpty_of_noninitial
    (current : NewV.Current) (event : EssentialAccessEvent)
    (different : current ≠ initialSelectionCurrent) :
    IsEmpty (CallerInstalledCriticalRenewalAt current event) :=
  ⟨fun claim => different claim.active.down⟩

theorem callerInstalledCriticalRenewal_isEmpty_of_wrongEvent
    (current : NewV.Current) (event : EssentialAccessEvent)
    (different : event ≠ current.root.1) :
    IsEmpty (CallerInstalledCriticalRenewalAt current event) :=
  ⟨fun claim => different
    (claim.selectedEventExact.symm.trans
      claim.installed.selected.selectedEvent_eq_currentRoot)⟩

abbrev RevisedFirstTargetCriticalRenewalReplayAt
    (event : EssentialAccessEvent) :=
  CallerInstalledCriticalRenewalAt
    (retainedSelectionNext initialSelectionCurrent) event

theorem revisedFirstTargetCriticalRenewalReplay_isEmpty
    (event : EssentialAccessEvent) :
    IsEmpty (RevisedFirstTargetCriticalRenewalReplayAt event) :=
  callerInstalledCriticalRenewal_isEmpty_of_noninitial _ _
    retainedSelectionNext_initial_ne

/-- Quantifying the subordinate event-polymorphic law family does not select
an installed family member.  A claimed installed coverage must provide the
root-owned active payload at every event, which is impossible. -/
structure RevisedInstalledCriticalEventFamilyCoverageAt : Type 1 where
  currentAt : EssentialAccessEvent → NewV.Current
  installedAt : (event : EssentialAccessEvent) →
    CallerInstalledCriticalRenewalAt (currentAt event) event

theorem revisedInstalledCriticalEventFamilyCoverage_isEmpty :
    IsEmpty RevisedInstalledCriticalEventFamilyCoverageAt := by
  constructor
  intro coverage
  let platform := coverage.installedAt .platform
  have current_eq : coverage.currentAt .platform =
      initialSelectionCurrent := platform.active.down
  have selected_root :=
    platform.installed.selected.selectedEvent_eq_currentRoot
  have platform_eq_root :
      EssentialAccessEvent.platform =
        (coverage.currentAt .platform).root.1 :=
    platform.selectedEventExact.symm.trans selected_root
  rw [current_eq] at platform_eq_root
  cases platform_eq_root

/-- The old and revised emitted occurrences are the two sides of the exact
typed-revision presentation.  Treating them as unrelated is empty. -/
structure OldRevisedSelectionOccurrenceSeparationAt : Prop where
  separated :
    generatedTypedRevision.occurrencePresentation.forward
        (healthCessationTargetRoot.emitted RootedFailure.oldSuccessor.next) ≠
      revisedEmitted initialSelectionCurrent

theorem oldRevisedSelectionOccurrenceSeparation_isEmpty :
    IsEmpty OldRevisedSelectionOccurrenceSeparationAt :=
  ⟨fun claim => claim.separated generatedTypedRevision.occurrence_commutes⟩

/-- Exhaustion of the revised projection grammar.  In particular there is no
hidden search/write coordinate beside ledger, one-shot selection and exact
old-target restrictions. -/
structure UnaccountedRevisedProjectionAt : Type 1 where
  projection : RevisedProjection
  notLedger : projection ≠ .ledger
  notInquiry : projection ≠ .inquiry
  notSelection : projection ≠ .selection
  notInherited : ∀ oldProjection, projection ≠ .inherited oldProjection

theorem unaccountedRevisedProjection_isEmpty :
    IsEmpty UnaccountedRevisedProjectionAt := by
  constructor
  rintro ⟨projection, notLedger, notInquiry, notSelection, notInherited⟩
  cases projection with
  | ledger => exact notLedger rfl
  | inquiry => exact notInquiry rfl
  | selection => exact notSelection rfl
  | inherited oldProjection => exact notInherited oldProjection rfl

theorem revisedRelationWrite_isEmpty (current : NewV.Current) :
    IsEmpty (NewV.RelationWriteAt current) :=
  ⟨PEmpty.elim⟩

theorem revisedContinuedTransport_isEmpty (current : NewV.Current) :
    IsEmpty (NewV.ContinuedTransportAt current) :=
  ⟨PEmpty.elim⟩

theorem revisedFaithfulTerminal_isEmpty (current : NewV.Current) :
    IsEmpty (NewV.FaithfulTerminalAt current) :=
  ⟨PEmpty.elim⟩

def revisedFiniteCurrentAt : Nat → NewV.Current
  | 0 => initialSelectionCurrent
  | depth + 1 => retainedSelectionNext (revisedFiniteCurrentAt depth)

def revisedProductiveFiniteHistory :
    ProductiveFiniteRootHistoryAt revisedAuthoritativeRoot.toLedgerRoot where
  currentAt := revisedFiniteCurrentAt
  initial_eq := rfl
  next_eq := fun _ => rfl

theorem revisedStrictCofinalFiniteVisit_isEmpty :
    IsEmpty (StrictCofinalRootVisitAt revisedProductiveFiniteHistory) :=
  strictCofinalRootVisitAt_isEmpty revisedProductiveFiniteHistory

/-- Direct boundary consumer.  The current candidate has an exact initial
health action and a living first successor, but it cannot report platform or
tenure coverage until a later actual action generates a new root seed. -/
theorem revisedCriticalEventSelectionBoundary_directConsumer :
    IsEmpty OldHealthTargetCriticalEventCoverageAt ∧
      IsEmpty OldHealthTargetCurrentFactoredFamilyCoverageAt ∧
      IsEmpty HealthTerminalCriticalContinuationAt ∧
      IsEmpty RevisedInstalledCriticalEventFamilyCoverageAt ∧
      IsEmpty (RevisedFirstTargetCriticalRenewalReplayAt .health) ∧
      IsEmpty OldRevisedSelectionOccurrenceSeparationAt ∧
      IsEmpty UnaccountedRevisedProjectionAt ∧
      IsEmpty (StrictCofinalRootVisitAt revisedProductiveFiniteHistory) :=
  ⟨oldHealthTargetCriticalEventCoverage_isEmpty,
    oldHealthTargetCurrentFactoredFamilyCoverage_isEmpty,
    healthTerminalCriticalContinuation_isEmpty,
    revisedInstalledCriticalEventFamilyCoverage_isEmpty,
    revisedFirstTargetCriticalRenewalReplay_isEmpty .health,
    oldRevisedSelectionOccurrenceSeparation_isEmpty,
    unaccountedRevisedProjection_isEmpty,
    revisedStrictCofinalFiniteVisit_isEmpty⟩

end
end M14SourceGeneratedCriticalEventSelectionRevisedRootNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedRootNoGo.revisedSelectionActivation_isEmpty_of_noninitial
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedRootNoGo.callerInstalledCriticalRenewal_isEmpty_of_wrongEvent
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedRootNoGo.revisedInstalledCriticalEventFamilyCoverage_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedRootNoGo.oldRevisedSelectionOccurrenceSeparation_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedRootNoGo.revisedCriticalEventSelectionBoundary_directConsumer
