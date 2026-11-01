import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Root.SourceGeneratedEssentialAccessCriticalActionAppendLedger

/-!
# Source-generated critical-action append selection

The source-generated action is installed only at its literal appended current.
The selected event remains the current's lineage root and compiles the existing
event-polymorphic renewal law; no root projection inventory is built here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedEssentialAccessCriticalActionAppendSelection

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal
open M14SourceEssentialAccessCriticalRenewal
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedEssentialAccessCriticalActionCarrier
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger

theorem actionCarrier_actionSeed_event
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    actionCarrier.action.criticalBearer.bearerLineage.seed.1 =
      actionCarrier.event :=
  congrArg Subtype.val
    (criticalActionCarrier_directConsumer actionCarrier).1

theorem appendOccurrence_eq_emitted
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier)
    {current : (AppendVAt prior actionCarrier).Current}
    (occurrence :
      (appendSource prior actionCarrier).toRootSource.actual.OccurrenceAt current) :
    occurrence = appendEmitted prior actionCarrier current := by
  rcases occurrence with ⟨support, event⟩
  cases support with
  | inl _ => exact nomatch event
  | inr direction => cases direction; cases event; rfl

def appendCriticalRenewalRootShell
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    SourceNativeRenewalRootShellAt
      (appendRestructuringSource prior actionCarrier).toLedgerSource where
  ActiveAt := fun {current} _ =>
    PLift (current = appendedCriticalSelectionCurrent prior actionCarrier)
  InactiveAt := fun {current} _ =>
    PLift (current ≠ appendedCriticalSelectionCurrent prior actionCarrier)
  classify := by
    intro current occurrence
    by_cases current_eq :
        current = appendedCriticalSelectionCurrent prior actionCarrier
    · exact .inl ⟨current_eq⟩
    · exact .inr ⟨current_eq⟩
  sourceEntry := by
    intro current occurrence active
    cases active.down
    rw [appendOccurrence_eq_emitted prior actionCarrier occurrence]
    exact newRevisedEntry
  selectedRow := by
    intro current occurrence active
    cases active.down
    rw [appendOccurrence_eq_emitted prior actionCarrier occurrence]
    exact (appendLedgerCompiler prior actionCarrier
      ).canonicalGeneratedEntry_of_terminalOrTransferred
        (appendEmitted prior actionCarrier
          (appendedCriticalSelectionCurrent prior actionCarrier))
        newRevisedEntry (by rfl)
  successor := by
    intro current occurrence active
    cases active.down
    rw [appendOccurrence_eq_emitted prior actionCarrier occurrence]
    exact (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
      ((appendLedgerCompiler prior actionCarrier).compile
        (appendEmitted prior actionCarrier
          (appendedCriticalSelectionCurrent prior actionCarrier)))).get (by rfl)
  activeOccurrences_eq := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence
      leftActive rightActive
    cases leftActive.down
    cases rightActive.down
    rw [appendOccurrence_eq_emitted prior actionCarrier leftOccurrence,
      appendOccurrence_eq_emitted prior actionCarrier rightOccurrence]

structure SourceGeneratedInstalledCriticalRenewalAt
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier)
    {current : (AppendVAt prior actionCarrier).Current}
    (occurrence :
      (appendSource prior actionCarrier).toRootSource.actual.OccurrenceAt current)
    (active :
      (appendCriticalRenewalRootShell prior actionCarrier).ActiveAt occurrence) :
    Type where
  private mk ::
  selected : SourceGeneratedSelectedEssentialAccessCriticalEventAt current
  selectedExact : selected =
    sourceGeneratedSelectedEssentialAccessCriticalEventAt current
  selectedEventExact : selected.selectedEvent = actionCarrier.event
  payload : RootRestrictedRenewalPayloadAt
    (appendRestructuringSource prior actionCarrier).toLedgerSource occurrence
      LocalGame (EssentialAccessCriticalLocalSeed actionCarrier.event)
      (EssentialAccessCriticalLocalSeedAt actionCarrier.event)
      (SourceEssentialAccessCriticalConsumerAt actionCarrier.event)
      (SourceEssentialAccessCriticalDispositionAt actionCarrier.event)
  payloadExact : payload =
    (sourceEssentialAccessCriticalRenewalLaw actionCarrier.event
      (appendCriticalRenewalRootShell prior actionCarrier)).compile occurrence active

def sourceGeneratedInstalledCriticalRenewalAt
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier)
    {current : (AppendVAt prior actionCarrier).Current}
    (occurrence :
      (appendSource prior actionCarrier).toRootSource.actual.OccurrenceAt current)
    (active :
      (appendCriticalRenewalRootShell prior actionCarrier).ActiveAt occurrence) :
    SourceGeneratedInstalledCriticalRenewalAt
      prior actionCarrier occurrence active :=
  let selected := sourceGeneratedSelectedEssentialAccessCriticalEventAt current
  { selected := selected
    selectedExact := rfl
    selectedEventExact := by
      rw [selected.selectedEvent_eq_currentRoot, active.down]
      exact actionCarrier_actionSeed_event actionCarrier
    payload :=
      (sourceEssentialAccessCriticalRenewalLaw actionCarrier.event
        (appendCriticalRenewalRootShell prior actionCarrier)).compile
          occurrence active
    payloadExact := rfl }

end
end M14SourceGeneratedEssentialAccessCriticalActionAppendSelection
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionAppendSelection.appendCriticalRenewalRootShell
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionAppendSelection.sourceGeneratedInstalledCriticalRenewalAt
