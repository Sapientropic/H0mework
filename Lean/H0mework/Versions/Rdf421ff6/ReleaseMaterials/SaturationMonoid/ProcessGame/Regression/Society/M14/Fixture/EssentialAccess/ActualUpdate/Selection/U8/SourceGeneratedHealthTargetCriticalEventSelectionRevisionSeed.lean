import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.U8.SourceGeneratedHealthTargetCriticalEventSelectionU8Frontier
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Source.SourceGeneratedSelectedEssentialAccessCriticalEvent

/-!
# Field-grounded critical-event selection revision seed

The U8 coface direction carries no semantic payload.  Its revised selection
current is therefore grounded separately in the exact health relation seed
already present in the action receipt's bearer lineage.  This file joins those
two generated inputs without claiming that a revised living root already
exists.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedHealthTargetCriticalEventSelectionRevisionSeed

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14EssentialAccessRelationFixture
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedHealthTargetCriticalEventSelectionU8Frontier
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent

def healthCriticalSelectionInitialSeed :
    essentialAccessRelationCompiler.ExactRelationSeed :=
  sourceGeneratedHealthCriticalAction.criticalBearer.bearerLineage.seed

@[simp] theorem healthCriticalSelectionInitialSeed_exact :
    healthCriticalSelectionInitialSeed = exactEssentialAccessSeed .health :=
  rfl

def healthCriticalSelectionInitialCurrent :
    EssentialAccessCriticalSelectionCurrent :=
  RootedAccountedUnfolding.zero healthCriticalSelectionInitialSeed

def healthCriticalSelectionInitialSelected :
    SourceGeneratedSelectedEssentialAccessCriticalEventAt
      healthCriticalSelectionInitialCurrent :=
  sourceGeneratedSelectedEssentialAccessCriticalEventAt
    healthCriticalSelectionInitialCurrent

@[simp] theorem healthCriticalSelectionInitialSelected_event :
    healthCriticalSelectionInitialSelected.selectedEvent = .health := by
  rw [healthCriticalSelectionInitialSelected.selectedEvent_eq_currentRoot]
  rfl

/-- Semantic seed for the later typed revision.  Constructor privacy prevents
replacement of either the rooted failure or the receipt-generated seed. -/
structure HealthTargetCriticalEventSelectionRevisionSeedAt : Type 12 where
  private mk ::
  frontier : HealthTargetCriticalEventSelectionU8Frontier
  frontierExact : frontier =
    sourceGeneratedHealthTargetCriticalEventSelectionU8Frontier
  initialSeed : essentialAccessRelationCompiler.ExactRelationSeed
  initialSeedFromHealthReceipt : initialSeed =
    sourceGeneratedHealthCriticalAction.criticalBearer.bearerLineage.seed
  revisedCurrent : EssentialAccessCriticalSelectionCurrent
  revisedCurrentExact : revisedCurrent =
    RootedAccountedUnfolding.zero initialSeed
  selected : SourceGeneratedSelectedEssentialAccessCriticalEventAt
    revisedCurrent
  selectedEventHealth : selected.selectedEvent = .health
  selectedActionSeedCommutes :
    selected.action.criticalBearer.bearerLineage.seed = initialSeed

def sourceGeneratedHealthTargetCriticalEventSelectionRevisionSeed :
    HealthTargetCriticalEventSelectionRevisionSeedAt :=
  let frontier :=
    sourceGeneratedHealthTargetCriticalEventSelectionU8Frontier
  let seed := healthCriticalSelectionInitialSeed
  let current := healthCriticalSelectionInitialCurrent
  let selected := healthCriticalSelectionInitialSelected
  { frontier := frontier
    frontierExact := rfl
    initialSeed := seed
    initialSeedFromHealthReceipt := rfl
    revisedCurrent := current
    revisedCurrentExact := rfl
    selected := selected
    selectedEventHealth := healthCriticalSelectionInitialSelected_event
    selectedActionSeedCommutes := by
      change selected.action.criticalBearer.bearerLineage.seed = seed
      rw [selected.actionSeed_commutes]
      rfl }

theorem healthTargetCriticalEventSelectionRevisionSeed_directConsumer :
    let revision :=
      sourceGeneratedHealthTargetCriticalEventSelectionRevisionSeed
    revision.frontier =
        sourceGeneratedHealthTargetCriticalEventSelectionU8Frontier ∧
      revision.initialSeed =
        sourceGeneratedHealthCriticalAction.criticalBearer.bearerLineage.seed ∧
      revision.revisedCurrent =
        RootedAccountedUnfolding.zero revision.initialSeed ∧
      revision.selected.selectedEvent = .health ∧
      revision.selected.action.criticalBearer.bearerLineage.seed =
        revision.initialSeed :=
  ⟨rfl, rfl, rfl, healthCriticalSelectionInitialSelected_event, by
    exact sourceGeneratedHealthTargetCriticalEventSelectionRevisionSeed
      |>.selectedActionSeedCommutes⟩

end
end M14SourceGeneratedHealthTargetCriticalEventSelectionRevisionSeed
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthTargetCriticalEventSelectionRevisionSeed.sourceGeneratedHealthTargetCriticalEventSelectionRevisionSeed
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthTargetCriticalEventSelectionRevisionSeed.healthTargetCriticalEventSelectionRevisionSeed_directConsumer
