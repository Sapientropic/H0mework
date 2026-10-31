import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Law.SourceEssentialAccessCriticalRenewal

/-!
# Fold-selected essential-access critical event

The intended U8-revised authoritative current is one
`RootedAccountedUnfolding` of existing exact relation seeds.  Selection is the
root fold of that current: no event, actor, relation, bearer or target is a
producer argument.  A later root integration must generate the current before
calling this subordinate producer; this file does not create a root or a
completed history.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSelectedEssentialAccessCriticalEvent

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power
open M14EssentialAccessRelationFixture
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalTerminal

abbrev EssentialAccessCriticalSelectionCurrent :=
  RootedAccountedUnfolding
    essentialAccessRelationCompiler.ExactRelationSeed

/-- The root occurrence owns selection; child results are trace only. -/
def selectedCriticalSeedAlgebra
    (origin : essentialAccessRelationCompiler.ExactRelationSeed)
    (_children : List
      essentialAccessRelationCompiler.ExactRelationSeed) :
    essentialAccessRelationCompiler.ExactRelationSeed :=
  origin

def selectedCriticalSeed
    (current : EssentialAccessCriticalSelectionCurrent) :
    essentialAccessRelationCompiler.ExactRelationSeed :=
  current.fold selectedCriticalSeedAlgebra

@[simp] theorem selectedCriticalSeed_eq_root
    (current : EssentialAccessCriticalSelectionCurrent) :
    selectedCriticalSeed current = current.root := by
  cases current
  rfl

/-- Any selector respecting the sole occurrence constructor is the same root
fold. -/
theorem selectedCriticalSeed_fold_unique
    (current : EssentialAccessCriticalSelectionCurrent)
    (candidate : EssentialAccessCriticalSelectionCurrent →
      essentialAccessRelationCompiler.ExactRelationSeed)
    (commutes : ∀
      (origin : essentialAccessRelationCompiler.ExactRelationSeed)
      (branches : AccountedBranches
        essentialAccessRelationCompiler.ExactRelationSeed),
      candidate (.occur origin branches) =
        selectedCriticalSeedAlgebra origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate current = selectedCriticalSeed current :=
  RootedAccountedUnfolding.fold_unique selectedCriticalSeedAlgebra candidate
    commutes current

theorem exactEssentialAccessSeed_of_exact
    (seed : essentialAccessRelationCompiler.ExactRelationSeed) :
    exactEssentialAccessSeed seed.1 = seed :=
  Subtype.ext rfl

/-- Zero-choice selected-event carrier.  Action and terminal update are
generated from the selected exact seed's existing event index. -/
structure SourceGeneratedSelectedEssentialAccessCriticalEventAt
    (current : EssentialAccessCriticalSelectionCurrent) : Type where
  private mk ::
  selectedSeed : essentialAccessRelationCompiler.ExactRelationSeed
  selectedSeedExact : selectedSeed = selectedCriticalSeed current
  action : SourceGeneratedEssentialAccessCriticalActionAt selectedSeed.1
  actionExact : action =
    sourceGeneratedEssentialAccessCriticalActionAt selectedSeed.1
  update : EssentialAccessCriticalActualUpdateAt selectedSeed.1
  updateExact : update =
    sourceGeneratedEssentialAccessCriticalActualUpdateAt selectedSeed.1

def sourceGeneratedSelectedEssentialAccessCriticalEventAt
    (current : EssentialAccessCriticalSelectionCurrent) :
    SourceGeneratedSelectedEssentialAccessCriticalEventAt current :=
  let seed := selectedCriticalSeed current
  { selectedSeed := seed
    selectedSeedExact := rfl
    action := sourceGeneratedEssentialAccessCriticalActionAt seed.1
    actionExact := rfl
    update := sourceGeneratedEssentialAccessCriticalActualUpdateAt seed.1
    updateExact := rfl }

namespace SourceGeneratedSelectedEssentialAccessCriticalEventAt

variable {current : EssentialAccessCriticalSelectionCurrent}
variable (selected :
  SourceGeneratedSelectedEssentialAccessCriticalEventAt current)

def selectedEvent : EssentialAccessEvent :=
  selected.selectedSeed.1

theorem selectedSeed_eq_currentRoot :
    selected.selectedSeed = current.root := by
  rw [selected.selectedSeedExact, selectedCriticalSeed_eq_root]

theorem selectedEvent_eq_currentRoot :
    selected.selectedEvent = current.root.1 :=
  congrArg Subtype.val selected.selectedSeed_eq_currentRoot

theorem exact_relation_action_update :
    selected.selectedSeed = current.root ∧
      selected.action =
        sourceGeneratedEssentialAccessCriticalActionAt
          selected.selectedSeed.1 ∧
      selected.update =
        sourceGeneratedEssentialAccessCriticalActualUpdateAt
          selected.selectedSeed.1 ∧
      selected.action.criticalBearer.commonBearer =
        (criticalRelationObligation essentialAccessCriticalBearerOf
          selected.selectedSeed.1).bearer := by
  refine ⟨selected.selectedSeed_eq_currentRoot, selected.actionExact,
    selected.updateExact, ?_⟩
  rw [selected.actionExact]
  exact (sourceGeneratedEssentialAccessCriticalActualUpdateAt
    selected.selectedSeed.1).bearerCommutes

theorem actionSeed_commutes :
    selected.action.criticalBearer.bearerLineage.seed =
      selected.selectedSeed := by
  rw [selected.actionExact]
  exact exactEssentialAccessSeed_of_exact selected.selectedSeed

end SourceGeneratedSelectedEssentialAccessCriticalEventAt

/-- Same revised current cannot generate two different selected events. -/
theorem selectedCriticalEvent_uniqueAtCurrent
    (current : EssentialAccessCriticalSelectionCurrent)
    (left right :
      SourceGeneratedSelectedEssentialAccessCriticalEventAt current) :
    left.selectedEvent = right.selectedEvent := by
  rw [left.selectedEvent_eq_currentRoot, right.selectedEvent_eq_currentRoot]

structure CallerSelectedCriticalEventAt
    (current : EssentialAccessCriticalSelectionCurrent)
    (event : EssentialAccessEvent) : Type where
  selected : SourceGeneratedSelectedEssentialAccessCriticalEventAt current
  selectedEventExact : selected.selectedEvent = event

theorem callerSelectedCriticalEvent_isEmpty
    (current : EssentialAccessCriticalSelectionCurrent)
    (event : EssentialAccessEvent)
    (different : event ≠ current.root.1) :
    IsEmpty (CallerSelectedCriticalEventAt current event) :=
  ⟨fun claim => different
    (claim.selected.selectedEvent_eq_currentRoot.symm.trans
      claim.selectedEventExact).symm⟩

structure TwoSelectedCriticalEventsAt
    (current : EssentialAccessCriticalSelectionCurrent) : Type where
  left : SourceGeneratedSelectedEssentialAccessCriticalEventAt current
  right : SourceGeneratedSelectedEssentialAccessCriticalEventAt current
  eventsDistinct : left.selectedEvent ≠ right.selectedEvent

theorem twoSelectedCriticalEventsAt_isEmpty
    (current : EssentialAccessCriticalSelectionCurrent) :
    IsEmpty (TwoSelectedCriticalEventsAt current) :=
  ⟨fun pair => pair.eventsDistinct
    (selectedCriticalEvent_uniqueAtCurrent current pair.left pair.right)⟩

end
end M14SourceGeneratedSelectedEssentialAccessCriticalEvent
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSelectedEssentialAccessCriticalEvent.selectedCriticalSeed_fold_unique
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSelectedEssentialAccessCriticalEvent.sourceGeneratedSelectedEssentialAccessCriticalEventAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSelectedEssentialAccessCriticalEvent.SourceGeneratedSelectedEssentialAccessCriticalEventAt.exact_relation_action_update
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSelectedEssentialAccessCriticalEvent.twoSelectedCriticalEventsAt_isEmpty
