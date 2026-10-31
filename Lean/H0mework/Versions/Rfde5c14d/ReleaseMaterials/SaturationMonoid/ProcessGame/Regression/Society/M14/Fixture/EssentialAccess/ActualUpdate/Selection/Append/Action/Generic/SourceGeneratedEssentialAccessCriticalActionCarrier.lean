import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Source.SourceGeneratedSelectedEssentialAccessCriticalEvent
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Source.Queue.SourceGeneratedEssentialAccessCriticalActionQueue

/-!
# Source-generated essential-access critical-action carrier

One small dependent carrier forgets whether an already generated action came
from an exact queue occurrence or from the current lineage fold.  It stores
only the generated event, its dependent action, and exactness.  There is no
raw-event constructor, selector, registry, root or append schedule here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedEssentialAccessCriticalActionCarrier

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power
open M14EssentialAccessRelationFixture
open M14SourceEssentialServiceRestoration
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedEssentialAccessCriticalActionQueue

abbrev QueueActionAt :=
  SourceGeneratedEssentialAccessCriticalActionQueueAt

/-- Common dependent image of an already source-generated critical action.
The private constructor prevents a caller from submitting an event. -/
structure SourceGeneratedEssentialAccessCriticalActionCarrier : Type 12 where
  private mk ::
  event : EssentialAccessEvent
  action : SourceGeneratedEssentialAccessCriticalActionAt event
  actionExact : action = sourceGeneratedEssentialAccessCriticalActionAt event

/-- Forget only the queue index, while definitionally preserving the queue's
generated event and dependent action. -/
def criticalActionCarrierOfQueueAction
    {unit : ExactQueueUnit} (queueAction : QueueActionAt unit) :
    SourceGeneratedEssentialAccessCriticalActionCarrier where
  event := queueAction.event
  action := queueAction.action
  actionExact := queueAction.actionExact

/-- Existing queue specializations enter the common gearbox through this
single transparent adapter.  It forgets no event/action provenance and does
not provide a reverse event selector. -/
instance queueActionCarrierCoeDep
    {unit : ExactQueueUnit} (queueAction : QueueActionAt unit) :
    CoeDep (QueueActionAt unit) queueAction
      SourceGeneratedEssentialAccessCriticalActionCarrier where
  coe := criticalActionCarrierOfQueueAction queueAction

theorem criticalActionCarrierOfQueueAction_provenance
    {unit : ExactQueueUnit} (queueAction : QueueActionAt unit) :
    let carrier := criticalActionCarrierOfQueueAction queueAction
    carrier.event = queueAction.event ∧
      carrier.action = queueAction.action ∧
      essentialServiceUnitOfEvent carrier.event = unit.1 :=
  ⟨rfl, rfl, queueAction.unitExact⟩

/-- Zero-choice conversion from the event already selected by the current's
lineage fold.  No event is accepted at this mouth. -/
def criticalActionCarrierOfSelected
    {current : EssentialAccessCriticalSelectionCurrent}
    (selected : SourceGeneratedSelectedEssentialAccessCriticalEventAt current) :
    SourceGeneratedEssentialAccessCriticalActionCarrier where
  event := selected.selectedEvent
  action := selected.action
  actionExact := selected.actionExact

theorem criticalActionCarrier_directConsumer
    (carrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    carrier.action.criticalBearer.bearerLineage.seed =
        exactEssentialAccessSeed carrier.event ∧
      carrier.action.criticalBearer.commonBearer =
        (criticalRelationObligation essentialAccessCriticalBearerOf
          carrier.event).bearer ∧
      essentialAccessRelationCompiler.phaseStep
          (essentialAccessCriticalRelation carrier.event) ≠ 0 ∧
      essentialAccessRelationCompiler.roleAt
          (essentialAccessCriticalRelation carrier.event) .target =
        essentialAccessRelationCompiler.advanceRole
          Lifecycle.actualEventGame.source
          (essentialAccessRelationCompiler.phaseStep
            (essentialAccessCriticalRelation carrier.event))
          (essentialAccessRelationCompiler.roleAt
            (essentialAccessCriticalRelation carrier.event) .source) := by
  refine ⟨?_, ?_, essentialAccessCriticalPhase_nonzero carrier.event, rfl⟩
  · rw [carrier.actionExact]
    rfl
  · rw [carrier.actionExact]
    exact (sourceGeneratedEssentialAccessCriticalActualUpdateAt
      carrier.event).bearerCommutes

/-- The selected carrier's event and action lineage seed are direct readouts
of the same current fold; the final equality exposes the fold's root law. -/
theorem criticalActionCarrierOfSelected_foldProvenance
    {current : EssentialAccessCriticalSelectionCurrent}
    (selected : SourceGeneratedSelectedEssentialAccessCriticalEventAt current) :
    let carrier := criticalActionCarrierOfSelected selected
    carrier.event = (selectedCriticalSeed current).1 ∧
      carrier.action.criticalBearer.bearerLineage.seed =
        selectedCriticalSeed current ∧
      selectedCriticalSeed current = current.root := by
  dsimp [criticalActionCarrierOfSelected,
    SourceGeneratedSelectedEssentialAccessCriticalEventAt.selectedEvent]
  exact ⟨congrArg Subtype.val selected.selectedSeedExact,
    selected.actionSeed_commutes.trans selected.selectedSeedExact,
    selectedCriticalSeed_eq_root current⟩

/-- Any occurrence-respecting candidate fold reads the same action lineage
seed.  This consumes the existing rooted-fold uniqueness theorem rather than
adding a second selector. -/
theorem criticalActionCarrierOfSelected_fold_unique
    {current : EssentialAccessCriticalSelectionCurrent}
    (selected : SourceGeneratedSelectedEssentialAccessCriticalEventAt current)
    (candidate : EssentialAccessCriticalSelectionCurrent →
      essentialAccessRelationCompiler.ExactRelationSeed)
    (commutes : ∀
      (origin : essentialAccessRelationCompiler.ExactRelationSeed)
      (branches : AccountedBranches
        essentialAccessRelationCompiler.ExactRelationSeed),
      candidate (.occur origin branches) =
        selectedCriticalSeedAlgebra origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    (criticalActionCarrierOfSelected selected
      ).action.criticalBearer.bearerLineage.seed = candidate current := by
  calc
    (criticalActionCarrierOfSelected selected
        ).action.criticalBearer.bearerLineage.seed =
        selectedCriticalSeed current :=
      (criticalActionCarrierOfSelected_foldProvenance selected).2.1
    _ = candidate current :=
      (selectedCriticalSeed_fold_unique current candidate commutes).symm

end
end M14SourceGeneratedEssentialAccessCriticalActionCarrier
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionCarrier.criticalActionCarrierOfQueueAction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionCarrier.criticalActionCarrierOfSelected
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionCarrier.criticalActionCarrier_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionCarrier.criticalActionCarrierOfSelected_fold_unique
