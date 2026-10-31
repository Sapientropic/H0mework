import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Source.Queue.SourceGeneratedEssentialAccessCriticalActionQueue

/-!
# Exact queue-action succession

The existing three-position M10 occurrence orders the named tenure, health
and platform carriers.  Succession is a proof-relevant restriction of those
exact positions, not a function from a queue unit, natural number or observer
readout to an event.  The recurrent position has no later unit in this finite
actual occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedEssentialAccessCriticalActionQueueSuccession

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M10OccurrenceCapacityProcessFixture
open M14EssentialAccessRelationFixture
open M14SourceEssentialServiceRestoration
open M14SourceGeneratedEssentialAccessCriticalActionQueue

structure SourceGeneratedQueueCriticalActionSuccessorAt
    (prior next : ExactQueueUnit) : Prop where
  private mk ::
  priorInQueue : prior.1 ∈ serviceQueueCompiler.queue
  nextInQueue : next.1 ∈ serviceQueueCompiler.queue
  positionStrict : prior.position.val < next.position.val
  adjacent : next.position.val = prior.position.val + 1

theorem firstToMiddleQueueCriticalAction :
    SourceGeneratedQueueCriticalActionSuccessorAt
      firstExactUnit middleExactUnit where
  priorInQueue := firstUnit_mem_queue
  nextInQueue := middleUnit_mem_queue
  positionStrict := by decide
  adjacent := rfl

theorem middleToRecurrentQueueCriticalAction :
    SourceGeneratedQueueCriticalActionSuccessorAt
      middleExactUnit recurrentExactUnit where
  priorInQueue := middleUnit_mem_queue
  nextInQueue := recurrentUnit_mem_queue
  positionStrict := by decide
  adjacent := rfl

structure RecurrentQueueCriticalActionSuccessorAt : Type 1 where
  next : ExactQueueUnit
  nextInQueue : next.1 ∈ serviceQueueCompiler.queue
  later : 2 < next.position.val

theorem recurrentQueueCriticalActionSuccessor_isEmpty :
    IsEmpty RecurrentQueueCriticalActionSuccessorAt := by
  constructor
  intro successor
  have bound := successor.next.position.isLt
  change successor.next.position.val < 3 at bound
  have later := successor.later
  change 2 < successor.next.position.val at later
  omega

theorem queueCriticalActionSuccession_directConsumer :
    SourceGeneratedQueueCriticalActionSuccessorAt
        firstExactUnit middleExactUnit ∧
      SourceGeneratedQueueCriticalActionSuccessorAt
        middleExactUnit recurrentExactUnit ∧
      IsEmpty RecurrentQueueCriticalActionSuccessorAt ∧
      sourceGeneratedTenureCriticalActionQueue.event = .tenure ∧
      sourceGeneratedHealthCriticalActionQueue.event = .health ∧
      sourceGeneratedPlatformCriticalActionQueue.event = .platform :=
  ⟨firstToMiddleQueueCriticalAction,
    middleToRecurrentQueueCriticalAction,
    recurrentQueueCriticalActionSuccessor_isEmpty,
    rfl, rfl, rfl⟩

end
end M14SourceGeneratedEssentialAccessCriticalActionQueueSuccession
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionQueueSuccession.firstToMiddleQueueCriticalAction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionQueueSuccession.middleToRecurrentQueueCriticalAction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionQueueSuccession.recurrentQueueCriticalActionSuccessor_isEmpty
