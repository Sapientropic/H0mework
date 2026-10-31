import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.Fixture.OccurrenceCapacityProcess
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Maintenance.SourceEssentialServiceRestoration
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Source.SourceGeneratedEssentialAccessCriticalAction

/-!
# Queue-generated essential-access critical actions

The existing M10 occurrence-capacity queue has three exact occurrences.  Its
first, middle and recurrent units generate tenure, health and platform action
carriers respectively.  The event is computed inside the producer and remains
locked to the queue occurrence and the existing exact relation seed; it is not
a caller argument.  This file adds no root, ledger, registry or schedule.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedEssentialAccessCriticalActionQueue

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity Lifecycle Universal Relations
open M10OccurrenceCapacityProcessFixture
open M14EssentialAccessRelationFixture
open M14SourceEssentialServiceRestoration
open M14SourceGeneratedEssentialAccessCriticalAction

abbrev QueueCompiler := serviceQueueCompiler
abbrev ExactQueueUnit := QueueCompiler.ExactQueueUnit
abbrev ExactRelationSeed := essentialAccessRelationCompiler.ExactRelationSeed

/-- One queue-indexed critical action.  Its constructor is private and every
field after `unitProvenance` is generated from the event selected internally
by the exact queue occurrence. -/
structure SourceGeneratedEssentialAccessCriticalActionQueueAt
    (unit : ExactQueueUnit) : Type where
  private mk ::
  unitProvenance : ∃ position : TracePosition game,
    position ∈ tracePositions game ∧
      ∃ raw : QueueCompiler.UnitAt position,
        raw ∈ QueueCompiler.unitInventoryAt position ∧
          (⟨position, raw⟩ : QueueCompiler.QueueUnit) = unit.1
  event : EssentialAccessEvent
  unitExact : essentialServiceUnitOfEvent event = unit.1
  action : SourceGeneratedEssentialAccessCriticalActionAt event
  actionExact : action = sourceGeneratedEssentialAccessCriticalActionAt event

/-- The first exact occurrence generates tenure. -/
def sourceGeneratedTenureCriticalActionQueue :
    SourceGeneratedEssentialAccessCriticalActionQueueAt firstExactUnit where
  unitProvenance := firstExactUnit.provenance QueueCompiler
  event := .tenure
  unitExact := rfl
  action := sourceGeneratedEssentialAccessCriticalActionAt .tenure
  actionExact := rfl

/-- The middle exact occurrence generates health. -/
def sourceGeneratedHealthCriticalActionQueue :
    SourceGeneratedEssentialAccessCriticalActionQueueAt middleExactUnit where
  unitProvenance := middleExactUnit.provenance QueueCompiler
  event := .health
  unitExact := rfl
  action := sourceGeneratedEssentialAccessCriticalActionAt .health
  actionExact := rfl

/-- The recurrent exact occurrence generates platform.  Its M10 state/seed
may equal the first occurrence's state/seed, while its actual position and
essential-access relation seed remain distinct. -/
def sourceGeneratedPlatformCriticalActionQueue :
    SourceGeneratedEssentialAccessCriticalActionQueueAt recurrentExactUnit where
  unitProvenance := recurrentExactUnit.provenance QueueCompiler
  event := .platform
  unitExact := rfl
  action := sourceGeneratedEssentialAccessCriticalActionAt .platform
  actionExact := rfl

/-- The compiler queue is exhaustive: no fourth exact queue occurrence can
enter this source producer. -/
theorem exactQueueUnit_exhaustive (unit : ExactQueueUnit) :
    unit = firstExactUnit ∨ unit = middleExactUnit ∨
      unit = recurrentExactUnit := by
  have membership : unit.1 ∈ [firstUnit, middleUnit, recurrentUnit] := by
    simpa [compiled_queue_eq] using unit.queueMembership QueueCompiler
  simp only [List.mem_cons] at membership
  rcases membership with first | middle | recurrent | impossible
  · left
    apply Subtype.ext
    exact first
  · right
    left
    apply Subtype.ext
    exact middle
  · right
    right
    apply Subtype.ext
    exact recurrent
  · simp at impossible

/-- Every exact queue occurrence lies in one of the three named nonempty
source fibres.  This Prop readout does not expose an ExactQueueUnit-to-event
observer. -/
theorem everyExactQueueUnit_generatesEssentialAccessCriticalAction
    (unit : ExactQueueUnit) :
    Nonempty (SourceGeneratedEssentialAccessCriticalActionQueueAt unit) := by
  rcases exactQueueUnit_exhaustive unit with rfl | rfl | rfl
  · exact ⟨sourceGeneratedTenureCriticalActionQueue⟩
  · exact ⟨sourceGeneratedHealthCriticalActionQueue⟩
  · exact ⟨sourceGeneratedPlatformCriticalActionQueue⟩

/-- The relation seed used downstream is a direct action-lineage readout, not
a second field stored in this queue carrier. -/
theorem queueAction_actionSeed_exact
    {unit : ExactQueueUnit}
    (queueAction : SourceGeneratedEssentialAccessCriticalActionQueueAt unit) :
    queueAction.action.criticalBearer.bearerLineage.seed =
      exactEssentialAccessSeed queueAction.event := by
  rw [queueAction.actionExact]
  rfl

@[simp] theorem firstQueue_event_exact :
    sourceGeneratedTenureCriticalActionQueue.event = .tenure :=
  rfl

@[simp] theorem middleQueue_event_exact :
    sourceGeneratedHealthCriticalActionQueue.event = .health :=
  rfl

@[simp] theorem recurrentQueue_event_exact :
    sourceGeneratedPlatformCriticalActionQueue.event = .platform :=
  rfl

/-! ## Distinct-occurrence and relation-seed no-go faces -/

theorem first_middle_exactQueueUnits_ne :
    firstExactUnit ≠ middleExactUnit := by
  intro equality
  have units := congrArg Subtype.val equality
  exact first_middle_positions_are_distinct
    (congrArg Sigma.fst units)

theorem middle_recurrent_exactQueueUnits_ne :
    middleExactUnit ≠ recurrentExactUnit := by
  intro equality
  have units := congrArg Subtype.val equality
  exact middle_recurrent_positions_are_distinct
    (congrArg Sigma.fst units)

theorem first_recurrent_exactQueueUnits_ne :
    firstExactUnit ≠ recurrentExactUnit := by
  intro equality
  have units := congrArg Subtype.val equality
  exact recurrent_positions_are_distinct
    (congrArg Sigma.fst units)

theorem tenure_health_relationSeeds_ne :
    exactEssentialAccessSeed .tenure ≠ exactEssentialAccessSeed .health := by
  intro equality
  have events := congrArg Subtype.val equality
  cases events

theorem health_platform_relationSeeds_ne :
    exactEssentialAccessSeed .health ≠ exactEssentialAccessSeed .platform := by
  intro equality
  have events := congrArg Subtype.val equality
  cases events

theorem tenure_platform_relationSeeds_ne :
    exactEssentialAccessSeed .tenure ≠ exactEssentialAccessSeed .platform := by
  intro equality
  have events := congrArg Subtype.val equality
  cases events

instance firstMiddleOccurrenceCollapse_isEmpty :
    IsEmpty (firstExactUnit = middleExactUnit) :=
  ⟨first_middle_exactQueueUnits_ne⟩

instance middleRecurrentOccurrenceCollapse_isEmpty :
    IsEmpty (middleExactUnit = recurrentExactUnit) :=
  ⟨middle_recurrent_exactQueueUnits_ne⟩

instance firstRecurrentOccurrenceCollapse_isEmpty :
    IsEmpty (firstExactUnit = recurrentExactUnit) :=
  ⟨first_recurrent_exactQueueUnits_ne⟩

instance tenureHealthSeedCollapse_isEmpty :
    IsEmpty (exactEssentialAccessSeed .tenure =
      exactEssentialAccessSeed .health) :=
  ⟨tenure_health_relationSeeds_ne⟩

instance healthPlatformSeedCollapse_isEmpty :
    IsEmpty (exactEssentialAccessSeed .health =
      exactEssentialAccessSeed .platform) :=
  ⟨health_platform_relationSeeds_ne⟩

instance tenurePlatformSeedCollapse_isEmpty :
    IsEmpty (exactEssentialAccessSeed .tenure =
      exactEssentialAccessSeed .platform) :=
  ⟨tenure_platform_relationSeeds_ne⟩

/-- Direct consumer of the three queue-generated action mouths. -/
theorem essentialAccessCriticalActionQueue_directConsumer :
    sourceGeneratedTenureCriticalActionQueue.unitExact = rfl ∧
      sourceGeneratedHealthCriticalActionQueue.unitExact = rfl ∧
      sourceGeneratedPlatformCriticalActionQueue.unitExact = rfl ∧
      sourceGeneratedTenureCriticalActionQueue.action =
        sourceGeneratedEssentialAccessCriticalActionAt .tenure ∧
      sourceGeneratedHealthCriticalActionQueue.action =
        sourceGeneratedEssentialAccessCriticalActionAt .health ∧
      sourceGeneratedPlatformCriticalActionQueue.action =
        sourceGeneratedEssentialAccessCriticalActionAt .platform ∧
      sourceGeneratedTenureCriticalActionQueue.action.criticalBearer.bearerLineage.seed =
        exactEssentialAccessSeed .tenure ∧
      sourceGeneratedHealthCriticalActionQueue.action.criticalBearer.bearerLineage.seed =
        exactEssentialAccessSeed .health ∧
      sourceGeneratedPlatformCriticalActionQueue.action.criticalBearer.bearerLineage.seed =
        exactEssentialAccessSeed .platform :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end
end M14SourceGeneratedEssentialAccessCriticalActionQueue
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionQueue.sourceGeneratedTenureCriticalActionQueue
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionQueue.sourceGeneratedHealthCriticalActionQueue
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionQueue.sourceGeneratedPlatformCriticalActionQueue
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionQueue.exactQueueUnit_exhaustive
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionQueue.everyExactQueueUnit_generatesEssentialAccessCriticalAction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionQueue.queueAction_actionSeed_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalActionQueue.essentialAccessCriticalActionQueue_directConsumer
