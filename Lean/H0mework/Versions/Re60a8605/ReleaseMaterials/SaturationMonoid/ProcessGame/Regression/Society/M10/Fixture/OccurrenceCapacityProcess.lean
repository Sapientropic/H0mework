import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.SourceGeneratedOccurrenceRate

/-!
# M10 occurrence-capacity process fixture

This regression-only fixture has one source occurrence whose chronological
trace has three positions.  The first and third positions revisit the same
state and generate the same seed.  Its rate compiler nevertheless retains
three distinct queue occurrences because identity is indexed by the actual
source-trace position.

The numeral `3` is confined to this fixture.  Production queue bounds remain
derived from `game.occurrence.trace.length`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M10OccurrenceCapacityProcessFixture

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity

abbrev Source := Unit
abbrev State := Bool

/-- One three-position occurrence with a genuine recurrent state at the final
position. -/
def occurrenceOf (_source : Source) : RootedAccountedUnfolding State :=
  .occur false <|
    .cons (.zero true) <|
      .singleton (.zero false)

def game : SaturationMonoid.ProcessGame occurrenceOf := ⟨()⟩

@[simp] theorem occurrence_trace :
    game.occurrence.trace = [false, true, false] :=
  rfl

@[simp] theorem occurrence_trace_length :
    game.occurrence.trace.length = 3 :=
  rfl

/-- Chronological positions used by downstream prefix regressions. -/
def firstPosition : TracePosition game :=
  ⟨0, by
    change 0 < 3
    decide⟩

def middlePosition : TracePosition game :=
  ⟨1, by
    change 1 < 3
    decide⟩

def recurrentPosition : TracePosition game :=
  ⟨2, by
    change 2 < 3
    decide⟩

@[simp] theorem firstPosition_value : firstPosition.val = 0 := rfl

@[simp] theorem middlePosition_value : middlePosition.val = 1 := rfl

@[simp] theorem recurrentPosition_value : recurrentPosition.val = 2 := rfl

@[simp] theorem first_state : stateAt game firstPosition = false := rfl

@[simp] theorem middle_state : stateAt game middlePosition = true := rfl

@[simp] theorem recurrent_state : stateAt game recurrentPosition = false := rfl

theorem recurrent_positions_are_distinct :
    firstPosition ≠ recurrentPosition := by
  decide

theorem first_middle_positions_are_distinct :
    firstPosition ≠ middlePosition := by
  decide

theorem middle_recurrent_positions_are_distinct :
    middlePosition ≠ recurrentPosition := by
  decide

theorem recurrent_positions_store_same_state :
    stateAt game firstPosition = stateAt game recurrentPosition :=
  rfl

abbrev Seed := Bool

/-- Each position generates its stored state as its exact seed. -/
def seedAt (_source : Source) (state : State) (seed : Seed) : Prop :=
  seed = state

abbrev Lineage (_source : Source) := Unit

def lineageOf (source : Source)
    (_seed : SourceSeed occurrenceOf Seed seedAt source) : Lineage source :=
  ()

/-- Exact focal seed generated at the first occurrence position. -/
def focalSeed : SourceSeed occurrenceOf Seed seedAt game.source :=
  ⟨false,
    ⟨stateAt game firstPosition, stateAt_mem game firstPosition, rfl⟩⟩

abbrev UnitAt (_position : TracePosition game) := PUnit

/-- One exhaustive unit per actual position.  The raw unit type is trivial;
all occurrence identity therefore comes from the source-derived position. -/
def compiler : SourceOwnedOccurrenceRateCompiler
    game Seed seedAt Lineage lineageOf focalSeed where
  UnitAt := UnitAt
  unitInventoryAt := fun _position => [PUnit.unit]
  unitInventory_nodup := by
    intro position
    simp
  raw_unit_mem := by
    intro position raw
    cases raw
    simp
  seedAt := fun position _unit => stateAt game position
  seedIncidence := by
    intro position raw
    cases raw
    rfl
  lineage_eq_focal := by
    intro position raw
    cases raw
    rfl

def firstUnit : compiler.QueueUnit := ⟨firstPosition, PUnit.unit⟩

def middleUnit : compiler.QueueUnit := ⟨middlePosition, PUnit.unit⟩

def recurrentUnit : compiler.QueueUnit :=
  ⟨recurrentPosition, PUnit.unit⟩

@[simp] theorem trace_positions_eq :
    tracePositions game =
      [firstPosition, middlePosition, recurrentPosition] := by
  rfl

@[simp] theorem compiled_queue_eq :
    compiler.queue = [firstUnit, middleUnit, recurrentUnit] := by
  rfl

@[simp] theorem compiled_queue_length : compiler.queue.length = 3 := by
  rw [compiled_queue_eq]
  rfl

theorem firstUnit_mem_queue : firstUnit ∈ compiler.queue := by
  simp

theorem middleUnit_mem_queue : middleUnit ∈ compiler.queue := by
  simp

theorem recurrentUnit_mem_queue : recurrentUnit ∈ compiler.queue := by
  simp

/-- Recurrent state and seed values do not erase actual occurrence identity. -/
theorem recurrent_units_are_distinct : firstUnit ≠ recurrentUnit :=
  SourceOwnedOccurrenceRateCompiler.QueueUnit.ne_of_position_ne
    compiler recurrent_positions_are_distinct

@[simp] theorem recurrent_unit_states_eq :
    firstUnit.state = recurrentUnit.state :=
  rfl

@[simp] theorem recurrent_unit_seeds_eq :
    firstUnit.seed compiler = recurrentUnit.seed compiler :=
  rfl

def firstExactUnit : compiler.ExactQueueUnit :=
  compiler.exactQueueUnitOf firstPosition PUnit.unit

def middleExactUnit : compiler.ExactQueueUnit :=
  compiler.exactQueueUnitOf middlePosition PUnit.unit

def recurrentExactUnit : compiler.ExactQueueUnit :=
  compiler.exactQueueUnitOf recurrentPosition PUnit.unit

@[simp] theorem first_sourceSeed_eq_focal :
    firstExactUnit.sourceSeed compiler = focalSeed := by
  apply Subtype.ext
  rfl

@[simp] theorem recurrent_sourceSeed_eq_focal :
    recurrentExactUnit.sourceSeed compiler = focalSeed := by
  apply Subtype.ext
  rfl

theorem every_exact_unit_has_focal_lineage
    (unit : compiler.ExactQueueUnit) :
    unit.lineage compiler = lineageOf game.source focalSeed :=
  unit.lineage_eq_focal compiler

/-! Canonical bounded readouts needed by the downstream prefix fixture. -/

@[simp] theorem queue_take_one :
    compiler.queue.take 1 = [firstUnit] := by
  rw [compiled_queue_eq]
  rfl

@[simp] theorem queue_take_two :
    compiler.queue.take 2 = [firstUnit, middleUnit] := by
  rw [compiled_queue_eq]
  rfl

@[simp] theorem queue_take_three :
    compiler.queue.take 3 = [firstUnit, middleUnit, recurrentUnit] := by
  rw [compiled_queue_eq]
  rfl

@[simp] theorem queue_drop_two :
    compiler.queue.drop 2 = [recurrentUnit] := by
  rw [compiled_queue_eq]
  rfl

end
end M10OccurrenceCapacityProcessFixture
end Society
end ProcessGame
end SaturationMonoid
