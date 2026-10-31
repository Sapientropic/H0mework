import H0mework.Foundation.Agency.Lineage
import Mathlib.Data.List.Nodup

/-!
# Source-generated occurrence-rate queue

An occurrence arrival queue is compiled from the complete finite trace of one
fixed `ProcessGame`.  Its carrier is indexed by actual positions in that trace,
not merely by state values: two visits to the same state remain two distinct
occurrence units.  A source-owned compiler supplies a finite exhaustive unit
inventory at every position, compiles every raw unit to an exact seed incidence
at the state stored at that position, and proves that every generated unit has
the same lineage as one focal exact `SourceSeed`.

The sole queue is definitionally

```text
tracePositions game |>.flatMap compiler.unitsAt
```

`TracePosition game` is `Fin game.occurrence.trace.length`; it is only the
dependent coordinate of the existing source trace, never a second occurrence
or a caller-selected finite horizon.  There is no caller queue, prefix, rate,
phase label, or fixed finite scope in this module.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Capacity

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe uSource uState uSeed uLineage uUnit uCarrier

variable {Source : Type uSource}
variable {State : Type uState}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {Seed : Type uSeed}
variable {SeedAt : Source → State → Seed → Prop}
variable {Lineage : Source → Type uLineage}
variable {lineageOf : ∀ source,
  SourceSeed occurrenceOf Seed SeedAt source → Lineage source}
variable {focal : SourceSeed occurrenceOf Seed SeedAt game.source}

noncomputable section

/-- A source-derived coordinate in the existing process trace.  Its bound is
the actual trace length, not a fixed or caller-supplied horizon. -/
abbrev TracePosition
    (game : SaturationMonoid.ProcessGame occurrenceOf) :=
  Fin game.occurrence.trace.length

/-- State visited at one exact source-trace position. -/
def stateAt
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (position : TracePosition game) : State :=
  game.occurrence.trace.get position

/-- A trace position automatically supplies exact membership of its stored
state in the one source trace. -/
theorem stateAt_mem
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (position : TracePosition game) :
    stateAt game position ∈ game.occurrence.trace :=
  List.get_mem game.occurrence.trace position

/-- Canonical chronological enumeration of all positions in the source trace. -/
def tracePositions
    (game : SaturationMonoid.ProcessGame occurrenceOf) :
    List (TracePosition game) :=
  List.finRange game.occurrence.trace.length

/-- Every source-derived trace position occurs in the canonical enumeration. -/
theorem tracePosition_mem
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (position : TracePosition game) :
    position ∈ tracePositions game := by
  unfold tracePositions
  exact List.mem_finRange position

/-- Canonical trace positions do not repeat. -/
theorem tracePositions_nodup
    (game : SaturationMonoid.ProcessGame occurrenceOf) :
    (tracePositions game).Nodup := by
  unfold tracePositions
  exact List.nodup_finRange game.occurrence.trace.length

/-- Source-owned finite occurrence-unit compiler relative to one focal exact
seed.  `UnitAt` varies with the actual trace position, so recurrent visits to
one state retain distinct occurrence identities. -/
structure SourceOwnedOccurrenceRateCompiler
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type uSeed)
    (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type uLineage)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source)
    (focal : SourceSeed occurrenceOf Seed SeedAt game.source) :
    Type (max uState uSeed uLineage (uUnit + 1)) where
  UnitAt : TracePosition game → Type uUnit
  unitInventoryAt : (position : TracePosition game) →
    List (UnitAt position)
  unitInventory_nodup : (position : TracePosition game) →
    (unitInventoryAt position).Nodup
  raw_unit_mem : (position : TracePosition game) →
    (unit : UnitAt position) → unit ∈ unitInventoryAt position
  seedAt : (position : TracePosition game) → UnitAt position → Seed
  seedIncidence : (position : TracePosition game) →
    (unit : UnitAt position) →
      SeedAt game.source (stateAt game position) (seedAt position unit)
  lineage_eq_focal :
    (position : TracePosition game) →
    (unit : UnitAt position) →
      lineageOf game.source
          (⟨seedAt position unit,
            ⟨stateAt game position,
              stateAt_mem game position,
              seedIncidence position unit⟩⟩ :
            SourceSeed occurrenceOf Seed SeedAt game.source) =
        lineageOf game.source focal

namespace SourceOwnedOccurrenceRateCompiler

variable
  (compiler : SourceOwnedOccurrenceRateCompiler
    game Seed SeedAt Lineage lineageOf focal)

/-- Uniform dependent carrier of one compiler-owned position unit. -/
abbrev QueueUnit := Sigma compiler.UnitAt

/-- Compile the exhaustive dependent inventory at one trace position into the
uniform queue carrier. -/
def unitsAt (position : TracePosition game) : List compiler.QueueUnit :=
  (compiler.unitInventoryAt position).map fun unit => ⟨position, unit⟩

/-- Every raw unit generated at a position occurs in that position's compiled
inventory. -/
theorem unit_mem
    (position : TracePosition game)
    (unit : compiler.UnitAt position) :
    (⟨position, unit⟩ : compiler.QueueUnit) ∈ compiler.unitsAt position :=
  List.mem_map.mpr ⟨unit, compiler.raw_unit_mem position unit, rfl⟩

/-- Each per-position compiled inventory remains duplicate-free. -/
theorem unitsAt_nodup (position : TracePosition game) :
    (compiler.unitsAt position).Nodup := by
  exact List.Nodup.map
    (fun left right equality => by injection equality)
    (compiler.unitInventory_nodup position)

/-- The sole source-generated arrival queue, in canonical trace-position
order. -/
def queue : List compiler.QueueUnit :=
  (tracePositions game).flatMap compiler.unitsAt

/-- Global queue integrity is a law of the source compiler, not a caller
deduplication pass. -/
theorem queue_nodup : compiler.queue.Nodup :=
  List.Nodup.sigma (tracePositions_nodup game) compiler.unitInventory_nodup

/-- Exact focal seed retained by this compiler. -/
def focalSeed : SourceSeed occurrenceOf Seed SeedAt game.source :=
  focal

namespace QueueUnit

variable (unit : compiler.QueueUnit)

/-- Actual source-trace position carried by this queue unit. -/
def position : TracePosition game := unit.1

/-- State stored at this exact source-trace position. -/
def state : State := stateAt game unit.position

def raw : compiler.UnitAt unit.position := unit.2

/-- Seed generated at this exact queue position. -/
def seed : Seed := compiler.seedAt unit.position unit.raw

/-- Exact state/seed incidence generated by the compiler. -/
theorem seedIncidence : SeedAt game.source unit.state unit.seed :=
  compiler.seedIncidence unit.position unit.raw

/-- Upgrade a queue unit to an exact source seed.  State membership is recovered
from `List.get_mem` at the carried position, never supplied by a caller. -/
def sourceSeed : SourceSeed occurrenceOf Seed SeedAt game.source :=
  ⟨unit.seed,
    ⟨unit.state,
      stateAt_mem game unit.position,
      unit.seedIncidence⟩⟩

/-- Lineage readout of one exact position-indexed queue unit. -/
def lineage : Lineage game.source :=
  lineageOf game.source (QueueUnit.sourceSeed compiler unit)

/-- Every generated unit belongs to the focal lineage. -/
theorem lineage_eq_focal :
    QueueUnit.lineage compiler unit = lineageOf game.source focal :=
  compiler.lineage_eq_focal unit.position unit.raw

/-- Distinct actual trace positions cannot collapse to the same queue unit,
even when their stored states and generated seeds coincide. -/
theorem ne_of_position_ne
    {left right : compiler.QueueUnit}
    (position_ne : left.position ≠ right.position) :
    left ≠ right := by
  intro unit_eq
  exact position_ne (congrArg Sigma.fst unit_eq)

end QueueUnit

/-- Exact queue occurrence: a position-indexed compiler unit together with
membership in the sole source-generated queue. -/
def ExactQueueUnit :=
  { unit : compiler.QueueUnit // unit ∈ compiler.queue }

namespace ExactQueueUnit

variable (unit : compiler.ExactQueueUnit)

/-- Queue membership is retained as a direct readout. -/
theorem queueMembership : unit.1 ∈ compiler.queue :=
  unit.2

/-- Every exact queue unit comes from one canonical actual trace position and
one member of that position's exhaustive compiler inventory. -/
theorem provenance :
    ∃ position : TracePosition game,
      position ∈ tracePositions game ∧
        ∃ raw : compiler.UnitAt position,
          raw ∈ compiler.unitInventoryAt position ∧
            (⟨position, raw⟩ : compiler.QueueUnit) = unit.1 := by
  rcases List.mem_flatMap.mp unit.2 with ⟨position, positionMem, packedMem⟩
  rcases List.mem_map.mp packedMem with ⟨raw, rawMem, packedEq⟩
  exact ⟨position, positionMem, raw, rawMem, packedEq⟩

/-- Exact source-trace position recovered from the queue unit itself. -/
def position : TracePosition game := unit.1.position

/-- Exact state readout at this queue occurrence's trace position. -/
def state : State := unit.1.state

/-- Exact source seed generated by this queue occurrence. -/
def sourceSeed : SourceSeed occurrenceOf Seed SeedAt game.source :=
  QueueUnit.sourceSeed compiler unit.1

/-- Exact lineage of this queue occurrence. -/
def lineage : Lineage game.source :=
  lineageOf game.source (ExactQueueUnit.sourceSeed compiler unit)

theorem lineage_eq_focal :
    ExactQueueUnit.lineage compiler unit = lineageOf game.source focal :=
  QueueUnit.lineage_eq_focal compiler unit.1

end ExactQueueUnit

/-- Generate an exact queue occurrence from any unit in one source-derived
trace position's exhaustive compiler inventory. -/
def exactQueueUnitOf
    (position : TracePosition game)
    (unit : compiler.UnitAt position) : compiler.ExactQueueUnit :=
  ⟨⟨position, unit⟩,
    List.mem_flatMap.mpr
      ⟨position, tracePosition_mem game position,
        compiler.unit_mem position unit⟩⟩

@[simp] theorem exactQueueUnitOf_sourceSeed
    (position : TracePosition game)
    (unit : compiler.UnitAt position) :
    ExactQueueUnit.sourceSeed compiler
        (compiler.exactQueueUnitOf position unit) =
      ⟨compiler.seedAt position unit,
        ⟨stateAt game position,
          stateAt_mem game position,
          compiler.seedIncidence position unit⟩⟩ := by
  apply Subtype.ext
  rfl

/-- Zero-field readout of one canonical fold over the compiler-owned queue. -/
inductive CanonicalQueueFoldReadout
    {Carrier : Type uCarrier}
    (initial : Carrier)
    (step : compiler.QueueUnit → Carrier → Carrier) : Type
      (max uCarrier uUnit uState) where
  | generated

namespace CanonicalQueueFoldReadout

variable {Carrier : Type uCarrier}
variable {initial : Carrier}
variable {step : compiler.QueueUnit → Carrier → Carrier}

/-- Sole canonical fold-readout producer. -/
def generate : compiler.CanonicalQueueFoldReadout initial step :=
  .generated

/-- Fold value is always recomputed from the exact compiler-owned queue. -/
def value
    (_readout : compiler.CanonicalQueueFoldReadout initial step) : Carrier :=
  compiler.queue.foldr step initial

/-- Every readout token is the unique generated fold seal. -/
theorem eq_generated
    (readout : compiler.CanonicalQueueFoldReadout initial step) :
    readout = .generated := by
  cases readout
  rfl

end CanonicalQueueFoldReadout

end SourceOwnedOccurrenceRateCompiler

end
end Capacity
end Society
end ProcessGame
end SaturationMonoid
