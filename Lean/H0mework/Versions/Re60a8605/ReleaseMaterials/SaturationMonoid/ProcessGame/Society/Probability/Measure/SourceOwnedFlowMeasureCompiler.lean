import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Space.GeneratedSocialSpace
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Probability.Measure.FiniteObserverMeasure

/-!
# Source-owned finite flow measure compiler

A fixed compiler assigns a nonnegative rational coefficient only by reading
the dependent flow payload of one exact M11 crossing.  Its generated weighted
list is definitionally the canonical social-space crossing trace mapped with
that coefficient.  It accepts no externally supplied finite carrier,
completion witness, scaling datum, probability value, or total-mass premise.

The accompanying zero-field seal distinguishes this source-owned producer
from an arbitrary neutral `FiniteObserverMeasure` value.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Probability
namespace Measure

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity Space

universe uSource uState uSeed uLineage uUnit
universe uSiteSeed uSiteLineage uFlow
universe uBoundarySeed uBoundaryLineage uBoundaryClass

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
variable {rateCompiler : SourceOwnedOccurrenceRateCompiler
  game Seed SeedAt Lineage lineageOf focal}
variable {crossingCompiler : SourceOwnedCrossingCompiler rateCompiler}
variable {socialSpace : SourceGeneratedSocialSpaceAt crossingCompiler}

noncomputable section

/-- Fixed source law for finite crossing mass.  Its sole field can inspect
only one exact crossing and the dependent flow payload generated at that same
crossing. -/
structure SourceOwnedFiniteMeasureCompilerAt
    (socialSpace : SourceGeneratedSocialSpaceAt crossingCompiler) where
  weightFromFlow : (crossing : crossingCompiler.ExactCrossing) →
    crossingCompiler.FlowPayloadAt crossing → ℚ≥0

namespace SourceOwnedFiniteMeasureCompilerAt

variable
  (measureCompiler : SourceOwnedFiniteMeasureCompilerAt socialSpace)

/-- Exact coefficient generated from the crossing's own flow payload. -/
def coefficient (crossing : crossingCompiler.ExactCrossing) : ℚ≥0 :=
  measureCompiler.weightFromFlow crossing
    (crossing.flowPayload crossingCompiler)

theorem coefficient_eq_weightFromFlow
    (crossing : crossingCompiler.ExactCrossing) :
    measureCompiler.coefficient crossing =
      measureCompiler.weightFromFlow crossing
        (crossing.flowPayload crossingCompiler) :=
  rfl

theorem coefficient_nonnegative
    (crossing : crossingCompiler.ExactCrossing) :
    0 ≤ measureCompiler.coefficient crossing :=
  (measureCompiler.coefficient crossing).2

/-- Exact weighted occurrence generated at one crossing. -/
def weightedCrossing (crossing : crossingCompiler.ExactCrossing) :
    crossingCompiler.ExactCrossing × ℚ≥0 :=
  (crossing, measureCompiler.coefficient crossing)

@[simp] theorem weightedCrossing_occurrence
    (crossing : crossingCompiler.ExactCrossing) :
    (measureCompiler.weightedCrossing crossing).1 = crossing :=
  rfl

@[simp] theorem weightedCrossing_coefficient
    (crossing : crossingCompiler.ExactCrossing) :
    (measureCompiler.weightedCrossing crossing).2 =
      measureCompiler.coefficient crossing :=
  rfl

/-- Sole generated weighted list, preserving exact crossing order and
occurrence identity. -/
def weightedCrossings :
    List (crossingCompiler.ExactCrossing × ℚ≥0) :=
  socialSpace.crossingTrace.map measureCompiler.weightedCrossing

theorem weightedCrossings_eq_crossingTrace_map :
    measureCompiler.weightedCrossings =
      socialSpace.crossingTrace.map measureCompiler.weightedCrossing :=
  rfl

/-- Every exact crossing, including one with zero coefficient, remains in the
generated weighted list. -/
theorem weightedCrossing_mem
    (crossing : crossingCompiler.ExactCrossing) :
    measureCompiler.weightedCrossing crossing ∈
      measureCompiler.weightedCrossings :=
  List.mem_map.mpr
    ⟨crossing, socialSpace.exactCrossing_mem crossing, rfl⟩

/-- Source-generated neutral measure readout. -/
def generatedMeasure :
    FiniteObserverMeasure crossingCompiler.ExactCrossing where
  weightedOccurrences := measureCompiler.weightedCrossings
  occurrence_nodup := by
    unfold weightedCrossings
    simpa [List.map_map, Function.comp_def, weightedCrossing] using
      socialSpace.crossingTrace_nodup

/-- Its occurrence trace is exactly the M11 canonical crossing trace. -/
theorem occurrenceTrace_eq_crossingTrace :
    measureCompiler.generatedMeasure.occurrenceTrace =
      socialSpace.crossingTrace := by
  unfold generatedMeasure FiniteObserverMeasure.occurrenceTrace
    weightedCrossings
  simp [List.map_map, Function.comp_def, weightedCrossing]

theorem generated_occurrenceTrace_nodup :
    measureCompiler.generatedMeasure.occurrenceTrace.Nodup :=
  measureCompiler.generatedMeasure.occurrenceTrace_nodup

theorem generated_weightedCrossings_nodup :
    measureCompiler.generatedMeasure.weightedOccurrences.Nodup :=
  measureCompiler.generatedMeasure.weightedOccurrences_nodup

/-- Positive support is derived from the weighted crossing list. -/
def support : List crossingCompiler.ExactCrossing :=
  measureCompiler.generatedMeasure.support

theorem support_nodup : measureCompiler.support.Nodup :=
  measureCompiler.generatedMeasure.support_nodup

/-- Positive support cannot introduce a crossing outside the generated M11
trace. -/
theorem support_subset_crossingTrace
    {crossing : crossingCompiler.ExactCrossing}
    (membership : crossing ∈ measureCompiler.support) :
    crossing ∈ socialSpace.crossingTrace := by
  rw [← measureCompiler.occurrenceTrace_eq_crossingTrace]
  exact measureCompiler.generatedMeasure.support_subset_occurrenceTrace
    membership

/-- Zero coefficients remain as exact weighted occurrences; they are not
dropped from the source inventory before mass is folded. -/
theorem zeroWeight_retained
    (crossing : crossingCompiler.ExactCrossing)
    (zeroWeight : measureCompiler.coefficient crossing = 0) :
    (crossing, 0) ∈
      measureCompiler.generatedMeasure.weightedOccurrences := by
  have generated := measureCompiler.weightedCrossing_mem crossing
  simpa [generatedMeasure, weightedCrossing, zeroWeight] using generated

/-- Distinct exact crossings remain distinct weighted occurrences even when
their coefficients coincide. -/
theorem weightedCrossing_ne_of_crossing_ne
    {left right : crossingCompiler.ExactCrossing}
    (crossing_ne : left ≠ right) :
    measureCompiler.weightedCrossing left ≠
      measureCompiler.weightedCrossing right := by
  intro weighted_eq
  exact crossing_ne (congrArg Prod.fst weighted_eq)

/-- Recurrent visits cannot collapse when their actual trace positions differ. -/
theorem weightedCrossing_ne_of_position_ne
    {left right : crossingCompiler.ExactCrossing}
    (position_ne :
      SourceOwnedOccurrenceRateCompiler.ExactQueueUnit.position
          rateCompiler left ≠
        SourceOwnedOccurrenceRateCompiler.ExactQueueUnit.position
          rateCompiler right) :
    measureCompiler.weightedCrossing left ≠
      measureCompiler.weightedCrossing right :=
  measureCompiler.weightedCrossing_ne_of_crossing_ne
    (SourceOwnedCrossingCompiler.ExactCrossing.ne_of_position_ne position_ne)

/-- Empty source trace and empty weighted list are equivalent; no default
mass is inserted. -/
theorem weightedCrossings_eq_nil_iff :
    measureCompiler.weightedCrossings = [] ↔
      socialSpace.crossingTrace = [] := by
  unfold weightedCrossings
  simp

/-- Canonical total flow mass. -/
def totalMass : ℚ≥0 :=
  measureCompiler.generatedMeasure.totalMass

/-- Canonical exact-event mass. -/
def eventMass
    (event : crossingCompiler.ExactCrossing → Prop)
    [DecidablePred event] : ℚ≥0 :=
  measureCompiler.generatedMeasure.eventMass event

theorem eventMass_le_totalMass
    (event : crossingCompiler.ExactCrossing → Prop)
    [DecidablePred event] :
    measureCompiler.eventMass event ≤ measureCompiler.totalMass :=
  measureCompiler.generatedMeasure.eventMass_le_totalMass event

@[simp] theorem eventMass_false :
    measureCompiler.eventMass (fun _crossing => False) = 0 :=
  measureCompiler.generatedMeasure.eventMass_false

@[simp] theorem eventMass_true :
    measureCompiler.eventMass (fun _crossing => True) =
      measureCompiler.totalMass :=
  measureCompiler.generatedMeasure.eventMass_true

/-- Total mass is exactly the canonical fold over the source crossing trace. -/
theorem totalMass_eq_crossingTrace_foldr :
    measureCompiler.totalMass =
      socialSpace.crossingTrace.foldr
        (fun crossing accumulated =>
          measureCompiler.coefficient crossing + accumulated) 0 := by
  change (socialSpace.crossingTrace.map measureCompiler.weightedCrossing).foldr
      (fun weighted accumulated => weighted.2 + accumulated) 0 = _
  rw [List.foldr_map]
  rfl

/-- Empty source crossing trace generates zero total and event mass. -/
theorem empty_crossingTrace_generates_zero
    (empty : socialSpace.crossingTrace = [])
    (event : crossingCompiler.ExactCrossing → Prop)
    [DecidablePred event] :
    measureCompiler.totalMass = 0 ∧
      measureCompiler.eventMass event = 0 := by
  have weightedEmpty : measureCompiler.weightedCrossings = [] :=
    measureCompiler.weightedCrossings_eq_nil_iff.mpr empty
  constructor
  · rw [measureCompiler.totalMass_eq_crossingTrace_foldr, empty]
    rfl
  · change measureCompiler.weightedCrossings.foldr
        (fun weighted accumulated =>
          if event weighted.1 then weighted.2 + accumulated else accumulated)
        0 = 0
    rw [weightedEmpty]
    rfl

/-- Direct use of the existing M10 canonical queue-fold token. -/
def canonicalMassFoldReadout :
    rateCompiler.CanonicalQueueFoldReadout (0 : ℚ≥0)
      (fun unit accumulated =>
        measureCompiler.coefficient
            (crossingCompiler.exactCrossingOf unit) + accumulated) :=
  socialSpace.canonicalFoldReadout (0 : ℚ≥0)
    (fun crossing accumulated =>
      measureCompiler.coefficient crossing + accumulated)

theorem canonicalMassFoldValue_eq_totalMass :
    SourceOwnedOccurrenceRateCompiler.CanonicalQueueFoldReadout.value
        rateCompiler measureCompiler.canonicalMassFoldReadout =
      measureCompiler.totalMass := by
  unfold canonicalMassFoldReadout
  rw [socialSpace.canonicalFoldReadout_value_eq_crossingTrace_foldr]
  exact measureCompiler.totalMass_eq_crossingTrace_foldr.symm

/-- A one-field compiler is uniquely determined by its dependent flow-weight
law, not by a submitted support or total mass. -/
@[ext] theorem ext
    (left right : SourceOwnedFiniteMeasureCompilerAt socialSpace)
    (weights : ∀ crossing payload,
      left.weightFromFlow crossing payload =
        right.weightFromFlow crossing payload) :
    left = right := by
  cases left with
  | mk leftWeight =>
      cases right with
      | mk rightWeight =>
          congr
          funext crossing payload
          exact weights crossing payload

end SourceOwnedFiniteMeasureCompilerAt

/-! ## Source-generated seal -/

/-- Zero-field admission seal distinguishing the unique generated finite
measure from arbitrary neutral finite masses. -/
inductive SourceGeneratedFiniteMeasureAt
    (measureCompiler : SourceOwnedFiniteMeasureCompilerAt socialSpace) :
    Type where
  | private generated

namespace SourceGeneratedFiniteMeasureAt

/-- Sole source-generated measure producer. -/
def generate
    (measureCompiler : SourceOwnedFiniteMeasureCompilerAt socialSpace) :
    SourceGeneratedFiniteMeasureAt measureCompiler :=
  .generated

theorem eq_generate
    {measureCompiler : SourceOwnedFiniteMeasureCompilerAt socialSpace}
    (sourceMeasure : SourceGeneratedFiniteMeasureAt measureCompiler) :
    sourceMeasure = generate measureCompiler := by
  cases sourceMeasure
  rfl

variable
  {measureCompiler : SourceOwnedFiniteMeasureCompilerAt socialSpace}
  (sourceMeasure : SourceGeneratedFiniteMeasureAt measureCompiler)

/-- Neutral mass readout of this exact source-generated seal. -/
def measure
    (_sourceMeasure : SourceGeneratedFiniteMeasureAt measureCompiler) :
    FiniteObserverMeasure crossingCompiler.ExactCrossing :=
  measureCompiler.generatedMeasure

theorem measure_eq_generatedMeasure :
    sourceMeasure.measure = measureCompiler.generatedMeasure :=
  rfl

theorem occurrenceTrace_eq_crossingTrace :
    sourceMeasure.measure.occurrenceTrace = socialSpace.crossingTrace :=
  measureCompiler.occurrenceTrace_eq_crossingTrace

def coefficient
    (_sourceMeasure : SourceGeneratedFiniteMeasureAt measureCompiler)
    (crossing : crossingCompiler.ExactCrossing) : ℚ≥0 :=
  measureCompiler.coefficient crossing

def support
    (_sourceMeasure : SourceGeneratedFiniteMeasureAt measureCompiler) :
    List crossingCompiler.ExactCrossing :=
  measureCompiler.support

theorem support_nodup : sourceMeasure.support.Nodup :=
  measureCompiler.support_nodup

def totalMass
    (_sourceMeasure : SourceGeneratedFiniteMeasureAt measureCompiler) : ℚ≥0 :=
  measureCompiler.totalMass

def eventMass
    (_sourceMeasure : SourceGeneratedFiniteMeasureAt measureCompiler)
    (event : crossingCompiler.ExactCrossing → Prop)
    [DecidablePred event] : ℚ≥0 :=
  measureCompiler.eventMass event

theorem eventMass_eq_measure_eventMass
    (event : crossingCompiler.ExactCrossing → Prop)
    [DecidablePred event] :
    sourceMeasure.eventMass event = sourceMeasure.measure.eventMass event :=
  rfl

theorem support_subset_crossingTrace
    {crossing : crossingCompiler.ExactCrossing}
    (membership : crossing ∈ sourceMeasure.support) :
    crossing ∈ socialSpace.crossingTrace :=
  SourceOwnedFiniteMeasureCompilerAt.support_subset_crossingTrace
    measureCompiler membership

theorem eventMass_le_totalMass
    (event : crossingCompiler.ExactCrossing → Prop)
    [DecidablePred event] :
    sourceMeasure.eventMass event ≤ sourceMeasure.totalMass :=
  SourceOwnedFiniteMeasureCompilerAt.eventMass_le_totalMass
    measureCompiler event

theorem totalMass_eq_crossingTrace_foldr :
    sourceMeasure.totalMass =
      socialSpace.crossingTrace.foldr
        (fun crossing accumulated =>
          sourceMeasure.coefficient crossing + accumulated) 0 :=
  measureCompiler.totalMass_eq_crossingTrace_foldr

end SourceGeneratedFiniteMeasureAt

end
end Measure
end Probability
end Society
end ProcessGame
end SaturationMonoid
