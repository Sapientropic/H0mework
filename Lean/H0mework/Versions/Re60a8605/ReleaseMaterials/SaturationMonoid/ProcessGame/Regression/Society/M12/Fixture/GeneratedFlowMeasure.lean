/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M12.Fixture.GeneratedFlowObserver
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M11.GeneratedSocialSpaceRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Probability.Measure.SourceOwnedFlowMeasureCompiler

/-!
# M12 generated flow-measure fixture

The exact three-crossing M11 space generates three source measures from its
dependent flow payload: monthly-event mass, uniform occurrence mass, and zero
mass.  All three retain the same exact crossing trace; changing the measure
compiler changes coefficients, never occurrence support authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M12GeneratedFlowMeasureFixture

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity Space
open Probability Measure
open M10OccurrenceCapacityProcessFixture
open M11GeneratedSocialSpaceCrossingFixture
open M11GeneratedSocialSpaceRegression

/-- Monthly trip count read directly from each crossing's dependent payload. -/
def monthlyMeasureCompiler :
    SourceOwnedFiniteMeasureCompilerAt socialSpace where
  weightFromFlow := fun _crossing payload => payload.monthlyEvents

def monthlyMeasure : SourceGeneratedFiniteMeasureAt monthlyMeasureCompiler :=
  SourceGeneratedFiniteMeasureAt.generate monthlyMeasureCompiler

@[simp] theorem monthlyCompiler_first_weight :
    monthlyMeasureCompiler.coefficient firstCrossing = 8754 :=
  rfl

@[simp] theorem monthlyCompiler_middle_weight :
    monthlyMeasureCompiler.coefficient middleCrossing = 9070 :=
  rfl

@[simp] theorem monthlyCompiler_recurrent_weight :
    monthlyMeasureCompiler.coefficient recurrentCrossing = 2757 :=
  rfl

@[simp] theorem monthly_first_weight :
    monthlyMeasure.coefficient firstCrossing = 8754 :=
  rfl

@[simp] theorem monthly_middle_weight :
    monthlyMeasure.coefficient middleCrossing = 9070 :=
  rfl

@[simp] theorem monthly_recurrent_weight :
    monthlyMeasure.coefficient recurrentCrossing = 2757 :=
  rfl

@[simp] theorem monthly_totalMass :
    monthlyMeasure.totalMass = 20581 := by
  change monthlyMeasureCompiler.totalMass = 20581
  rw [monthlyMeasureCompiler.totalMass_eq_crossingTrace_foldr,
    crossingTrace_exact]
  simp only [List.foldr_cons, List.foldr_nil]
  rw [show monthlyMeasureCompiler.coefficient firstCrossing = 8754 by rfl,
    show monthlyMeasureCompiler.coefficient middleCrossing = 9070 by rfl,
    show monthlyMeasureCompiler.coefficient recurrentCrossing = 2757 by rfl]
  norm_num

@[simp] theorem monthly_occurrenceTrace :
    monthlyMeasure.measure.occurrenceTrace =
      [firstCrossing, middleCrossing, recurrentCrossing] := by
  rfl

/-- Same exact trace, one unit of mass per actual crossing occurrence. -/
def uniformMeasureCompiler :
    SourceOwnedFiniteMeasureCompilerAt socialSpace where
  weightFromFlow := fun _crossing _payload => ⟨1, by decide⟩

def uniformMeasure : SourceGeneratedFiniteMeasureAt uniformMeasureCompiler :=
  SourceGeneratedFiniteMeasureAt.generate uniformMeasureCompiler

@[simp] theorem uniformCompiler_coefficient
    (crossing : crossingCompiler.ExactCrossing) :
    uniformMeasureCompiler.coefficient crossing = 1 :=
  rfl

@[simp] theorem uniform_totalMass : uniformMeasure.totalMass = 3 := by
  change uniformMeasureCompiler.totalMass = 3
  rw [uniformMeasureCompiler.totalMass_eq_crossingTrace_foldr,
    crossingTrace_exact]
  simp only [List.foldr_cons, List.foldr_nil, uniformCompiler_coefficient]
  apply Subtype.ext
  norm_num [NNRat.coe_add, NNRat.coe_natCast]

@[simp] theorem uniform_occurrenceTrace :
    uniformMeasure.measure.occurrenceTrace =
      [firstCrossing, middleCrossing, recurrentCrossing] := by
  rfl

/-- Zero weighting does not delete occurrences from the generated inventory. -/
def zeroMeasureCompiler :
    SourceOwnedFiniteMeasureCompilerAt socialSpace where
  weightFromFlow := fun _crossing _payload => 0

def zeroMeasure : SourceGeneratedFiniteMeasureAt zeroMeasureCompiler :=
  SourceGeneratedFiniteMeasureAt.generate zeroMeasureCompiler

@[simp] theorem zeroCompiler_coefficient
    (crossing : crossingCompiler.ExactCrossing) :
    zeroMeasureCompiler.coefficient crossing = 0 :=
  rfl

@[simp] theorem zero_totalMass : zeroMeasure.totalMass = 0 := by
  change zeroMeasureCompiler.totalMass = 0
  rw [zeroMeasureCompiler.totalMass_eq_crossingTrace_foldr,
    crossingTrace_exact]
  norm_num [SourceOwnedFiniteMeasureCompilerAt.coefficient,
    zeroMeasureCompiler]

@[simp] theorem zero_support : zeroMeasure.support = [] :=
  rfl

@[simp] theorem zero_occurrenceTrace_retained :
    zeroMeasure.measure.occurrenceTrace =
      [firstCrossing, middleCrossing, recurrentCrossing] := by
  rfl

theorem zero_weight_does_not_erase_recurrence :
    zeroMeasure.measure.occurrenceTrace.length = 3 ∧
      firstCrossing ≠ recurrentCrossing :=
  ⟨rfl, SourceOwnedCrossingCompiler.ExactCrossing.ne_of_position_ne
    recurrent_positions_are_distinct⟩

/-- Measure compiler is an independent source coordinate: monthly and uniform
weights differ on the exact first crossing while their occurrence trace is
identical. -/
theorem same_sourceTrace_different_measure :
    monthlyMeasure.measure.occurrenceTrace =
        uniformMeasure.measure.occurrenceTrace ∧
      monthlyMeasure.coefficient firstCrossing ≠
        uniformMeasure.coefficient firstCrossing := by
  constructor
  · rfl
  · decide

end
end M12GeneratedFlowMeasureFixture
end Society
end ProcessGame
end SaturationMonoid
