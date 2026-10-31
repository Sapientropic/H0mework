/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M12.Fixture.GeneratedFlowMeasure
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Probability.Kernel.NormalizedObserverKernelFold
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic

/-!
# M12 observer-kernel geometry regression

One source measure, one exact event and one visible label produce opposite
half-threshold predictions solely because observer kernel geometry changes.
The coarse fibre contains all three crossings; the fine fibre retains only
the recurrent false-state pair.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M12ObserverGeometryRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity Space Observer
open Probability Measure Kernel
open M10OccurrenceCapacityProcessFixture
open M11GeneratedSocialSpaceCrossingFixture
open M11GeneratedSocialSpaceRegression
open M12GeneratedFlowObserverFixture
open M12GeneratedFlowMeasureFixture

def coarseMonthlyFold : SourceGeneratedObserverKernelFoldAt
    monthlyMeasure coarseObserver firstOccurrenceEvent :=
  SourceGeneratedObserverKernelFoldAt.generate
    monthlyMeasure coarseObserver firstOccurrenceEvent

def fineMonthlyFold : SourceGeneratedObserverKernelFoldAt
    monthlyMeasure fineObserver firstOccurrenceEvent :=
  SourceGeneratedObserverKernelFoldAt.generate
    monthlyMeasure fineObserver firstOccurrenceEvent

def coarseUniformFold : SourceGeneratedObserverKernelFoldAt
    uniformMeasure coarseObserver firstOccurrenceEvent :=
  SourceGeneratedObserverKernelFoldAt.generate
    uniformMeasure coarseObserver firstOccurrenceEvent

@[simp] theorem coarse_conditioned_fibre :
    coarseMonthlyFold.fibre .conditioned =
      [firstCrossing, middleCrossing, recurrentCrossing] := by
  rfl

@[simp] theorem fine_conditioned_fibre :
    fineMonthlyFold.fibre .conditioned =
      [firstCrossing, recurrentCrossing] := by
  rfl

@[simp] theorem fine_outside_fibre :
    fineMonthlyFold.fibre .outside = [middleCrossing] := by
  rfl

@[simp] theorem coarse_event_fibre :
    coarseMonthlyFold.eventFibre .conditioned = [firstCrossing] := by
  rfl

@[simp] theorem fine_event_fibre :
    fineMonthlyFold.eventFibre .conditioned = [firstCrossing] := by
  rfl

@[simp] theorem coarse_fibreMass :
    coarseMonthlyFold.fibreMass .conditioned = 20581 := by
  unfold SourceGeneratedObserverKernelFoldAt.fibreMass
    SourceGeneratedFiniteMeasureAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.generatedMeasure
    FiniteObserverMeasure.eventMass
  change monthlyMeasureCompiler.weightedCrossings.foldr
    (fun weighted accumulated =>
      if coarseObserver.forget weighted.1 = .conditioned then
        weighted.2 + accumulated else accumulated) 0 = 20581
  rw [monthlyMeasureCompiler.weightedCrossings_eq_crossingTrace_map,
    crossingTrace_exact]
  simp
  norm_num

@[simp] theorem coarse_eventMass :
    coarseMonthlyFold.eventMass .conditioned = 8754 := by
  unfold SourceGeneratedObserverKernelFoldAt.eventMass
    SourceGeneratedFiniteMeasureAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.generatedMeasure
    FiniteObserverMeasure.eventMass
  change monthlyMeasureCompiler.weightedCrossings.foldr
    (fun weighted accumulated =>
      if coarseObserver.forget weighted.1 = .conditioned ∧
          firstOccurrenceEvent weighted.1 then
        weighted.2 + accumulated else accumulated) 0 = 8754
  rw [monthlyMeasureCompiler.weightedCrossings_eq_crossingTrace_map,
    crossingTrace_exact]
  simp

@[simp] theorem fine_fibreMass :
    fineMonthlyFold.fibreMass .conditioned = 11511 := by
  unfold SourceGeneratedObserverKernelFoldAt.fibreMass
    SourceGeneratedFiniteMeasureAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.generatedMeasure
    FiniteObserverMeasure.eventMass
  change monthlyMeasureCompiler.weightedCrossings.foldr
    (fun weighted accumulated =>
      if fineObserver.forget weighted.1 = .conditioned then
        weighted.2 + accumulated else accumulated) 0 = 11511
  rw [monthlyMeasureCompiler.weightedCrossings_eq_crossingTrace_map,
    crossingTrace_exact]
  simp
  norm_num

@[simp] theorem fine_eventMass :
    fineMonthlyFold.eventMass .conditioned = 8754 := by
  unfold SourceGeneratedObserverKernelFoldAt.eventMass
    SourceGeneratedFiniteMeasureAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.generatedMeasure
    FiniteObserverMeasure.eventMass
  change monthlyMeasureCompiler.weightedCrossings.foldr
    (fun weighted accumulated =>
      if fineObserver.forget weighted.1 = .conditioned ∧
          firstOccurrenceEvent weighted.1 then
        weighted.2 + accumulated else accumulated) 0 = 8754
  rw [monthlyMeasureCompiler.weightedCrossings_eq_crossingTrace_map,
    crossingTrace_exact]
  simp

theorem coarse_readVisible_exact :
    coarseMonthlyFold.readVisible .conditioned =
      some ((8754 : ℚ≥0) / 20581) := by
  rw [coarseMonthlyFold.readVisible_eq_some_ratio]
  · rw [coarse_eventMass, coarse_fibreMass]
  · rw [coarse_fibreMass]
    change (0 : ℚ) < 20581
    norm_num

theorem fine_readVisible_exact :
    fineMonthlyFold.readVisible .conditioned =
      some ((8754 : ℚ≥0) / 11511) := by
  rw [fineMonthlyFold.readVisible_eq_some_ratio]
  · rw [fine_eventMass, fine_fibreMass]
  · rw [fine_fibreMass]
    change (0 : ℚ) < 11511
    norm_num

theorem coarse_probability_below_half :
    (8754 : ℚ≥0) / 20581 < 1 / 2 := by
  change (8754 : ℚ) / 20581 < 1 / 2
  norm_num

theorem fine_probability_above_half :
    (1 : ℚ≥0) / 2 < 8754 / 11511 := by
  change (1 : ℚ) / 2 < 8754 / 11511
  norm_num

/-- Same source/measure/event/visible, opposite prediction sides solely from
kernel geometry. -/
theorem observer_kernel_geometry_flips_prediction :
    coarseMonthlyFold.readVisible .conditioned =
        some ((8754 : ℚ≥0) / 20581) ∧
      fineMonthlyFold.readVisible .conditioned =
        some ((8754 : ℚ≥0) / 11511) ∧
      (8754 : ℚ≥0) / 20581 < 1 / 2 ∧
      (1 : ℚ≥0) / 2 < 8754 / 11511 :=
  ⟨coarse_readVisible_exact, fine_readVisible_exact,
    coarse_probability_below_half, fine_probability_above_half⟩

/-- Both probability readouts remain visible computations and therefore
cannot recover exact position authority hidden in their kernel fibres. -/
theorem probability_factorization_not_authority_complete :
    (¬ Nonempty (AuthorityCompleteReadoutAt coarseObserver
      coarseMonthlyFold.probabilityReadout)) ∧
      (¬ Nonempty (AuthorityCompleteReadoutAt fineObserver
        fineMonthlyFold.probabilityReadout)) :=
  ⟨coarseMonthlyFold.noAuthorityCompleteProbability coarseKernelPair,
    fineMonthlyFold.noAuthorityCompleteProbability fineKernelPair⟩

@[simp] theorem uniform_coarse_fibreMass :
    coarseUniformFold.fibreMass .conditioned = 3 := by
  unfold SourceGeneratedObserverKernelFoldAt.fibreMass
    SourceGeneratedFiniteMeasureAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.generatedMeasure
    FiniteObserverMeasure.eventMass
  change uniformMeasureCompiler.weightedCrossings.foldr
    (fun weighted accumulated =>
      if coarseObserver.forget weighted.1 = .conditioned then
        weighted.2 + accumulated else accumulated) 0 = 3
  rw [uniformMeasureCompiler.weightedCrossings_eq_crossingTrace_map,
    crossingTrace_exact]
  simp
  apply Subtype.ext
  norm_num [NNRat.coe_add, NNRat.coe_natCast]

@[simp] theorem uniform_coarse_eventMass :
    coarseUniformFold.eventMass .conditioned = 1 := by
  unfold SourceGeneratedObserverKernelFoldAt.eventMass
    SourceGeneratedFiniteMeasureAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.generatedMeasure
    FiniteObserverMeasure.eventMass
  change uniformMeasureCompiler.weightedCrossings.foldr
    (fun weighted accumulated =>
      if coarseObserver.forget weighted.1 = .conditioned ∧
          firstOccurrenceEvent weighted.1 then
        weighted.2 + accumulated else accumulated) 0 = 1
  rw [uniformMeasureCompiler.weightedCrossings_eq_crossingTrace_map,
    crossingTrace_exact]
  simp

theorem uniform_coarse_readVisible_exact :
    coarseUniformFold.readVisible .conditioned =
      some ((1 : ℚ≥0) / 3) := by
  rw [coarseUniformFold.readVisible_eq_some_ratio]
  · rw [uniform_coarse_eventMass, uniform_coarse_fibreMass]
  · rw [uniform_coarse_fibreMass]
    change (0 : ℚ) < 3
    norm_num

/-- Observer and event fixed, changing only the source measure compiler changes
the normalized readout. -/
theorem measure_compiler_cannot_be_deleted :
    coarseMonthlyFold.readVisible .conditioned ≠
      coarseUniformFold.readVisible .conditioned := by
  rw [coarse_readVisible_exact, uniform_coarse_readVisible_exact]
  intro equality
  have valueEquality : (8754 : ℚ≥0) / 20581 = 1 / 3 :=
    Option.some.inj equality
  have rationalEquality :=
    congrArg (fun value : ℚ≥0 => (value : ℚ)) valueEquality
  change (8754 : ℚ) / 20581 = (1 : ℚ) / 3 at rationalEquality
  norm_num at rationalEquality

end
end M12ObserverGeometryRegression
end Society
end ProcessGame
end SaturationMonoid
