/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M12.Kernel.ObserverGeometryRegression

/-!
# M12 zero-mass and empty-event boundaries

Empty geometric fibres and visibly nonempty all-zero fibres both yield
undefined normalization, but remain structurally distinct.  A positive fibre
with an empty event instead yields the defined value `some 0`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M12ZeroMassBoundaryRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity Space Observer
open Probability Measure Kernel
open M11GeneratedSocialSpaceCrossingFixture
open M12GeneratedFlowObserverFixture
open M12GeneratedFlowMeasureFixture
open M12ObserverGeometryRegression

def coarseZeroFold : SourceGeneratedObserverKernelFoldAt
    zeroMeasure coarseObserver firstOccurrenceEvent :=
  SourceGeneratedObserverKernelFoldAt.generate
    zeroMeasure coarseObserver firstOccurrenceEvent

@[simp] theorem coarseZero_conditioned_fibre :
    coarseZeroFold.fibre .conditioned =
      [firstCrossing, middleCrossing, recurrentCrossing] := by
  rfl

@[simp] theorem coarseZero_outside_fibre :
    coarseZeroFold.fibre .outside = [] := by
  rfl

theorem coarseZero_all_coefficients_zero
    (crossing : crossingCompiler.ExactCrossing)
    (_membership : crossing ∈ coarseZeroFold.fibre .conditioned) :
    zeroMeasure.coefficient crossing = 0 := by
  rfl

/-- Nonempty geometric fibre with all coefficients zero remains present but
has no normalized probability. -/
theorem nonempty_allZero_fibre_is_none :
    coarseZeroFold.readVisible .conditioned = none ∧
      coarseZeroFold.fibre .conditioned ≠ [] :=
  coarseZeroFold.nonempty_allZero_fibre_readVisible_none
    (by simp) coarseZero_all_coefficients_zero

/-- Empty geometric fibre also has no normalized probability. -/
theorem empty_fibre_is_none :
    coarseZeroFold.readVisible .outside = none :=
  coarseZeroFold.empty_fibre_readVisible_none coarseZero_outside_fibre

/-- Empty and all-zero are observationally equal at `Option`, but the exact
fibre carrier keeps them distinct. -/
theorem none_boundary_preserves_geometric_distinction :
    coarseZeroFold.readVisible .conditioned =
        coarseZeroFold.readVisible .outside ∧
      coarseZeroFold.fibre .conditioned ≠ [] ∧
      coarseZeroFold.fibre .outside = [] :=
  ⟨nonempty_allZero_fibre_is_none.1.trans empty_fibre_is_none.symm,
    nonempty_allZero_fibre_is_none.2, coarseZero_outside_fibre⟩

/-- Same positive monthly measure, but an event predicate which is nowhere
true. -/
def emptyEventMonthlyFold : SourceGeneratedObserverKernelFoldAt
    monthlyMeasure coarseObserver (fun _crossing => False) :=
  SourceGeneratedObserverKernelFoldAt.generate
    monthlyMeasure coarseObserver (fun _crossing => False)

@[simp] theorem emptyEvent_conditioned_fibre :
    emptyEventMonthlyFold.fibre .conditioned =
      [firstCrossing, middleCrossing, recurrentCrossing] := by
  rfl

@[simp] theorem emptyEvent_eventFibre :
    emptyEventMonthlyFold.eventFibre .conditioned = [] := by
  rfl

theorem emptyEvent_fibreMass_positive :
    0 < emptyEventMonthlyFold.fibreMass .conditioned := by
  have sameMass : emptyEventMonthlyFold.fibreMass .conditioned =
      coarseMonthlyFold.fibreMass .conditioned :=
    rfl
  rw [sameMass, coarse_fibreMass]
  change (0 : ℚ) < (20581 : ℚ)
  norm_num

/-- Positive conditioning mass and empty event produce a defined zero, not
the undefined `none` used at zero mass. -/
theorem positive_fibre_empty_event_is_some_zero :
    emptyEventMonthlyFold.readVisible .conditioned = some 0 :=
  emptyEventMonthlyFold.positive_fibre_empty_event_readVisible_some_zero
    emptyEvent_fibreMass_positive emptyEvent_eventFibre

theorem defined_zero_is_not_undefined :
    emptyEventMonthlyFold.readVisible .conditioned ≠ none := by
  rw [positive_fibre_empty_event_is_some_zero]
  decide

end
end M12ZeroMassBoundaryRegression
end Society
end ProcessGame
end SaturationMonoid
