import H0mework.NavierStokes.Crossing.FiniteComponentSources

/-!
# Complete source/gluing ledger of an actual whole crossing

At an actual half-critical crossing, the internally generated finite core is
now an exact sum of primitive finite half-critical source occurrences.  Two
and only two nonlinear responsibilities remain before quotienting:

* ordered cross rows among the finite component occurrences;
* the exact interaction of the finite core with the retained whole tail.

This module combines those already generated identities into one complete
whole-output ledger.  No component is evolved as an independent PDE
solution, and no finite endpoint is substituted for the actual whole update.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingWholeSourceGluingLedger

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteComponentSources

noncomputable section

/-- Sum of the nonlinear self rows of every primitive finite component
occurrence, after exact recompilation. -/
def wholeRestartCrossingFiniteComponentSelfRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  ((wholeRestartCrossingFiniteComponentSources initial index crossed).map
      fun source =>
        wholeStateVorticityNonlinearCoefficientAt
          (generatedComplexVorticityState source (generatedSupport source))
          output).sum

/-- Ordered cross rows internal to the generated finite-core component
occurrences. -/
def wholeRestartCrossingFiniteComponentCrossResidual
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  wholeComponentCrossGluingResidual
    (wholeRestartCrossingFiniteComponents initial index crossed) output

/-- Exact nonlinear interaction between the finite core and the retained
whole tail. -/
def wholeRestartCrossingFiniteTailGluingResidual
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  wholeStateVorticityBilinearCoefficientAt
      (wholeRestartCrossingFiniteTail initial index crossed)
      (run initial index).contact.physicalState output +
    wholeStateVorticityBilinearCoefficientAt
      (wholeRestartCrossingFiniteCoreState initial index crossed)
      (wholeRestartCrossingFiniteTail initial index crossed) output

/-- Complete unclosed nonlinear row after all primitive finite component
self rows have been materialized. -/
def wholeRestartCrossingCompleteSourceGluingResidual
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  wholeRestartCrossingFiniteComponentCrossResidual
      initial index crossed output +
    wholeRestartCrossingFiniteTailGluingResidual
      initial index crossed output

/-- Recompiled primitive component self rows are exactly the self rows of the
ordered component-state list. -/
theorem wholeRestartCrossingFiniteComponentSelfRow_eq_componentStates
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    wholeRestartCrossingFiniteComponentSelfRow
        initial index crossed output =
      ((wholeRestartCrossingFiniteComponents initial index crossed).map
        fun component =>
          wholeStateVorticityNonlinearCoefficientAt component output).sum := by
  simp [wholeRestartCrossingFiniteComponentSelfRow,
    wholeRestartCrossingFiniteComponentSources,
    wholeRestartCrossingFiniteComponents,
    canonicalHalfCriticalComponents,
    generatedComplexVorticityState_crossingFiniteComponentSource]

/-- The finite core nonlinearity is exactly its primitive self rows plus the
ordered component cross residual. -/
theorem wholeRestartCrossingFiniteCoreNonlinear_eq_self_add_cross
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    wholeStateVorticityNonlinearCoefficientAt
        (wholeRestartCrossingFiniteCoreState initial index crossed) output =
      wholeRestartCrossingFiniteComponentSelfRow
          initial index crossed output +
        wholeRestartCrossingFiniteComponentCrossResidual
          initial index crossed output := by
  have componentLedger :=
    canonicalHalfCriticalComponents_wholeNonlinear_self_cross
      ν (wholeRestartCrossingFiniteCoreState initial index crossed)
      (wholeStateTransverse_sharpSupportProjection
        (wholeRestartCrossingFiniteCoreModes initial index crossed)
        (run initial index).contact.physicalState
        (run initial index).contact.transverse)
      output
  rw [wholeRestartCrossingFiniteComponentSelfRow_eq_componentStates]
  simpa [wholeRestartCrossingFiniteComponents,
    wholeRestartCrossingFiniteComponentCrossResidual] using componentLedger

/-- Complete same-output ledger: the actual whole nonlinear row is the sum
of primitive finite half-critical self rows and the two generated gluing
responsibilities, with no hidden remainder. -/
theorem wholeRestartCrossingWholeNonlinear_eq_sourceSelf_add_gluing
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    wholeStateVorticityNonlinearCoefficientAt
        (run initial index).contact.physicalState output =
      wholeRestartCrossingFiniteComponentSelfRow
          initial index crossed output +
        wholeRestartCrossingCompleteSourceGluingResidual
          initial index crossed output := by
  have tailLedger :=
    wholeRestartCrossingNonlinearCoefficient_sub_core
      initial index crossed output
  have coreLedger :=
    wholeRestartCrossingFiniteCoreNonlinear_eq_self_add_cross
      initial index crossed output
  unfold wholeRestartCrossingCompleteSourceGluingResidual
    wholeRestartCrossingFiniteTailGluingResidual at ⊢
  rw [coreLedger] at tailLedger
  have wholeEq := (sub_eq_iff_eq_add).mp tailLedger
  rw [wholeEq]
  abel

/-- The complete crossing gluing row vanishes exactly when the primitive
finite component self rows already reconstruct the actual whole nonlinear
row.  This is faithful zero on the same coefficient carrier. -/
theorem wholeRestartCrossingCompleteSourceGluingResidual_eq_zero_iff
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    (fun output =>
        wholeRestartCrossingCompleteSourceGluingResidual
          initial index crossed output) = 0 ↔
      (fun output =>
        wholeStateVorticityNonlinearCoefficientAt
          (run initial index).contact.physicalState output) =
        fun output =>
          wholeRestartCrossingFiniteComponentSelfRow
            initial index crossed output := by
  constructor
  · intro residualZero
    funext output
    have ledger :=
      wholeRestartCrossingWholeNonlinear_eq_sourceSelf_add_gluing
        initial index crossed output
    have coordinateZero := congrFun residualZero output
    simpa only [Pi.zero_apply, add_zero, coordinateZero] using ledger
  · intro selfEq
    funext output
    change
      wholeRestartCrossingCompleteSourceGluingResidual
          initial index crossed output =
        (0 : ComplexCoordinateVector)
    have ledger :=
      wholeRestartCrossingWholeNonlinear_eq_sourceSelf_add_gluing
        initial index crossed output
    have coordinateEq := congrFun selfEq output
    rw [coordinateEq] at ledger
    have balanced :
        wholeRestartCrossingFiniteComponentSelfRow
              initial index crossed output +
            wholeRestartCrossingCompleteSourceGluingResidual
              initial index crossed output =
          wholeRestartCrossingFiniteComponentSelfRow
              initial index crossed output + 0 := by
      simpa using ledger.symm
    exact add_left_cancel balanced

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingWholeSourceGluingLedger
end NavierStokes
end SaturationMonoid
