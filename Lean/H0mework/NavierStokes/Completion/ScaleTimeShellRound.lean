import H0mework.NavierStokes.Completion.OmittedPreTimeConsumeBeforeQuotient
import H0mework.NavierStokes.ScaleControl.TimeShellRound
import H0mework.NavierStokes.ScaleControl.TimeShellJumpLedger

/-!
# Complete-support macro target of one generated shell round

The existing `GeneratedFiniteRound` owns the exact old-q shell path.  Its
legacy macro target enters physical time directly at the radial terminal.
That is correct only when no interior nonlinear support is missing.

This module keeps the old shell producer unchanged and versions its
macroscopic target:

```text
old generated shell terminal
→ no missing support: the same terminal
→ missing support: the unique conservative complete-support write
→ actual positive-time unforced receipt.
```

The complete time current has the same whole physical state as the old shell
terminal, owns every generated nonlinear coordinate, and has no remaining
missing-support demand.  Its next authoritative response is therefore the
time event.  No shell microstep is interpreted as physical time, and no
caller supplies the support branch, target, receipt, or closure witness.
-/

namespace SaturationMonoid
namespace NavierStokes

open scoped Interval

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellRound
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedNativeSuccessor
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedScaleTimeResponse
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedPreTimeConsumeBeforeQuotient
open
  ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellJumpLedger

noncomputable section

namespace ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellRound.GeneratedFiniteRound

/-- Literal current at the old shell path terminal, before optional support. -/
def shellTerminalCurrent
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    ScaleTimeCurrent where
  source := round.shellRun.terminal
  elapsed := current.elapsed

/--
Source-owned current on which the actual physical-time event runs.  The
branch is computed from the terminal's complete missing-support set.
-/
noncomputable def completeTimeCurrent
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    ScaleTimeCurrent :=
  if _missingNonempty :
      (generatedMissingNonlinearModes
        round.shellRun.terminal).Nonempty
  then
    completeSupportTarget round.shellTerminalCurrent
  else
    round.shellTerminalCurrent

theorem completeTimeCurrent_of_missing
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current)
    (missingNonempty :
      (generatedMissingNonlinearModes
        round.shellRun.terminal).Nonempty) :
    round.completeTimeCurrent =
      completeSupportTarget round.shellTerminalCurrent := by
  simp [completeTimeCurrent, missingNonempty]

theorem completeTimeCurrent_of_closed
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current)
    (missingClosed :
      generatedMissingNonlinearModes
          round.shellRun.terminal =
        ∅) :
    round.completeTimeCurrent =
      round.shellTerminalCurrent := by
  have notNonempty :
      ¬(generatedMissingNonlinearModes
        round.shellRun.terminal).Nonempty := by
    rw [missingClosed]
    exact Finset.not_nonempty_empty
  simp [completeTimeCurrent, notNonempty]

@[simp] theorem completeTimeCurrent_elapsed
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    round.completeTimeCurrent.elapsed = current.elapsed := by
  by_cases missingNonempty :
      (generatedMissingNonlinearModes
        round.shellRun.terminal).Nonempty
  · rw [round.completeTimeCurrent_of_missing missingNonempty]
    rfl
  · have missingClosed :
        generatedMissingNonlinearModes
            round.shellRun.terminal =
          ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp missingNonempty
    rw [round.completeTimeCurrent_of_closed missingClosed]
    rfl

/--
The optional support write changes no physical Fourier coefficient on the
ambient carrier.
-/
theorem completeTimeCurrent_generatedState
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    generatedComplexVorticityState
        round.completeTimeCurrent.source
        (generatedSupport round.completeTimeCurrent.source) =
      generatedComplexVorticityState
        round.shellRun.terminal
        (generatedSupport round.shellRun.terminal) := by
  by_cases missingNonempty :
      (generatedMissingNonlinearModes
        round.shellRun.terminal).Nonempty
  · rw [round.completeTimeCurrent_of_missing missingNonempty]
    exact
      completeSupportTarget_generatedState
        round.shellTerminalCurrent
  · have missingClosed :
        generatedMissingNonlinearModes
            round.shellRun.terminal =
          ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp missingNonempty
    rw [round.completeTimeCurrent_of_closed missingClosed]
    rfl

/-- Every old terminal support coordinate is owned by the complete time current. -/
theorem shellTerminalSupport_subset_completeTimeSupport
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    generatedSupport round.shellRun.terminal ⊆
      generatedSupport round.completeTimeCurrent.source := by
  by_cases missingNonempty :
      (generatedMissingNonlinearModes
        round.shellRun.terminal).Nonempty
  · rw [round.completeTimeCurrent_of_missing missingNonempty,
      completeSupportTarget_source,
      completeOmittedPhysicalLiftSource_generatedSupport]
    exact
      generatedSupport_subset_completeNonlinearGalerkinModes
        round.shellRun.terminal
  · have missingClosed :
        generatedMissingNonlinearModes
            round.shellRun.terminal =
          ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp missingNonempty
    rw [round.completeTimeCurrent_of_closed missingClosed]
    exact Finset.Subset.rfl

@[simp] theorem completeTimeCurrent_missingClosed
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    generatedMissingNonlinearModes
        round.completeTimeCurrent.source =
      ∅ := by
  by_cases missingNonempty :
      (generatedMissingNonlinearModes
        round.shellRun.terminal).Nonempty
  · rw [round.completeTimeCurrent_of_missing missingNonempty]
    exact
      completeSupportTarget_missingNonlinearModes
        round.shellTerminalCurrent
  · have missingClosed :
        generatedMissingNonlinearModes
            round.shellRun.terminal =
          ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp missingNonempty
    rw [round.completeTimeCurrent_of_closed missingClosed]
    exact missingClosed

theorem completeTimeCurrent_outerStopped
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    generatedIntegerShellRespond
        round.completeTimeCurrent.source =
      none := by
  by_cases missingNonempty :
      (generatedMissingNonlinearModes
        round.shellRun.terminal).Nonempty
  · rw [round.completeTimeCurrent_of_missing missingNonempty,
      completeSupportTarget_source]
    exact
      generatedIntegerShellRespond_completeLift_eq_none_of_none
        round.shellRun.terminal round.shellRun.stopped
  · have missingClosed :
        generatedMissingNonlinearModes
            round.shellRun.terminal =
          ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp missingNonempty
    rw [round.completeTimeCurrent_of_closed missingClosed]
    exact round.shellRun.stopped

/-- Actual unforced receipt selected at the complete macro target. -/
def completeTimeReceipt
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    GeneratedTimeAdvanceReceipt
      round.completeTimeCurrent.source ν.coeff :=
  generatedTimeAdvanceReceipt
    round.completeTimeCurrent.source ν.coeff

/-- Actual current written by the complete shell/support/time macro. -/
def completeNext
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    ScaleTimeCurrent :=
  timeTarget ν round.completeTimeCurrent

/-- The authoritative next response at the complete target is physical time. -/
theorem completeTimeResponse
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    generatedCompleteScaleTimeRespond
        ν round.completeTimeCurrent =
      ⟨round.completeNext,
        ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedScaleTimeResponse.NativeStep.time
          round.completeTimeCurrent_outerStopped
          round.completeTimeCurrent_missingClosed⟩ := by
  exact
    generatedCompleteScaleTimeRespond_of_none_closed
      ν round.completeTimeCurrent
      round.completeTimeCurrent_outerStopped
      round.completeTimeCurrent_missingClosed

/-- The actual receipt starts at the old shell terminal's physical state. -/
theorem completeTimeReceipt_initial
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    round.completeTimeReceipt.trajectory 0 =
      generatedComplexVorticityState
        round.shellRun.terminal
        (generatedSupport round.shellRun.terminal) := by
  exact
    round.completeTimeReceipt.initial.trans
      round.completeTimeCurrent_generatedState

/--
The exact finite-support generator of the actual receipt has zero
whole-lattice PDE residual at its time-zero state.
-/
theorem completeTimeReceipt_wholeLatticePDEResidual_eq_zero
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    wholeLatticeVorticityFourierPDEResidualAt
        ν.coeff
        (generatedComplexVorticityState
          round.completeTimeCurrent.source
          (generatedSupport round.completeTimeCurrent.source))
        (finiteStateVorticityGenerator
          (generatedSupport round.completeTimeCurrent.source)
          ν.coeff
          (generatedComplexVorticityState
            round.completeTimeCurrent.source
            (generatedSupport round.completeTimeCurrent.source))) =
      0 :=
  generatedTimeAdvancePDEResidual_eq_zero_of_missingClosed
    round.completeTimeCurrent.source ν
    round.completeTimeCurrent_missingClosed

/-- The same actual receipt differentiates by the whole-lattice tangent. -/
theorem completeTimeReceipt_wholeLatticeDerivative
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current)
    (output : IntegerWavevector) :
    HasDerivAt
        (fun time =>
          round.completeTimeReceipt.trajectory time output)
        (wholeLatticeVorticityFourierTangentAt
          ν.coeff
          (generatedComplexVorticityState
            round.completeTimeCurrent.source
            (generatedSupport round.completeTimeCurrent.source))
          output)
        0 :=
  generatedTimeAdvanceReceipt_wholeLatticeDerivative_of_missingClosed
    round.completeTimeCurrent.source ν
    round.completeTimeCurrent_missingClosed output

/-! ## Actual integral macro write-back -/

/--
The versioned complete macro projection commutes with the actual unforced
Navier--Stokes segment.  Its initial physical state is the endpoint of the
old source-owned shell path, its positive-time derivative is the Galerkin
generator on the complete owned support, and its recompiled endpoint is the
next macro state.  The final equality is the same whole-state enstrophy
residual.
-/
theorem completeMacroPhysicalProjection_unforcedNS_commutes
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    round.completeTimeReceipt.trajectory 0 =
        generatedComplexVorticityState round.shellRun.terminal
          (generatedSupport round.shellRun.terminal) ∧
      (∀ time ∈
          Set.Icc (0 : ℝ) round.completeTimeReceipt.duration,
        HasDerivAt round.completeTimeReceipt.trajectory
          (finiteStateVorticityGenerator
            (generatedSupport round.completeTimeCurrent.source)
            ν.coeff
            (round.completeTimeReceipt.trajectory time))
          time) ∧
      generatedComplexVorticityState round.completeNext.source
          (generatedSupport round.completeNext.source) =
        round.completeTimeReceipt.trajectory
          round.completeTimeReceipt.duration ∧
      (∫ time in (0 : ℝ)..round.completeTimeReceipt.duration,
        (finiteStateVorticityStretchingWork
            (generatedSupport round.completeTimeCurrent.source)
            (round.completeTimeReceipt.trajectory time) -
          ν.coeff * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass
              (generatedSupport round.completeTimeCurrent.source)
              (round.completeTimeReceipt.trajectory time))) =
        (1 / 2 : ℝ) *
            wholeVorticityEuclideanMass
              (generatedComplexVorticityState
                round.completeNext.source
                (generatedSupport round.completeNext.source)) -
          (1 / 2 : ℝ) *
            wholeVorticityEuclideanMass
              (generatedComplexVorticityState
                round.shellRun.terminal
                (generatedSupport
                  round.shellRun.terminal)) := by
  refine
    ⟨round.completeTimeReceipt_initial,
      fun time timeMem =>
        (round.completeTimeReceipt.physical time timeMem).1,
      ?_,
      ?_⟩
  · simpa [
      completeNext, timeTarget, completeTimeReceipt,
      GeneratedTimeAdvanceReceipt.endpoint] using
        round.completeTimeReceipt.nextSource_generatedState
  · have timeBalance :=
      ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellJumpLedger.GeneratedTimeAdvanceReceipt.integral_stretching_sub_viscosity_eq_wholeMassChange
        round.completeTimeReceipt
    rw [round.completeTimeCurrent_generatedState] at timeBalance
    simpa [completeNext, timeTarget, completeTimeReceipt] using
      timeBalance

/--
The actual macro endpoint equals the original source state plus exactly two
same-carrier writes:

* the complete old-`q` shell trace; and
* the Bochner integral of the actual unforced generator on the complete
  physical support.

No shell microstep is literalized as physical time.
-/
theorem
    completeMacroPhysicalWriteBack_eq_shellTrace_add_unforcedIntegral
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    generatedComplexVorticityState round.completeNext.source
          (generatedSupport round.completeNext.source) -
        generatedComplexVorticityState current.source
          (generatedSupport current.source) =
      generatedIntegerShellPathStateTrace round.shellRun.arrival +
        ∫ time in (0 : ℝ)..round.completeTimeReceipt.duration,
          finiteStateVorticityGenerator
            (generatedSupport round.completeTimeCurrent.source)
            ν.coeff
            (round.completeTimeReceipt.trajectory time) := by
  let modes :=
    generatedSupport round.completeTimeCurrent.source
  let trajectory :=
    round.completeTimeReceipt.trajectory
  have generatorContinuousOn :
      ContinuousOn
        (fun time =>
          finiteStateVorticityGenerator
            modes ν.coeff (trajectory time))
        (Set.Icc (0 : ℝ)
          round.completeTimeReceipt.duration) := by
    intro time timeMem
    have trajectoryContinuous :
        ContinuousAt trajectory time :=
      ((round.completeTimeReceipt.physical
        time timeMem).1).continuousAt
    exact
      ((finiteStateVorticityGenerator_contDiff
          modes ν.coeff).continuous
        |>.continuousAt.comp
          trajectoryContinuous).continuousWithinAt
  have generatorIntegrable :
      IntervalIntegrable
        (fun time =>
          finiteStateVorticityGenerator
            modes ν.coeff (trajectory time))
        MeasureTheory.volume 0
          round.completeTimeReceipt.duration :=
    generatorContinuousOn.intervalIntegrable_of_Icc
      round.completeTimeReceipt.duration_pos.le
  have integralWrite :
      (∫ time in (0 : ℝ)..round.completeTimeReceipt.duration,
          finiteStateVorticityGenerator
            modes ν.coeff (trajectory time)) =
        trajectory round.completeTimeReceipt.duration -
          trajectory 0 := by
    refine
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := trajectory)
        (f' := fun time =>
          finiteStateVorticityGenerator
            modes ν.coeff (trajectory time))
        ?_ generatorIntegrable
    intro time timeMem
    apply
      (round.completeTimeReceipt.physical time ?_).1
    simpa [
      Set.uIcc_of_le
        round.completeTimeReceipt.duration_pos.le] using
      timeMem
  have macroProjection :=
    round.completeMacroPhysicalProjection_unforcedNS_commutes
  have timeWrite :
      (∫ time in (0 : ℝ)..round.completeTimeReceipt.duration,
          finiteStateVorticityGenerator
            (generatedSupport
              round.completeTimeCurrent.source)
            ν.coeff
            (round.completeTimeReceipt.trajectory time)) =
        generatedComplexVorticityState
              round.completeNext.source
              (generatedSupport round.completeNext.source) -
          generatedComplexVorticityState
              round.shellRun.terminal
              (generatedSupport
                round.shellRun.terminal) := by
    change
      (∫ time in (0 : ℝ)..round.completeTimeReceipt.duration,
          finiteStateVorticityGenerator
            modes ν.coeff (trajectory time)) =
        generatedComplexVorticityState
              round.completeNext.source
              (generatedSupport round.completeNext.source) -
          generatedComplexVorticityState
              round.shellRun.terminal
              (generatedSupport round.shellRun.terminal)
    rw [integralWrite]
    dsimp only [trajectory]
    rw [← macroProjection.2.2.1, macroProjection.1]
  have shellWrite :=
    generatedIntegerShellReachable_endpointState_sub_seed_eq_trace
      round.shellRun.arrival
  calc
    generatedComplexVorticityState round.completeNext.source
          (generatedSupport round.completeNext.source) -
        generatedComplexVorticityState current.source
          (generatedSupport current.source) =
      (generatedComplexVorticityState round.shellRun.terminal
            (generatedSupport round.shellRun.terminal) -
          generatedComplexVorticityState current.source
            (generatedSupport current.source)) +
        (generatedComplexVorticityState round.completeNext.source
            (generatedSupport round.completeNext.source) -
          generatedComplexVorticityState round.shellRun.terminal
            (generatedSupport round.shellRun.terminal)) := by
      abel
    _ =
      generatedIntegerShellPathStateTrace
          round.shellRun.arrival +
        ∫ time in (0 : ℝ)..
            round.completeTimeReceipt.duration,
          finiteStateVorticityGenerator
            (generatedSupport
              round.completeTimeCurrent.source)
            ν.coeff
            (round.completeTimeReceipt.trajectory time) := by
      rw [shellWrite, timeWrite]

/-- The generated Picard receipt retains its exact field-weighted time law. -/
theorem completeTimeReceipt_fieldWeightedQuantum
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    4 * round.completeTimeReceipt.duration *
        ((round.completeTimeReceipt.fieldBound : ℝ) + 1) =
      1 :=
  round.completeTimeReceipt.four_mul_duration_mul_fieldBound_add_one

end GeneratedFiniteRound
end ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellRound
end
end NavierStokes
end SaturationMonoid
