import H0mework.NavierStokes.ShellSources.WholeReceiptEnergyWriteBack
import H0mework.NavierStokes.ScaleControl.TimeRoundRuntime

/-!
# Exact zero-time shell-jump ledger

The scale-time runtime assigns physical duration only to its actual Picard
time receipts.  A preceding source-generated shell burst keeps elapsed time
fixed, but its native source write adds complete nonzero Fourier rows.

This module puts both facts on the same whole Hilbert carrier.  For every
finite generated shell path,

```text
endpoint state - seed state
  = embedded cumulative receipt trace,
```

and the whole Euclidean mass of this difference is exactly the sum of the
pairwise-orthogonal receipt masses.  Hence every positive-length shell burst
is a genuine state jump occurring at zero runtime physical occupancy.

This is the exact seam required before one may compare cumulative runtime
time with a single continuous Navier--Stokes path.  It does not silently
identify the grammar write with physical time evolution.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellJumpLedger

open scoped BigOperators

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCarrierCompletion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCarrierCompletion.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveLedger
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellRound
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeRoundRuntime

noncomputable section

/-! ## Exact whole-state compilation of an arbitrary shell path -/

/-- The finite flattened-carrier compiler preserves addition exactly. -/
@[simp] theorem coefficientCarrierComplexState_add
    (left right : IntegerShellCoefficientCarrier) :
    coefficientCarrierComplexState (left + right) =
      coefficientCarrierComplexState left +
        coefficientCarrierComplexState right := by
  apply lp.ext
  rw [lp.coeFn_add]
  funext wave coordinate
  simp only [
    coefficientCarrierComplexState_apply,
    Finsupp.add_apply,
    Pi.add_apply]

/-- Whole-state image of the exact cumulative trace written by a generated
finite shell path. -/
def generatedIntegerShellPathStateTrace
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    ComplexVorticityHilbertState :=
  coefficientCarrierComplexState
    (generatedIntegerShellCumulativeTrace arrival)

/--
The actual endpoint state is the seed state plus the whole-state image of
the complete source-generated trace.
-/
theorem generatedIntegerShellReachable_endpointState_eq_seed_add_trace
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    generatedComplexVorticityState current
          (generatedSupport current) =
      generatedComplexVorticityState seed
          (generatedSupport seed) +
        generatedIntegerShellPathStateTrace arrival := by
  rw [
    ← coefficientCarrierComplexState_generatedCoefficientCarrier,
    ← coefficientCarrierComplexState_generatedCoefficientCarrier,
    generatedCoefficientCarrier_eq_seed_add_cumulativeTrace,
    coefficientCarrierComplexState_add]
  rfl

/-- Difference form of the exact whole-state path write-back. -/
theorem generatedIntegerShellReachable_endpointState_sub_seed_eq_trace
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    generatedComplexVorticityState current
          (generatedSupport current) -
        generatedComplexVorticityState seed
          (generatedSupport seed) =
      generatedIntegerShellPathStateTrace arrival := by
  rw [
    generatedIntegerShellReachable_endpointState_eq_seed_add_trace
      arrival]
  abel

/--
Exact Pythagorean jump mass on the complete whole-state carrier.  The right
side retains every literal source receipt.
-/
theorem generatedIntegerShellPathStateTrace_euclideanMass
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    wholeVorticityEuclideanMass
        (generatedIntegerShellPathStateTrace arrival) =
      ((generatedIntegerShellReachableReceipts arrival).map
        (fun receipt =>
          coefficientCarrierNormSq
            (generatedIntegerShellReceiptTrace receipt))).sum := by
  rw [
    generatedIntegerShellPathStateTrace,
    wholeVorticityEuclideanMass_coefficientCarrierComplexState,
    generatedIntegerShellCumulativeTrace_normSq]

/-- Exact endpoint-jump mass for every generated finite shell path. -/
theorem generatedIntegerShellReachable_endpointJump_euclideanMass
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    wholeVorticityEuclideanMass
        (generatedComplexVorticityState current
            (generatedSupport current) -
          generatedComplexVorticityState seed
            (generatedSupport seed)) =
      ((generatedIntegerShellReachableReceipts arrival).map
        (fun receipt =>
          coefficientCarrierNormSq
            (generatedIntegerShellReceiptTrace receipt))).sum := by
  rw [
    generatedIntegerShellReachable_endpointState_sub_seed_eq_trace,
    generatedIntegerShellPathStateTrace_euclideanMass]

/-! ## Exact shell contribution to the target enstrophy balance -/

/-- The whole Euclidean mass of an actual finite source state is exactly its
flattened coefficient-carrier mass. -/
theorem generatedSourceState_euclideanMass_eq_coefficientCarrierNormSq
    (source : RawVorticityFourierSource) :
    wholeVorticityEuclideanMass
        (generatedComplexVorticityState source
          (generatedSupport source)) =
      coefficientCarrierNormSq
        (generatedCoefficientCarrier source) := by
  rw [
    ← coefficientCarrierComplexState_generatedCoefficientCarrier,
    wholeVorticityEuclideanMass_coefficientCarrierComplexState]

/--
An arbitrary generated shell path adds its complete orthogonal receipt mass
to the target whole-state enstrophy.  This is a state-energy identity, not
only a norm estimate for the isolated trace.
-/
theorem generatedIntegerShellReachable_endpointState_euclideanMass
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    wholeVorticityEuclideanMass
        (generatedComplexVorticityState current
          (generatedSupport current)) =
      wholeVorticityEuclideanMass
          (generatedComplexVorticityState seed
            (generatedSupport seed)) +
        ((generatedIntegerShellReachableReceipts arrival).map
          (fun receipt =>
            coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt))).sum := by
  induction arrival with
  | initial =>
      simp [generatedIntegerShellReachableReceipts]
  | @step prior arrival response generated inductionHypothesis =>
      let receipt : GeneratedIntegerShellReceipt :=
        ⟨prior, response, generated⟩
      calc
        wholeVorticityEuclideanMass
              (generatedComplexVorticityState response.1
                (generatedSupport response.1)) =
            coefficientCarrierNormSq
              (generatedCoefficientCarrier response.1) :=
          generatedSourceState_euclideanMass_eq_coefficientCarrierNormSq
            response.1
        _ =
            coefficientCarrierNormSq
                (generatedCoefficientCarrier prior) +
              coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) := by
          simpa [receipt] using
            receipt_generatedCoefficientCarrier_normSq_next receipt
        _ =
            wholeVorticityEuclideanMass
                (generatedComplexVorticityState prior
                  (generatedSupport prior)) +
              coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) := by
          rw [
            generatedSourceState_euclideanMass_eq_coefficientCarrierNormSq]
        _ =
            (wholeVorticityEuclideanMass
                (generatedComplexVorticityState seed
                  (generatedSupport seed)) +
              ((generatedIntegerShellReachableReceipts arrival).map
                (fun historicalReceipt =>
                  coefficientCarrierNormSq
                    (generatedIntegerShellReceiptTrace
                      historicalReceipt))).sum) +
              coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) := by
          rw [inductionHypothesis]
        _ = _ := by
          simp [
            generatedIntegerShellReachableReceipts_step,
            List.concat_eq_append,
            receipt]
          ring

/--
The actual Picard receipt pays the standard stretching-minus-viscosity
balance on the same whole-state mass used by the shell ledger.
-/
theorem
    GeneratedTimeAdvanceReceipt.integral_stretching_sub_viscosity_eq_wholeMassChange
    {source : RawVorticityFourierSource}
    {ν : ℝ}
    (receipt : GeneratedTimeAdvanceReceipt source ν) :
    (∫ time in (0 : ℝ)..receipt.duration,
      (finiteStateVorticityStretchingWork
          (generatedSupport source) (receipt.trajectory time) -
        ν * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass
            (generatedSupport source) (receipt.trajectory time))) =
      (1 / 2 : ℝ) *
          wholeVorticityEuclideanMass
            (generatedComplexVorticityState receipt.nextSource
              (generatedSupport receipt.nextSource)) -
        (1 / 2 : ℝ) *
          wholeVorticityEuclideanMass
            (generatedComplexVorticityState source
              (generatedSupport source)) := by
  have negClosed :
      ∀ wave, wave ∈ generatedSupport source →
        waveNeg wave ∈ generatedSupport source := by
    intro wave waveMem
    exact generatedSupport_waveNeg_mem source waveMem
  have balance :=
    finiteStateVorticityHalfEnstrophy_integral_stretchingWork
      (generatedSupport source) negClosed ν receipt.trajectory
      0 receipt.duration receipt.duration_pos.le
      (fun time timeMem => (receipt.physical time timeMem).1)
      (fun time timeMem => (receipt.physical time timeMem).2.2.2)
  rw [finiteStateVorticityHalfEnstrophy] at balance
  have endpointSupported :
      ∀ wave,
        wave ∉ generatedSupport source →
          receipt.endpoint wave = 0 :=
    receipt.endpoint_physical.2.1
  have initialSupported :
      ∀ wave,
        wave ∉ generatedSupport source →
          generatedComplexVorticityState source
              (generatedSupport source) wave =
            0 := by
    intro wave waveNotMem
    rw [generatedComplexVorticityState_apply, if_neg waveNotMem]
  rw [receipt.initial] at balance
  change
    (∫ time in (0 : ℝ)..receipt.duration,
      (finiteStateVorticityStretchingWork
          (generatedSupport source) (receipt.trajectory time) -
        ν * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass
            (generatedSupport source) (receipt.trajectory time))) =
      (1 / 2 : ℝ) *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport source) receipt.endpoint -
        (1 / 2 : ℝ) *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport source)
            (generatedComplexVorticityState source
              (generatedSupport source))
      at balance
  rw [
    ← wholeVorticityEuclideanMass_eq_finite_of_supported
      (generatedSupport source) receipt.endpoint endpointSupported,
    ← wholeVorticityEuclideanMass_eq_finite_of_supported
      (generatedSupport source)
      (generatedComplexVorticityState source
        (generatedSupport source))
      initialSupported,
    ← receipt.nextSource_generatedState] at balance
  exact balance

/-!
The next theorem is the macro compiler seam.  Its physical projection starts
only after the internally generated shell burst has reached its terminal
whole source.  The terminal source is compiled to the initial physical
state, the same receipt follows the unforced Galerkin generator for positive
physical time, and its actual endpoint is recompiled as the next source.

In particular, this does not interpret any literal shell write as a
classical physical-time step.
-/

/--
The complete finite-round macro projection commutes with the actual
unforced Navier--Stokes update and its whole-state enstrophy residual.
-/
theorem GeneratedFiniteRound.macroPhysicalProjection_unforcedNS_commutes
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    round.timeReceipt.trajectory 0 =
        generatedComplexVorticityState round.shellRun.terminal
          (generatedSupport round.shellRun.terminal) ∧
      (∀ time ∈ Set.Icc (0 : ℝ) round.timeReceipt.duration,
        HasDerivAt round.timeReceipt.trajectory
          (finiteStateVorticityGenerator
            (generatedSupport round.shellRun.terminal)
            ν.coeff
            (round.timeReceipt.trajectory time))
          time) ∧
      generatedComplexVorticityState round.next.source
          (generatedSupport round.next.source) =
        round.timeReceipt.trajectory round.timeReceipt.duration ∧
      (∫ time in (0 : ℝ)..round.timeReceipt.duration,
        (finiteStateVorticityStretchingWork
            (generatedSupport round.shellRun.terminal)
            (round.timeReceipt.trajectory time) -
          ν.coeff * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass
              (generatedSupport round.shellRun.terminal)
              (round.timeReceipt.trajectory time))) =
        (1 / 2 : ℝ) *
            wholeVorticityEuclideanMass
              (generatedComplexVorticityState round.next.source
                (generatedSupport round.next.source)) -
          (1 / 2 : ℝ) *
            wholeVorticityEuclideanMass
              (generatedComplexVorticityState round.shellRun.terminal
                (generatedSupport round.shellRun.terminal)) := by
  refine
    ⟨round.timeReceipt.initial,
      fun time timeMem =>
        (round.timeReceipt.physical time timeMem).1,
      ?_,
      ?_⟩
  · simpa [
      GeneratedFiniteRound.next,
      GeneratedTimeAdvanceReceipt.endpoint] using
        round.timeReceipt.nextSource_generatedState
  · simpa [GeneratedFiniteRound.next] using
      GeneratedTimeAdvanceReceipt.integral_stretching_sub_viscosity_eq_wholeMassChange
        round.timeReceipt

/--
The complete macro writes its old source to its next physical state by the
sum of exactly two same-carrier contributions:

* the cumulative old-`q` trace generated by the internal zero-time shell
  burst; and
* the Bochner integral of the actual unforced Galerkin generator during the
  following positive-time event.

Thus the shell microsteps remain internal source writes.  Only their complete
macro trace is composed with physical time evolution.
-/
theorem GeneratedFiniteRound.macroPhysicalWriteBack_eq_shellTrace_add_unforcedIntegral
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    generatedComplexVorticityState round.next.source
          (generatedSupport round.next.source) -
        generatedComplexVorticityState current.source
          (generatedSupport current.source) =
      generatedIntegerShellPathStateTrace round.shellRun.arrival +
        ∫ time in (0 : ℝ)..round.timeReceipt.duration,
          finiteStateVorticityGenerator
            (generatedSupport round.shellRun.terminal)
            ν.coeff
            (round.timeReceipt.trajectory time) := by
  let modes := generatedSupport round.shellRun.terminal
  let trajectory := round.timeReceipt.trajectory
  have generatorContinuousOn :
      ContinuousOn
        (fun time =>
          finiteStateVorticityGenerator
            modes ν.coeff (trajectory time))
        (Set.Icc (0 : ℝ) round.timeReceipt.duration) := by
    intro time timeMem
    have trajectoryContinuous :
        ContinuousAt trajectory time :=
      ((round.timeReceipt.physical time timeMem).1).continuousAt
    exact
      ((finiteStateVorticityGenerator_contDiff modes ν.coeff).continuous
        |>.continuousAt.comp trajectoryContinuous).continuousWithinAt
  have generatorIntegrable :
      IntervalIntegrable
        (fun time =>
          finiteStateVorticityGenerator
            modes ν.coeff (trajectory time))
        MeasureTheory.volume 0 round.timeReceipt.duration :=
    generatorContinuousOn.intervalIntegrable_of_Icc
      round.timeReceipt.duration_pos.le
  have integralWrite :
      (∫ time in (0 : ℝ)..round.timeReceipt.duration,
          finiteStateVorticityGenerator
            modes ν.coeff (trajectory time)) =
        trajectory round.timeReceipt.duration -
          trajectory 0 := by
    refine
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := trajectory)
        (f' := fun time =>
          finiteStateVorticityGenerator
            modes ν.coeff (trajectory time))
        ?_ generatorIntegrable
    intro time timeMem
    apply (round.timeReceipt.physical time ?_).1
    simpa [Set.uIcc_of_le round.timeReceipt.duration_pos.le] using
      timeMem
  have macroProjection :=
    GeneratedFiniteRound.macroPhysicalProjection_unforcedNS_commutes
      round
  have timeWrite :
      (∫ time in (0 : ℝ)..round.timeReceipt.duration,
          finiteStateVorticityGenerator
            (generatedSupport round.shellRun.terminal)
            ν.coeff
            (round.timeReceipt.trajectory time)) =
        generatedComplexVorticityState round.next.source
              (generatedSupport round.next.source) -
          generatedComplexVorticityState round.shellRun.terminal
              (generatedSupport round.shellRun.terminal) := by
    change
      (∫ time in (0 : ℝ)..round.timeReceipt.duration,
          finiteStateVorticityGenerator
            modes ν.coeff (trajectory time)) =
        generatedComplexVorticityState round.next.source
              (generatedSupport round.next.source) -
          generatedComplexVorticityState round.shellRun.terminal
              (generatedSupport round.shellRun.terminal)
    rw [integralWrite]
    dsimp only [trajectory]
    rw [← macroProjection.2.2.1, macroProjection.1]
  have shellWrite :=
    generatedIntegerShellReachable_endpointState_sub_seed_eq_trace
      round.shellRun.arrival
  calc
    generatedComplexVorticityState round.next.source
          (generatedSupport round.next.source) -
        generatedComplexVorticityState current.source
          (generatedSupport current.source) =
      (generatedComplexVorticityState round.shellRun.terminal
            (generatedSupport round.shellRun.terminal) -
          generatedComplexVorticityState current.source
            (generatedSupport current.source)) +
        (generatedComplexVorticityState round.next.source
            (generatedSupport round.next.source) -
          generatedComplexVorticityState round.shellRun.terminal
            (generatedSupport round.shellRun.terminal)) := by
      abel
    _ =
      generatedIntegerShellPathStateTrace round.shellRun.arrival +
        ∫ time in (0 : ℝ)..round.timeReceipt.duration,
          finiteStateVorticityGenerator
            (generatedSupport round.shellRun.terminal)
            ν.coeff
            (round.timeReceipt.trajectory time) := by
      rw [shellWrite, timeWrite]

/-!
The next theorem is the target-facing round balance.  The shell trace is an
explicit positive jump term; it is not hidden inside the physical integral.
-/

/--
One actual maximal shell/time round satisfies the exact whole-state balance

```text
stretching - viscous dissipation
  = half(next mass - current mass - shell jump mass).
```

Thus classical continuation may consume the round only after paying the
source-generated jump defect.
-/
theorem GeneratedFiniteRound.integral_stretching_sub_viscosity_eq_massChange_sub_shellJump
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    (∫ time in (0 : ℝ)..round.timeReceipt.duration,
      (finiteStateVorticityStretchingWork
          (generatedSupport round.shellRun.terminal)
          (round.timeReceipt.trajectory time) -
        ν.coeff * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass
            (generatedSupport round.shellRun.terminal)
            (round.timeReceipt.trajectory time))) =
      (1 / 2 : ℝ) *
          wholeVorticityEuclideanMass
            (generatedComplexVorticityState round.next.source
              (generatedSupport round.next.source)) -
        (1 / 2 : ℝ) *
          wholeVorticityEuclideanMass
            (generatedComplexVorticityState current.source
              (generatedSupport current.source)) -
        (1 / 2 : ℝ) *
          ((generatedIntegerShellReachableReceipts
              round.shellRun.arrival).map
            (fun receipt =>
              coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt))).sum := by
  have timeBalance :=
    ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellJumpLedger.GeneratedTimeAdvanceReceipt.integral_stretching_sub_viscosity_eq_wholeMassChange
      round.timeReceipt
  have shellMass :=
    generatedIntegerShellReachable_endpointState_euclideanMass
      round.shellRun.arrival
  change
    (∫ time in (0 : ℝ)..round.timeReceipt.duration,
      (finiteStateVorticityStretchingWork
          (generatedSupport round.shellRun.terminal)
          (round.timeReceipt.trajectory time) -
        ν.coeff * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass
            (generatedSupport round.shellRun.terminal)
            (round.timeReceipt.trajectory time))) =
      (1 / 2 : ℝ) *
          wholeVorticityEuclideanMass
            (generatedComplexVorticityState
              round.timeReceipt.nextSource
              (generatedSupport round.timeReceipt.nextSource)) -
        (1 / 2 : ℝ) *
          wholeVorticityEuclideanMass
            (generatedComplexVorticityState current.source
              (generatedSupport current.source)) -
        (1 / 2 : ℝ) *
          ((generatedIntegerShellReachableReceipts
              round.shellRun.arrival).map
            (fun receipt =>
              coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt))).sum
  rw [timeBalance, shellMass]
  ring

/-! ## Exact accumulation along an arbitrary finite round prefix -/

namespace GeneratedInfiniteRoundLineage

/-- Total source-written shell jump mass in the first actual rounds. -/
def shellJumpMass
    {ν : Viscosity}
    (lineage : GeneratedInfiniteRoundLineage ν)
    (length : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    ((generatedIntegerShellReachableReceipts
        (lineage.round index).shellRun.arrival).map
      (fun receipt =>
        coefficientCarrierNormSq
          (generatedIntegerShellReceiptTrace receipt))).sum

/-- Exact stretching-minus-viscosity work of the actual Picard segments in
the first source-generated rounds. -/
def stretchingSubViscosityWork
    {ν : Viscosity}
    (lineage : GeneratedInfiniteRoundLineage ν)
    (length : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    ∫ time in (0 : ℝ)..(lineage.timeReceipt index).duration,
      (finiteStateVorticityStretchingWork
          (generatedSupport
            (lineage.round index).shellRun.terminal)
          ((lineage.timeReceipt index).trajectory time) -
        ν.coeff * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass
            (generatedSupport
              (lineage.round index).shellRun.terminal)
            ((lineage.timeReceipt index).trajectory time))

/--
Exact whole-state balance for every finite prefix of an actual infinite
scale-time lineage:

```text
Σ physical segment work
  = half(final mass - initial mass - Σ shell jump mass).
```

The formula telescopes the actual round endpoints while retaining every
zero-time source write as an explicit positive defect term.
-/
theorem prefix_stretchingSubViscosityWork_eq_massChange_sub_shellJump
    {ν : Viscosity}
    (lineage : GeneratedInfiniteRoundLineage ν) :
    ∀ length : ℕ,
      stretchingSubViscosityWork lineage length =
        (1 / 2 : ℝ) *
            wholeVorticityEuclideanMass
              (generatedComplexVorticityState
                (lineage.current length).source
                (generatedSupport
                  (lineage.current length).source)) -
          (1 / 2 : ℝ) *
            wholeVorticityEuclideanMass
              (generatedComplexVorticityState
                (lineage.current 0).source
                (generatedSupport
                  (lineage.current 0).source)) -
          (1 / 2 : ℝ) * shellJumpMass lineage length
  | 0 => by
      simp [stretchingSubViscosityWork, shellJumpMass]
  | length + 1 => by
      have prefixBalance :=
        prefix_stretchingSubViscosityWork_eq_massChange_sub_shellJump
          lineage length
      have roundBalance :=
        ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellJumpLedger.GeneratedFiniteRound.integral_stretching_sub_viscosity_eq_massChange_sub_shellJump
          (lineage.round length)
      rw [stretchingSubViscosityWork, shellJumpMass] at prefixBalance
      rw [
        stretchingSubViscosityWork,
        shellJumpMass,
        Finset.sum_range_succ,
        Finset.sum_range_succ,
        prefixBalance,
        lineage.current_succ_eq_round_next length,
        ThreeDimensionalVorticityCoefficientGeneratedScaleTimeRoundRuntime.GeneratedInfiniteRoundLineage.timeReceipt,
        roundBalance]
      ring

end GeneratedInfiniteRoundLineage

/-! ## Positive paths cannot be silent at fixed physical time -/

/-- A positive-length generated shell path has strictly positive whole-state
jump mass.  Positivity comes from the final actual source receipt, not from a
caller-supplied amplitude lower bound. -/
theorem generatedIntegerShellReachable_endpointJump_euclideanMass_pos
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (occurrencePos : 0 < arrival.occurrence) :
    0 <
      wholeVorticityEuclideanMass
        (generatedComplexVorticityState current
            (generatedSupport current) -
          generatedComplexVorticityState seed
            (generatedSupport seed)) := by
  rw [
    generatedIntegerShellReachable_endpointJump_euclideanMass
      arrival]
  cases arrival with
  | initial =>
      simp [NativeReachable.occurrence] at occurrencePos
  | @step prior arrival response generated =>
      let receipt : GeneratedIntegerShellReceipt :=
        ⟨prior, response, generated⟩
      rw [
        generatedIntegerShellReachableReceipts_step,
        List.concat_eq_append,
        List.map_append,
        List.map_singleton,
        List.sum_append,
        List.sum_singleton]
      exact
        add_pos_of_nonneg_of_pos
          (List.sum_nonneg fun mass massMem => by
            rcases List.mem_map.mp massMem with
              ⟨historicalReceipt, _, rfl⟩
            exact
              coefficientCarrierNormSq_nonneg
                (generatedIntegerShellReceiptTrace
                  historicalReceipt))
          (generatedIntegerShellReceiptTrace_normSq_pos receipt)

/-- A positive-length generated shell path changes the actual compiled whole
state. -/
theorem generatedIntegerShellReachable_endpointState_ne_seed
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (occurrencePos : 0 < arrival.occurrence) :
    generatedComplexVorticityState current
          (generatedSupport current) ≠
      generatedComplexVorticityState seed
        (generatedSupport seed) := by
  intro endpointEq
  have jumpMassPos :=
    generatedIntegerShellReachable_endpointJump_euclideanMass_pos
      arrival occurrencePos
  rw [endpointEq, sub_self] at jumpMassPos
  simp [
    wholeVorticityEuclideanMass,
    vorticityRowAmplitude,
    complexCoordinateAmplitudeSq] at jumpMassPos

/-! ## The actual scale-time round seam -/

/--
For every actual finite round, the shell burst has zero physical occupancy
and its endpoint jump mass is exactly the sum of its source-owned receipt
masses.  The final alternative is generated from the actual shell length:
either no shell write occurred, or the zero-time jump is strictly positive.
-/
theorem
    GeneratedFiniteRound.zeroTimeShellBurst_exactJumpDisposition
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    physicalTimeOccupancy ν current round.shellLength = 0 ∧
      wholeVorticityEuclideanMass
          (generatedComplexVorticityState round.shellRun.terminal
              (generatedSupport round.shellRun.terminal) -
            generatedComplexVorticityState current.source
              (generatedSupport current.source)) =
        ((generatedIntegerShellReachableReceipts
            round.shellRun.arrival).map
          (fun receipt =>
            coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt))).sum ∧
      (round.shellLength = 0 ∨
        0 <
          wholeVorticityEuclideanMass
            (generatedComplexVorticityState round.shellRun.terminal
                (generatedSupport round.shellRun.terminal) -
              generatedComplexVorticityState current.source
                (generatedSupport current.source))) := by
  refine
    ⟨round.physicalTimeOccupancy_shellLength,
      generatedIntegerShellReachable_endpointJump_euclideanMass
        round.shellRun.arrival,
      ?_⟩
  exact
    (Nat.eq_zero_or_pos round.shellLength).imp_right
      (fun shellLengthPos =>
        generatedIntegerShellReachable_endpointJump_euclideanMass_pos
          round.shellRun.arrival shellLengthPos)

end

end
    ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellJumpLedger
end NavierStokes
end SaturationMonoid
