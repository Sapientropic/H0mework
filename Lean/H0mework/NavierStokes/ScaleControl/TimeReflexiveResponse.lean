import H0mework.Realization.Reflexive.Iteration
import H0mework.NavierStokes.InitialData.FinitePhysicalStateRestart
import H0mework.NavierStokes.Galerkin.CommonTimeExistence
import H0mework.NavierStokes.ShellSources.ReflexiveResidualTransport

/-!
# Source-generated scale-or-time reflexive responses

The integer-shell responder can stop when the current coefficient table has
no active outer nonlinear row.  That is a faithful zero for the instantaneous
outer-shell readout, but it is not a Navier--Stokes terminal: the actual
finite-dimensional flow may change the coefficients and expose a later
outer responsibility.

This module removes that false third outlet by a conservative versioned
extension.  At every current:

* a successful integer-shell response writes its existing native whole-shell
  successor and receipt;
* an empty outer-shell read generates an actual positive-time physical
  Galerkin segment, reifies its endpoint as the next raw source on the same
  owned mode set, and writes elapsed physical time.

Both branches are chosen internally by the source.  The resulting responder
is total, and its `ReflexiveQuery` read and write are projections of the same
dependent event.  Thus “no current outer shell” means “perform the generated
time update”, not “continuation exists” and not “the PDE residual vanished”.

This is a native producer.  It does not prove that repeated physical times
diverge, that infinitely many scale receipts violate a budget, or that a
time-advanced source must expose a new shell.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse

open Set
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCommonTimeExistence
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellReflexiveWrite

noncomputable section

/-! ## The physical time receipt generated at an outer-shell zero -/

/-- Canonical carrier radius of the actual current physical state. -/
def generatedTimeAdvanceInnerRadius
    (source : RawVorticityFourierSource) : NNReal :=
  ⟨Real.sqrt
      (finiteStateVorticityCoefficientEnstrophy
        (generatedSupport source)
        (generatedComplexVorticityState source
          (generatedSupport source))),
    Real.sqrt_nonneg _⟩

/--
One actual positive-time physical Galerkin segment generated from a raw
source on its own complete support.
-/
structure GeneratedTimeAdvanceReceipt
    (source : RawVorticityFourierSource)
    (ν : ℝ) : Type where
  trajectory : ℝ → ComplexVorticityHilbertState
  duration : ℝ
  duration_pos : 0 < duration
  fieldBound : NNReal
  fieldBound_eq :
    fieldBound =
      canonicalProjectedGeneratorFieldBound
        (generatedSupport source) ν
        (generatedTimeAdvanceInnerRadius source + 1)
  duration_eq :
    duration =
      1 / (4 * ((fieldBound : ℝ) + 1))
  initial :
    trajectory 0 =
      generatedComplexVorticityState source
        (generatedSupport source)
  physical :
    ∀ time ∈ Icc (0 : ℝ) duration,
      HasDerivAt trajectory
          (finiteStateVorticityGenerator
            (generatedSupport source) ν (trajectory time)) time ∧
        (∀ wave,
          wave ∉ generatedSupport source →
            trajectory time wave = 0) ∧
        (∀ wave,
          complexWavevector wave ⬝ᵥ trajectory time wave = 0) ∧
        FiniteStateFourierReality (trajectory time)
  generator_norm_le :
    ∀ time ∈ Icc (0 : ℝ) duration,
      ‖finiteStateVorticityGenerator
          (generatedSupport source) ν
          (trajectory time)‖ ≤
        fieldBound

/--
The quantified local Picard producer generates the time receipt, including
its exact source-owned lifespan and canonical generator-field bound.
-/
theorem generatedTimeAdvanceReceipt_nonempty
    (source : RawVorticityFourierSource)
    (ν : ℝ) :
    Nonempty (GeneratedTimeAdvanceReceipt source ν) := by
  let modes := generatedSupport source
  let initialState :=
    generatedComplexVorticityState source modes
  let innerRadius :=
    generatedTimeAdvanceInnerRadius source
  have zeroNotMem : (0 : IntegerWavevector) ∉ modes := by
    exact zero_not_mem_generatedSupport source
  have negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes := by
    intro wave waveMem
    exact generatedSupport_waveNeg_mem source waveMem
  have supported :
      ∀ wave, wave ∉ modes → initialState wave = 0 := by
    intro wave waveNotMem
    simp [initialState, waveNotMem]
  have transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ initialState wave = 0 := by
    intro wave waveMem
    simp only [initialState,
      generatedComplexVorticityState_apply, if_pos waveMem]
    exact generatedVorticityCoefficient_transverse source wave
  have reality :
      FiniteStateFourierReality initialState := by
    apply finiteStateFourierReality_of_reflection_fixed
      (fun {wave} waveMem =>
        generatedSupport_waveNeg_mem source waveMem)
      supported
    exact
      complexFourierRealityReflection_generatedSourceInitial source
  have initialMem :
      initialState ∈
        Metric.closedBall
          (0 : ComplexVorticityHilbertState) innerRadius := by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    exact
      complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
        modes initialState supported
  obtain
      ⟨fieldBound, fieldBoundEq,
        duration, durationPos, durationEq, uniformLocal⟩ :=
    exists_quantified_uniform_finitePhysicalTrajectory
      modes zeroNotMem negClosed ν innerRadius
  obtain
      ⟨trajectory, initial, physical⟩ :=
    uniformLocal initialState initialMem
      supported transverse reality
  exact
    ⟨{ trajectory := trajectory
       duration := duration
       duration_pos := durationPos
       fieldBound := fieldBound
       fieldBound_eq := by
         simpa [modes, innerRadius] using fieldBoundEq
       duration_eq := durationEq
       initial := initial
       physical := by
         intro time timeMem
         exact
           ⟨(physical time timeMem).1,
             (physical time timeMem).2.1,
             (physical time timeMem).2.2.1,
             (physical time timeMem).2.2.2.1⟩
       generator_norm_le := by
         intro time timeMem
         exact (physical time timeMem).2.2.2.2 }⟩

/-- Canonical source-selected local time receipt. -/
noncomputable def generatedTimeAdvanceReceipt
    (source : RawVorticityFourierSource)
    (ν : ℝ) :
    GeneratedTimeAdvanceReceipt source ν :=
  Classical.choice
    (generatedTimeAdvanceReceipt_nonempty source ν)

namespace GeneratedTimeAdvanceReceipt

/--
The source-generated Picard event carries an exact inverse field-bound time
quantum.
-/
theorem four_mul_duration_mul_fieldBound_add_one
    {source : RawVorticityFourierSource}
    {ν : ℝ}
    (receipt : GeneratedTimeAdvanceReceipt source ν) :
    4 * receipt.duration *
        ((receipt.fieldBound : ℝ) + 1) =
      1 := by
  rw [receipt.duration_eq]
  have denominatorNe :
      (4 : ℝ) *
          ((receipt.fieldBound : ℝ) + 1) ≠ 0 := by
    positivity
  field_simp

/--
The actual displacement on a generated time receipt is bounded by the same
source-owned field bound that fixes its duration.
-/
theorem trajectory_sub_initial_norm_le_fieldBound_mul
    {source : RawVorticityFourierSource}
    {ν : ℝ}
    (receipt : GeneratedTimeAdvanceReceipt source ν)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) receipt.duration) :
    ‖receipt.trajectory time - receipt.trajectory 0‖ ≤
      (receipt.fieldBound : ℝ) * time := by
  simpa only [sub_zero] using
    norm_image_sub_le_of_norm_deriv_le_segment'
      (a := (0 : ℝ))
      (b := receipt.duration)
      (f := receipt.trajectory)
      (f' := fun moment =>
        finiteStateVorticityGenerator
          (generatedSupport source) ν
          (receipt.trajectory moment))
      (fun moment momentMem =>
        ((receipt.physical moment momentMem).1).hasDerivWithinAt)
      (fun moment momentMem =>
        receipt.generator_norm_le moment
          (Ico_subset_Icc_self momentMem))
      time timeMem

/--
The generated physical trajectory stays in the same outer carrier ball
used to choose its canonical Picard field bound.

This is not an additional receipt field.  It is forced by the receipt's
actual differential law, its generated field bound, its exact inverse-bound
duration, and the source-owned initial radius.
-/
theorem trajectory_mem_generatedOuterBall
    {source : RawVorticityFourierSource}
    {ν : ℝ}
    (receipt : GeneratedTimeAdvanceReceipt source ν)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) receipt.duration) :
    receipt.trajectory time ∈
      Metric.closedBall
        (0 : ComplexVorticityHilbertState)
        (generatedTimeAdvanceInnerRadius source + 1) := by
  have initialSupported :
      ∀ wave,
        wave ∉ generatedSupport source →
          generatedComplexVorticityState source
              (generatedSupport source) wave =
            0 := by
    intro wave waveNotMem
    simp [waveNotMem]
  have initialNormLe :
      ‖receipt.trajectory 0‖ ≤
        generatedTimeAdvanceInnerRadius source := by
    rw [receipt.initial]
    apply Real.le_sqrt_of_sq_le
    exact
      complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
        (generatedSupport source)
        (generatedComplexVorticityState source
          (generatedSupport source))
        initialSupported
  have displacementLe :
      ‖receipt.trajectory time - receipt.trajectory 0‖ ≤
        (receipt.fieldBound : ℝ) * time := by
    exact
      receipt.trajectory_sub_initial_norm_le_fieldBound_mul
        time timeMem
  have fieldTimeLeOne :
      (receipt.fieldBound : ℝ) * time ≤ 1 := by
    have fieldNonneg : 0 ≤ (receipt.fieldBound : ℝ) :=
      NNReal.coe_nonneg _
    have fieldDurationLe :
        (receipt.fieldBound : ℝ) * time ≤
          (receipt.fieldBound : ℝ) * receipt.duration :=
      mul_le_mul_of_nonneg_left timeMem.2 fieldNonneg
    have exactTime :=
      receipt.four_mul_duration_mul_fieldBound_add_one
    have fieldDurationLtOne :
        (receipt.fieldBound : ℝ) * receipt.duration < 1 := by
      nlinarith
    exact fieldDurationLe.trans fieldDurationLtOne.le
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖receipt.trajectory time‖ ≤
        ‖receipt.trajectory time - receipt.trajectory 0‖ +
          ‖receipt.trajectory 0‖ := by
      simpa only [sub_add_cancel] using
        norm_add_le
          (receipt.trajectory time - receipt.trajectory 0)
          (receipt.trajectory 0)
    _ ≤
        (receipt.fieldBound : ℝ) * time +
          (generatedTimeAdvanceInnerRadius source : ℝ) :=
      add_le_add displacementLe initialNormLe
    _ ≤
        (generatedTimeAdvanceInnerRadius source : ℝ) + 1 := by
      linarith
    _ =
        ((generatedTimeAdvanceInnerRadius source + 1 : NNReal) : ℝ) := by
      simp

/-- Actual endpoint of the generated local physical segment. -/
def endpoint
    {source : RawVorticityFourierSource}
    {ν : ℝ}
    (receipt : GeneratedTimeAdvanceReceipt source ν) :
    ComplexVorticityHilbertState :=
  receipt.trajectory receipt.duration

/--
Reify the actual endpoint as the next raw source on the same exact mode set.
-/
def nextSource
    {source : RawVorticityFourierSource}
    {ν : ℝ}
    (receipt : GeneratedTimeAdvanceReceipt source ν) :
    RawVorticityFourierSource :=
  rawSourceOfFiniteVorticityState
    (generatedSupport source) receipt.endpoint

theorem endpoint_physical
    {source : RawVorticityFourierSource}
    {ν : ℝ}
    (receipt : GeneratedTimeAdvanceReceipt source ν) :
    HasDerivAt receipt.trajectory
        (finiteStateVorticityGenerator
          (generatedSupport source) ν receipt.endpoint)
        receipt.duration ∧
      (∀ wave,
        wave ∉ generatedSupport source →
          receipt.endpoint wave = 0) ∧
      (∀ wave,
        complexWavevector wave ⬝ᵥ receipt.endpoint wave = 0) ∧
      FiniteStateFourierReality receipt.endpoint := by
  exact
    receipt.physical receipt.duration
      ⟨receipt.duration_pos.le, le_rfl⟩

/-- Time advance preserves the exact owned support after recompilation. -/
theorem nextSource_generatedSupport
    {source : RawVorticityFourierSource}
    {ν : ℝ}
    (receipt : GeneratedTimeAdvanceReceipt source ν) :
    generatedSupport receipt.nextSource =
      generatedSupport source := by
  exact
    rawSourceOfFiniteVorticityState_generatedSupport
      (generatedSupport source)
      (zero_not_mem_generatedSupport source)
      (fun wave waveMem =>
        generatedSupport_waveNeg_mem source waveMem)
      receipt.endpoint

/--
The primitive raw-source compiler recovers the actual physical endpoint
exactly.
-/
theorem nextSource_generatedState
    {source : RawVorticityFourierSource}
    {ν : ℝ}
    (receipt : GeneratedTimeAdvanceReceipt source ν) :
    generatedComplexVorticityState receipt.nextSource
        (generatedSupport receipt.nextSource) =
      receipt.endpoint := by
  exact
    generatedComplexVorticityState_rawSourceOfFinitePhysicalState
      (generatedSupport source)
      (zero_not_mem_generatedSupport source)
      (fun wave waveMem =>
        generatedSupport_waveNeg_mem source waveMem)
      receipt.endpoint
      receipt.endpoint_physical.2.1
      (fun wave waveMem =>
        receipt.endpoint_physical.2.2.1 wave)
      receipt.endpoint_physical.2.2.2

/-- Exact whole-state receipt written by the positive physical-time event. -/
def stateTrace
    {source : RawVorticityFourierSource}
    {ν : ℝ}
    (receipt : GeneratedTimeAdvanceReceipt source ν) :
    ComplexVorticityHilbertState :=
  receipt.endpoint -
    generatedComplexVorticityState source
      (generatedSupport source)

/-- The time endpoint is the old physical state plus its exact receipt. -/
theorem endpoint_eq_initial_add_stateTrace
    {source : RawVorticityFourierSource}
    {ν : ℝ}
    (receipt : GeneratedTimeAdvanceReceipt source ν) :
    receipt.endpoint =
      generatedComplexVorticityState source
          (generatedSupport source) +
        receipt.stateTrace := by
  unfold stateTrace
  abel

end GeneratedTimeAdvanceReceipt

/-! ## Total scale-or-time native response -/

/-- Versioned source current retaining accumulated actual physical time. -/
structure ScaleTimeCurrent where
  source : RawVorticityFourierSource
  elapsed : ℝ

/-- Target of an existing successful whole-shell source response. -/
def shellTarget
    (current : ScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.source) :
    ScaleTimeCurrent where
  source := response.1
  elapsed := current.elapsed

/-- Target of the source-generated physical time update. -/
def timeTarget
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    ScaleTimeCurrent :=
  let receipt :=
    generatedTimeAdvanceReceipt current.source ν.coeff
  { source := receipt.nextSource
    elapsed := current.elapsed + receipt.duration }

/--
The native edge is determined by the literal outer-shell response.

The branch equalities are occurrence provenance generated inside
`generatedScaleTimeRespond`; callers never provide them to the producer.
-/
inductive NativeStep
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    ScaleTimeCurrent → Type
  | shell
      (response :
        Response GeneratedIntegerShellStep current.source)
      (generated :
        generatedIntegerShellRespond current.source =
          some response) :
      NativeStep ν current (shellTarget current response)
  | time
      (stopped :
        generatedIntegerShellRespond current.source = none) :
      NativeStep ν current (timeTarget ν current)

/-- Fixed observation carrier for the scale-or-time reflexive query. -/
inductive Observation
    (ν : Viscosity) : Type
  | shell
      (receipt : GeneratedIntegerShellReceipt)
  | time
      (source : RawVorticityFourierSource)
      (receipt :
        GeneratedTimeAdvanceReceipt source ν.coeff)

namespace NativeStep

/-- Read the exact receipt emitted by one native occurrence. -/
def observation
    {ν : Viscosity}
    {current next : ScaleTimeCurrent}
    (step : NativeStep ν current next) :
    Observation ν :=
  match step with
  | .shell response generated =>
      .shell
        (receiptOfResponse
          current.source response generated)
  | .time _ =>
      .time current.source
        (generatedTimeAdvanceReceipt
          current.source ν.coeff)

end NativeStep

/--
Total source response.  An outer-shell zero generates the physical time
edge instead of returning `none`.
-/
noncomputable def generatedScaleTimeRespond
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    Response (NativeStep ν) current :=
  match generated :
      generatedIntegerShellRespond current.source with
  | some response =>
      ⟨shellTarget current response,
        NativeStep.shell response generated⟩
  | none =>
      ⟨timeTarget ν current,
        NativeStep.time generated⟩

/--
The total response as a reflexive event.  Its observation and next state are
two projections of the same dependent response.
-/
noncomputable def scaleTimeReflexiveQuery
    (ν : Viscosity) :
    ReflexiveQuery ScaleTimeCurrent (Observation ν) where
  read := fun current =>
    (generatedScaleTimeRespond ν current).2.observation
  write := fun current =>
    (generatedScaleTimeRespond ν current).1

theorem generatedScaleTimeRespond_of_some
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.source)
    (generated :
      generatedIntegerShellRespond current.source =
        some response) :
  generatedScaleTimeRespond ν current =
      ⟨shellTarget current response,
        NativeStep.shell response generated⟩ := by
  unfold generatedScaleTimeRespond
  split
  · rename_i response' generated'
    have responseEq : response' = response :=
      Option.some.inj (generated'.symm.trans generated)
    subst response'
    have generatedEq : generated' = generated :=
      Subsingleton.elim _ _
    cases generatedEq
    rfl
  · rename_i stopped
    cases stopped.symm.trans generated

theorem generatedScaleTimeRespond_of_none
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (generated :
      generatedIntegerShellRespond current.source = none) :
  generatedScaleTimeRespond ν current =
      ⟨timeTarget ν current,
        NativeStep.time generated⟩ := by
  unfold generatedScaleTimeRespond
  split
  · rename_i _response generated'
    cases generated'.symm.trans generated
  · rename_i generated'
    have generatedEq : generated' = generated :=
      Subsingleton.elim _ _
    cases generatedEq
    rfl

theorem scaleTimeReflexiveQuery_run_of_some
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.source)
    (generated :
      generatedIntegerShellRespond current.source =
        some response) :
    ReflexiveQuery.run (scaleTimeReflexiveQuery ν) current =
      (.shell
          (receiptOfResponse current.source response generated),
        shellTarget current response) := by
  unfold ReflexiveQuery.run scaleTimeReflexiveQuery
  change
    ((generatedScaleTimeRespond ν current).2.observation,
      (generatedScaleTimeRespond ν current).1) =
      (.shell
          (receiptOfResponse current.source response generated),
        shellTarget current response)
  rw [generatedScaleTimeRespond_of_some
    ν current response generated]
  rfl

theorem scaleTimeReflexiveQuery_run_of_none
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (generated :
      generatedIntegerShellRespond current.source = none) :
    ReflexiveQuery.run (scaleTimeReflexiveQuery ν) current =
      (.time current.source
          (generatedTimeAdvanceReceipt
            current.source ν.coeff),
        timeTarget ν current) := by
  unfold ReflexiveQuery.run scaleTimeReflexiveQuery
  change
    ((generatedScaleTimeRespond ν current).2.observation,
      (generatedScaleTimeRespond ν current).1) =
      (.time current.source
          (generatedTimeAdvanceReceipt
            current.source ν.coeff),
        timeTarget ν current)
  rw [generatedScaleTimeRespond_of_none ν current generated]
  rfl

/-! ## Source-generated zero-or-scale / zero-to-time disposition -/

/--
Exact one-event consequences of the total producer.
-/
inductive GeneratedDisposition
    (ν : Viscosity)
    (current : ScaleTimeCurrent) : Type
  | shell
      (response :
        Response GeneratedIntegerShellStep current.source)
      (generated :
        generatedIntegerShellRespond current.source =
          some response)
      (run :
        ReflexiveQuery.run (scaleTimeReflexiveQuery ν) current =
          (.shell
              (receiptOfResponse
                current.source response generated),
            shellTarget current response))
      (traceNonzero :
        generatedIntegerShellReceiptTrace
            (receiptOfResponse
              current.source response generated) ≠ 0)
      (coefficientWriteBack :
        generatedCoefficientCarrier response.1 =
          generatedCoefficientCarrier current.source +
            generatedIntegerShellReceiptTrace
              (receiptOfResponse
                current.source response generated))
  | time
      (receipt :
        GeneratedTimeAdvanceReceipt current.source ν.coeff)
      (outerReadZero :
        reflexiveObservation current.source = 0)
      (run :
        ReflexiveQuery.run (scaleTimeReflexiveQuery ν) current =
          (.time current.source receipt,
            timeTarget ν current))
      (durationPos : 0 < receipt.duration)
      (nextState :
        generatedComplexVorticityState receipt.nextSource
            (generatedSupport receipt.nextSource) =
          receipt.endpoint)
      (stateWriteBack :
        receipt.endpoint =
          generatedComplexVorticityState current.source
              (generatedSupport current.source) +
            receipt.stateTrace)

/--
Generate the exact scale-or-time event without an input branch.

In particular, zero of the complete outer-shell readout produces a positive
physical-time native write; it is never interpreted as a continuation
certificate or a PDE terminal.
-/
noncomputable def generatedDisposition
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    GeneratedDisposition ν current := by
  cases generated :
      generatedIntegerShellRespond current.source with
  | some response =>
      let receipt :=
        receiptOfResponse current.source response generated
      exact .shell response generated
        (scaleTimeReflexiveQuery_run_of_some
          ν current response generated)
        (coefficientTrace_ne_zero receipt)
        (coefficientCarrier_next receipt)
  | none =>
      let receipt :=
        generatedTimeAdvanceReceipt current.source ν.coeff
      exact .time receipt
        (by
          exact
            (reflexiveObservation_eq_zero_iff current.source).2
              generated)
        (scaleTimeReflexiveQuery_run_of_none
          ν current generated)
        receipt.duration_pos
        receipt.nextSource_generatedState
        receipt.endpoint_eq_initial_add_stateTrace

/--
Canonical iteration of the total producer.  Every adjacent section is an
actual scale write or an actual positive physical-time write by
`generatedDisposition`.
-/
theorem repeatEval_canonical
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (length : ℕ) :
    StatefulGenAlg.repeatEval
        (reflexiveQueryPrimitive (scaleTimeReflexiveQuery ν))
        (reflexiveQueryStatefulPlan (scaleTimeReflexiveQuery ν))
        length initial
        (reflexiveQueryIteratedObservationTrace
          (scaleTimeReflexiveQuery ν) initial length)
        ((reflexiveQueryIteratedTimeField
          (scaleTimeReflexiveQuery ν) initial).stateAt length) :=
  reflexiveStatefulPlan_repeatEval_canonical
    (scaleTimeReflexiveQuery ν) initial length

end

end ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
end NavierStokes
end SaturationMonoid
