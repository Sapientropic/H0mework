import H0mework.NavierStokes.ScaleControl.TimeReflexiveResponse
import H0mework.NavierStokes.InitialData.FinitePhysicalStateSupportLift

/-!
# PDE target validation for generated shell observations

The integer-shell grammar remains the authoritative source producer and
continues to write its generated nonlinear row into the next coefficient
table.  A literal shell microstep is not thereby identified with one
classical physical-time step.

This module supplies a target-side validation of the already generated row.
It enlarges the finite Galerkin inventory, zero-extends the old physical
state, and generates an actual positive-time unforced Galerkin receipt.
Every selected shell row is recovered as the time-zero derivative of that
receipt:

```text
actual unforced time receipt
  -> selected-row derivative observation
  -> legacy whole-shell receipt readout.
```

This validates a genuine PDE tangent readout of the old `q`; it does not
replace the old source update or become the authoritative scale scheduler.
The auxiliary shell ledger below is therefore target memory only.  Its next
physical source is the endpoint of the validation receipt.

Promoting this local target semantics back into the source primitive would
be target-semantics capture.  Reading the old grammar's internal shell
microsteps as literal classical time steps would be microstep literalization.
Neither interpretation is used here.

If the shell read is empty, the validation process still emits an actual
positive-time receipt on the current support and records no shell trace.
This remains a target validation, not a replacement source terminal law.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedUnforcedScaleTimeReceipt

open Set
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateSupportLift
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellReflexiveWrite
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse

noncomputable section

/-! ## Zero-filled source-owned support expansion -/

/--
Recompile the current physical state on the support selected by one literal
shell response.  Newly exposed shell rows are zero at time zero.
-/
def shellPhysicalLiftSource
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current) :
    RawVorticityFourierSource :=
  rawSourceOfFiniteVorticityState
    (generatedIntegerShellGalerkinModes current response)
    (generatedComplexVorticityState current
      (generatedSupport current))

theorem generatedIntegerShellGalerkinModes_waveNeg_mem
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current)
    {wave : IntegerWavevector}
    (waveMem :
      wave ∈ generatedIntegerShellGalerkinModes current response) :
    waveNeg wave ∈
      generatedIntegerShellGalerkinModes current response := by
  rw [generatedIntegerShellGalerkinModes, Finset.mem_union] at waveMem ⊢
  rcases waveMem with currentMem | shellMem
  · exact Or.inl (generatedSupport_waveNeg_mem current currentMem)
  · exact Or.inr
      ((mem_generatedOuterNonlinearShellModes_waveNeg_iff
        current response.2.shellSq wave).mpr shellMem)

theorem shellPhysicalLiftSource_generatedSupport
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current) :
    generatedSupport (shellPhysicalLiftSource current response) =
      generatedIntegerShellGalerkinModes current response := by
  exact
    rawSourceOfFiniteVorticityState_generatedSupport
      (generatedIntegerShellGalerkinModes current response)
      (zero_not_mem_generatedIntegerShellGalerkinModes current response)
      (fun wave waveMem =>
        generatedIntegerShellGalerkinModes_waveNeg_mem
          current response waveMem)
      (generatedComplexVorticityState current
        (generatedSupport current))

/--
The enlarged-support initial table is exactly the pre-event physical state
on the whole Hilbert carrier.
-/
theorem generatedIntegerShellGalerkinInitialState_eq_currentPhysicalState
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current) :
    generatedIntegerShellGalerkinInitialState current response =
      generatedComplexVorticityState current
        (generatedSupport current) := by
  exact
    generatedComplexVorticityState_eq_generatedSupport_of_subset
      current
      (generatedIntegerShellGalerkinModes current response)
      (generatedSupport_subset_generatedIntegerShellGalerkinModes
        current response)

/--
Support expansion is physically conservative: recompilation returns exactly
the old coefficient state, zero-filled on the newly exposed rows.
-/
theorem shellPhysicalLiftSource_generatedState
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current) :
    generatedComplexVorticityState
        (shellPhysicalLiftSource current response)
        (generatedSupport (shellPhysicalLiftSource current response)) =
      generatedIntegerShellGalerkinInitialState current response := by
  calc
    generatedComplexVorticityState
        (shellPhysicalLiftSource current response)
        (generatedSupport (shellPhysicalLiftSource current response)) =
      generatedComplexVorticityState current
        (generatedSupport current) := by
      exact
        rawSourceOfGeneratedPhysicalState_supportLift_generatedState
          current
          (generatedIntegerShellGalerkinModes current response)
          (generatedSupport_subset_generatedIntegerShellGalerkinModes
            current response)
          (zero_not_mem_generatedIntegerShellGalerkinModes
            current response)
          (fun wave waveMem =>
            generatedIntegerShellGalerkinModes_waveNeg_mem
              current response waveMem)
    _ = generatedIntegerShellGalerkinInitialState current response :=
      (generatedIntegerShellGalerkinInitialState_eq_currentPhysicalState
        current response).symm

/-! ## The target-side actual time receipt -/

/--
Canonical unforced physical receipt on the source-selected enlarged support.
-/
def shellPhysicalTimeReceipt
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current)
    (ν : Viscosity) :
    GeneratedTimeAdvanceReceipt
      (shellPhysicalLiftSource current response) ν.coeff :=
  generatedTimeAdvanceReceipt
    (shellPhysicalLiftSource current response) ν.coeff

/--
The physical receipt starts at the old physical state.  No selected nonlinear
row has been inserted into the state at time zero.
-/
theorem shellPhysicalTimeReceipt_initial
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current)
    (ν : Viscosity) :
    (shellPhysicalTimeReceipt current response ν).trajectory 0 =
      generatedIntegerShellGalerkinInitialState current response := by
  exact
    (shellPhysicalTimeReceipt current response ν).initial.trans
      (shellPhysicalLiftSource_generatedState current response)

/-- There is no instantaneous physical jump before the unforced segment. -/
theorem shellPhysicalTimeReceipt_initial_eq_currentPhysicalState
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current)
    (ν : Viscosity) :
    (shellPhysicalTimeReceipt current response ν).trajectory 0 =
      generatedComplexVorticityState current
        (generatedSupport current) := by
  rw [shellPhysicalTimeReceipt_initial,
    generatedIntegerShellGalerkinInitialState_eq_currentPhysicalState]

/--
The legacy shell row is an observation of the actual unforced event: it is
the selected row's exact time-zero derivative, not its endpoint increment.
-/
theorem shellPhysicalTimeReceipt_selectedOutput_derivative
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current)
    (ν : Viscosity)
    {output : IntegerWavevector}
    (membership :
      output ∈ generatedOuterNonlinearShellModes
        current response.2.shellSq) :
    HasDerivAt
        (fun time =>
          (shellPhysicalTimeReceipt current response ν).trajectory
            time output)
        (generatedVorticityNonlinearCoefficientAt current output)
        0 := by
  let receipt := shellPhysicalTimeReceipt current response ν
  have zeroInTime :
      (0 : ℝ) ∈ Icc (0 : ℝ) receipt.duration :=
    ⟨le_rfl, receipt.duration_pos.le⟩
  have actualLaw := (receipt.physical 0 zeroInTime).1
  have rowLaw :=
    complexVorticityTrajectoryWave_hasDerivAt
      receipt.trajectory 0
      (finiteStateVorticityGenerator
        (generatedSupport (shellPhysicalLiftSource current response))
        ν.coeff (receipt.trajectory 0))
      output actualLaw
  rw [show receipt.trajectory 0 =
        generatedIntegerShellGalerkinInitialState current response by
      exact shellPhysicalTimeReceipt_initial current response ν,
    shellPhysicalLiftSource_generatedSupport,
    generatedIntegerShellGalerkinGenerator_selectedOutput
      current response ν.coeff membership] at rowLaw
  exact rowLaw

theorem shellPhysicalTimeReceipt_selectedOutput_initial_zero
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current)
    (ν : Viscosity)
    {output : IntegerWavevector}
    (membership :
      output ∈ generatedOuterNonlinearShellModes
        current response.2.shellSq) :
    (shellPhysicalTimeReceipt current response ν).trajectory 0 output =
      0 := by
  rw [shellPhysicalTimeReceipt_initial,
    generatedIntegerShellGalerkinInitialState_apply]
  have outputMem :
      output ∈ generatedIntegerShellGalerkinModes current response :=
    generatedOuterNonlinearShellModes_subset_galerkinModes
      current response membership
  rw [if_pos outputMem,
    generatedVorticityCoefficient_eq_zero_of_mem_outerNonlinearShell
      current response.2.shellSq membership]

theorem shellPhysicalTimeReceipt_selectedOutput_derivative_ne_zero
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current)
    {output : IntegerWavevector}
    (membership :
      output ∈ generatedOuterNonlinearShellModes
        current response.2.shellSq) :
    generatedVorticityNonlinearCoefficientAt current output ≠ 0 :=
  generatedVorticityNonlinearCoefficientAt_ne_zero_of_mem_outerShell
    current response.2.shellSq membership

/-! ## Total target-validation response -/

/--
Physical current plus the path-memory trace written by earlier selected-row
observations.  The ledger is not part of the physical source and is never
materialized by a primitive state jump.
-/
structure UnforcedScaleTimeCurrent where
  physicalSource : RawVorticityFourierSource
  shellTraceLedger : IntegerShellCoefficientCarrier
  elapsed : ℝ

/-- Canonical empty-memory embedding of one physical source. -/
def UnforcedScaleTimeCurrent.ofSource
    (source : RawVorticityFourierSource) :
    UnforcedScaleTimeCurrent where
  physicalSource := source
  shellTraceLedger := 0
  elapsed := 0

/--
Target of a successful shell observation.  The shell response selects only
the enlarged support and the ledger row.  The physical target is solely the
endpoint of the actual unforced receipt.
-/
def unforcedShellTarget
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.physicalSource) :
    UnforcedScaleTimeCurrent :=
  let receipt :=
    shellPhysicalTimeReceipt current.physicalSource response ν
  { physicalSource := receipt.nextSource
    shellTraceLedger :=
      current.shellTraceLedger +
        generatedIntegerShellTrace
          current.physicalSource response.2.shellSq
    elapsed := current.elapsed + receipt.duration }

/--
Target at a faithful shell zero.  The physical source still performs its
actual unforced positive-time update; the shell ledger is unchanged.
-/
def unforcedQuietTarget
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    UnforcedScaleTimeCurrent :=
  let receipt :=
    generatedTimeAdvanceReceipt current.physicalSource ν.coeff
  { physicalSource := receipt.nextSource
    shellTraceLedger := current.shellTraceLedger
    elapsed := current.elapsed + receipt.duration }

/--
Every native edge carries an actual unforced time receipt.  The source-owned
shell responder decides only whether that receipt is observed on an enlarged
support or on the current support.
-/
inductive UnforcedNativeStep
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    UnforcedScaleTimeCurrent → Type
  | shell
      (response :
        Response GeneratedIntegerShellStep current.physicalSource)
      (generated :
        generatedIntegerShellRespond current.physicalSource =
          some response) :
      UnforcedNativeStep ν current
        (unforcedShellTarget ν current response)
  | quiet
      (stopped :
        generatedIntegerShellRespond current.physicalSource = none) :
      UnforcedNativeStep ν current
        (unforcedQuietTarget ν current)

/--
Both the old shell row and the physical receipt are projections of one
event.  The quiet constructor retains the actual receipt together with the
faithful zero provenance.
-/
inductive UnforcedObservation
    (ν : Viscosity) : Type
  | shell
      (legacyReceipt : GeneratedIntegerShellReceipt)
      (physicalReceipt :
        GeneratedTimeAdvanceReceipt
          (shellPhysicalLiftSource
            legacyReceipt.current legacyReceipt.response)
          ν.coeff)
  | quiet
      (source : RawVorticityFourierSource)
      (physicalReceipt :
        GeneratedTimeAdvanceReceipt source ν.coeff)

namespace UnforcedNativeStep

/-- Read both projections of the exact native event. -/
def observation
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : UnforcedNativeStep ν current next) :
    UnforcedObservation ν :=
  match step with
  | .shell response generated =>
      .shell
        (receiptOfResponse
          current.physicalSource response generated)
        (shellPhysicalTimeReceipt
          current.physicalSource response ν)
  | .quiet _ =>
      .quiet current.physicalSource
        (generatedTimeAdvanceReceipt
          current.physicalSource ν.coeff)

end UnforcedNativeStep

/--
Total target-validation response.  No branch, path, duration, endpoint, shell,
nonzero derivative, or continuation certificate is supplied by the caller.
-/
noncomputable def generatedUnforcedScaleTimeRespond
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    Response (UnforcedNativeStep ν) current :=
  match generated :
      generatedIntegerShellRespond current.physicalSource with
  | some response =>
      ⟨unforcedShellTarget ν current response,
        UnforcedNativeStep.shell response generated⟩
  | none =>
      ⟨unforcedQuietTarget ν current,
        UnforcedNativeStep.quiet generated⟩

/-- Observation and physical write are projections of the same event. -/
noncomputable def unforcedScaleTimeReflexiveQuery
    (ν : Viscosity) :
    ReflexiveQuery UnforcedScaleTimeCurrent
      (UnforcedObservation ν) where
  read := fun current =>
    (generatedUnforcedScaleTimeRespond ν current).2.observation
  write := fun current =>
    (generatedUnforcedScaleTimeRespond ν current).1

theorem generatedUnforcedScaleTimeRespond_of_some
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.physicalSource)
    (generated :
      generatedIntegerShellRespond current.physicalSource =
        some response) :
    generatedUnforcedScaleTimeRespond ν current =
      ⟨unforcedShellTarget ν current response,
        UnforcedNativeStep.shell response generated⟩ := by
  unfold generatedUnforcedScaleTimeRespond
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

theorem generatedUnforcedScaleTimeRespond_of_none
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (stopped :
      generatedIntegerShellRespond current.physicalSource = none) :
    generatedUnforcedScaleTimeRespond ν current =
      ⟨unforcedQuietTarget ν current,
        UnforcedNativeStep.quiet stopped⟩ := by
  unfold generatedUnforcedScaleTimeRespond
  split
  · rename_i _response generated
    cases generated.symm.trans stopped
  · rename_i stopped'
    have stoppedEq : stopped' = stopped :=
      Subsingleton.elim _ _
    cases stoppedEq
    rfl

/--
At a successful read, the exact legacy shell receipt and the target-side
unforced time receipt are emitted while the actual endpoint is written.
-/
theorem unforcedScaleTimeReflexiveQuery_run_of_some
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.physicalSource)
    (generated :
      generatedIntegerShellRespond current.physicalSource =
        some response) :
    ReflexiveQuery.run (unforcedScaleTimeReflexiveQuery ν) current =
      (.shell
          (receiptOfResponse
            current.physicalSource response generated)
          (shellPhysicalTimeReceipt
            current.physicalSource response ν),
        unforcedShellTarget ν current response) := by
  unfold ReflexiveQuery.run unforcedScaleTimeReflexiveQuery
  change
    ((generatedUnforcedScaleTimeRespond ν current).2.observation,
      (generatedUnforcedScaleTimeRespond ν current).1) =
      (.shell
          (receiptOfResponse
            current.physicalSource response generated)
          (shellPhysicalTimeReceipt
            current.physicalSource response ν),
        unforcedShellTarget ν current response)
  rw [generatedUnforcedScaleTimeRespond_of_some
    ν current response generated]
  rfl

/--
At a faithful shell zero, the same query still writes an actual positive-time
unforced endpoint and emits its receipt.
-/
theorem unforcedScaleTimeReflexiveQuery_run_of_none
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (stopped :
      generatedIntegerShellRespond current.physicalSource = none) :
    ReflexiveQuery.run (unforcedScaleTimeReflexiveQuery ν) current =
      (.quiet current.physicalSource
          (generatedTimeAdvanceReceipt
            current.physicalSource ν.coeff),
        unforcedQuietTarget ν current) := by
  unfold ReflexiveQuery.run unforcedScaleTimeReflexiveQuery
  change
    ((generatedUnforcedScaleTimeRespond ν current).2.observation,
      (generatedUnforcedScaleTimeRespond ν current).1) =
      (.quiet current.physicalSource
          (generatedTimeAdvanceReceipt
            current.physicalSource ν.coeff),
        unforcedQuietTarget ν current)
  rw [generatedUnforcedScaleTimeRespond_of_none
    ν current stopped]
  rfl

/-! ## Exact physical and ledger laws of the same event -/

theorem unforcedShellTarget_physicalState
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.physicalSource) :
    generatedComplexVorticityState
        (unforcedShellTarget ν current response).physicalSource
        (generatedSupport
          (unforcedShellTarget ν current response).physicalSource) =
      (shellPhysicalTimeReceipt
        current.physicalSource response ν).endpoint := by
  exact
    (shellPhysicalTimeReceipt
      current.physicalSource response ν).nextSource_generatedState

theorem unforcedShellTarget_shellTraceLedger
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.physicalSource) :
    (unforcedShellTarget ν current response).shellTraceLedger =
      current.shellTraceLedger +
        generatedIntegerShellTrace
          current.physicalSource response.2.shellSq :=
  rfl

theorem unforcedShellTarget_elapsed_lt
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.physicalSource) :
    current.elapsed <
      (unforcedShellTarget ν current response).elapsed := by
  exact
    lt_add_of_pos_right _
      (shellPhysicalTimeReceipt
        current.physicalSource response ν).duration_pos

theorem unforcedQuietTarget_physicalState
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    generatedComplexVorticityState
        (unforcedQuietTarget ν current).physicalSource
        (generatedSupport
          (unforcedQuietTarget ν current).physicalSource) =
      (generatedTimeAdvanceReceipt
        current.physicalSource ν.coeff).endpoint := by
  exact
    (generatedTimeAdvanceReceipt
      current.physicalSource ν.coeff).nextSource_generatedState

@[simp] theorem unforcedQuietTarget_shellTraceLedger
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    (unforcedQuietTarget ν current).shellTraceLedger =
      current.shellTraceLedger :=
  rfl

theorem unforcedQuietTarget_elapsed_lt
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    current.elapsed <
      (unforcedQuietTarget ν current).elapsed := by
  exact
    lt_add_of_pos_right _
      (generatedTimeAdvanceReceipt
        current.physicalSource ν.coeff).duration_pos

/--
Source-generated one-event disposition.  The successful branch packages the
no-impulse law, actual PDE update, nonzero derivative readout, and separate
ledger write.  The quiet branch packages faithful shell zero and an actual
PDE update.  There is no continuation-only outlet.
-/
inductive GeneratedUnforcedDisposition
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) : Type
  | shell
      (response :
        Response GeneratedIntegerShellStep current.physicalSource)
      (generated :
        generatedIntegerShellRespond current.physicalSource =
          some response)
      (run :
        ReflexiveQuery.run
            (unforcedScaleTimeReflexiveQuery ν) current =
          (.shell
              (receiptOfResponse
                current.physicalSource response generated)
              (shellPhysicalTimeReceipt
                current.physicalSource response ν),
            unforcedShellTarget ν current response))
      (durationPos :
        0 <
          (shellPhysicalTimeReceipt
            current.physicalSource response ν).duration)
      (noImpulse :
        (shellPhysicalTimeReceipt
            current.physicalSource response ν).trajectory 0 =
          generatedComplexVorticityState current.physicalSource
            (generatedSupport current.physicalSource))
      (selectedDerivative :
        ∀ output ∈ generatedOuterNonlinearShellModes
            current.physicalSource response.2.shellSq,
          HasDerivAt
              (fun time =>
                (shellPhysicalTimeReceipt
                  current.physicalSource response ν).trajectory
                    time output)
              (generatedVorticityNonlinearCoefficientAt
                current.physicalSource output)
              0 ∧
            (shellPhysicalTimeReceipt
                current.physicalSource response ν).trajectory
                0 output =
              0 ∧
            generatedVorticityNonlinearCoefficientAt
                current.physicalSource output ≠
              0)
      (nextPhysical :
        generatedComplexVorticityState
            (unforcedShellTarget
              ν current response).physicalSource
            (generatedSupport
              (unforcedShellTarget
                ν current response).physicalSource) =
          (shellPhysicalTimeReceipt
            current.physicalSource response ν).endpoint)
      (ledgerWrite :
        (unforcedShellTarget
            ν current response).shellTraceLedger =
          current.shellTraceLedger +
            generatedIntegerShellTrace
              current.physicalSource response.2.shellSq)
  | quiet
      (stopped :
        generatedIntegerShellRespond current.physicalSource = none)
      (outerReadZero :
        reflexiveObservation current.physicalSource = 0)
      (run :
        ReflexiveQuery.run
            (unforcedScaleTimeReflexiveQuery ν) current =
          (.quiet current.physicalSource
              (generatedTimeAdvanceReceipt
                current.physicalSource ν.coeff),
            unforcedQuietTarget ν current))
      (durationPos :
        0 <
          (generatedTimeAdvanceReceipt
            current.physicalSource ν.coeff).duration)
      (nextPhysical :
        generatedComplexVorticityState
            (unforcedQuietTarget ν current).physicalSource
            (generatedSupport
              (unforcedQuietTarget ν current).physicalSource) =
          (generatedTimeAdvanceReceipt
            current.physicalSource ν.coeff).endpoint)
      (ledgerSilent :
        (unforcedQuietTarget ν current).shellTraceLedger =
          current.shellTraceLedger)

/-- Generate the exact actual-time event without an input branch. -/
noncomputable def generatedUnforcedScaleTimeDisposition
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    GeneratedUnforcedDisposition ν current := by
  cases generated :
      generatedIntegerShellRespond current.physicalSource with
  | some response =>
      exact
        .shell response generated
          (unforcedScaleTimeReflexiveQuery_run_of_some
            ν current response generated)
          (shellPhysicalTimeReceipt
            current.physicalSource response ν).duration_pos
          (shellPhysicalTimeReceipt_initial_eq_currentPhysicalState
            current.physicalSource response ν)
          (by
            intro output membership
            exact
              ⟨shellPhysicalTimeReceipt_selectedOutput_derivative
                  current.physicalSource response ν membership,
                shellPhysicalTimeReceipt_selectedOutput_initial_zero
                  current.physicalSource response ν membership,
                shellPhysicalTimeReceipt_selectedOutput_derivative_ne_zero
                  current.physicalSource response membership⟩)
          (unforcedShellTarget_physicalState ν current response)
          (unforcedShellTarget_shellTraceLedger ν current response)
  | none =>
      exact
        .quiet generated
          (reflexiveObservation_of_none
            current.physicalSource generated)
          (unforcedScaleTimeReflexiveQuery_run_of_none
            ν current generated)
          (generatedTimeAdvanceReceipt
            current.physicalSource ν.coeff).duration_pos
          (unforcedQuietTarget_physicalState ν current)
          (unforcedQuietTarget_shellTraceLedger ν current)

end

end ThreeDimensionalVorticityCoefficientGeneratedUnforcedScaleTimeReceipt
end NavierStokes
end SaturationMonoid
