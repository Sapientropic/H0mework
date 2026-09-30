import H0mework.NavierStokes.WindowPhysics.RootControl
import H0mework.NavierStokes.PhysicalView.RootPairing

set_option autoImplicit false
open scoped Topology ENNReal NNReal Convolution

namespace SaturationMonoid.NavierStokes.NativeViewPreparation

open Set Filter MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeCompleteStressAction NativeCompleteHeatTransport
open NativeWindowRootCarrier NativeWindowRootControl NativeEndpointVelocityCarrier

noncomputable section

/-- A preparation takes two units of the original physical clock. -/
def laboratoryClock (origin time : ℝ) : ℝ := origin + 2 + time

theorem laboratoryClock_hasDerivAt (origin time : ℝ) :
    HasDerivAt (laboratoryClock origin) 1 time :=
  (hasDerivAt_id time).const_add (origin + 2)

theorem laboratoryClock_advance (origin advance time : ℝ) :
    laboratoryClock (origin + advance) time = laboratoryClock origin (advance + time) := by
  unfold laboratoryClock
  ring

theorem kernel_window (shift : ℝ) (nonzero : NativeForwardWindowSource.kernel shift ≠ 0) :
    shift ∈ Ioo (-2 : ℝ) (-1) := by
  have inside : shift ∈ Metric.ball (-3 / 2 : ℝ) (1 / 2) := by
    have member : shift ∈ Function.support (NativeForwardWindowSource.bump.normed volume) := nonzero
    rw [NativeForwardWindowSource.bump.support_normed_eq] at member
    exact member
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at inside
  constructor <;> linarith

theorem sample_before_laboratoryClock (origin time shift : ℝ)
    (nonzero : NativeForwardWindowSource.kernel shift ≠ 0) :
    origin + (time - shift) ∈ Ioo (laboratoryClock origin time - 1) (laboratoryClock origin time) := by
  have inside := kernel_window shift nonzero
  constructor <;> dsimp [laboratoryClock] <;> linarith [inside.1, inside.2]

/-- This predicts a measurement from a mathematical history; it does not declare its samples already observed. -/
def predict (nu : Viscosity) (lag : ℝ≥0) (history : ℝ → FullSpace) (time : ℝ) : FullSpace :=
  fullHeatCLM nu lag (∫ shift : ℝ, NativeForwardWindowSource.kernel shift • history (time - shift))

def laboratoryRead (nu : Viscosity) (lag : ℝ≥0) (history : ℝ → FullSpace) (clock : ℝ) : FullSpace :=
  predict nu lag history (clock - 2)

theorem predict_local (nu : Viscosity) (lag : ℝ≥0) (first last : ℝ → FullSpace) (time : ℝ)
    (same : EqOn first last (Icc (time + 1) (time + 2))) :
    predict nu lag first time = predict nu lag last time := by
  apply congrArg (fullHeatCLM nu lag)
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : NativeForwardWindowSource.kernel shift = 0
  · simp only [zero, zero_smul]
  · have inside := kernel_window shift zero
    exact congrArg (fun value : FullSpace => NativeForwardWindowSource.kernel shift • value)
      (same (show time - shift ∈ Icc (time + 1) (time + 2) from ⟨by linarith [inside.2], by linarith [inside.1]⟩))

theorem laboratoryRead_local (nu : Viscosity) (lag : ℝ≥0) (first last : ℝ → FullSpace) (clock : ℝ)
    (same : EqOn first last (Icc (clock - 1) clock)) :
    laboratoryRead nu lag first clock = laboratoryRead nu lag last clock := by
  apply predict_local
  intro sample inside
  exact same ⟨by linarith [inside.1], by linarith [inside.2]⟩

theorem predict_past_local (nu : Viscosity) (lag : ℝ≥0) (first last : ℝ → FullSpace) (origin time : ℝ)
    (same : EqOn first last (Icc (laboratoryClock origin time - 1) (laboratoryClock origin time))) :
    predict nu lag (fun sample => first (origin + sample)) time =
      predict nu lag (fun sample => last (origin + sample)) time := by
  apply predict_local
  intro sample inside
  apply same
  constructor <;> dsimp [laboratoryClock] <;> linarith [inside.1, inside.2]

variable {nu : Viscosity}

def rootClock (initial : GeneratedWholeRestartCurrent nu) (current : NativeTemporalCurrent initial) (time : ℝ) : ℝ :=
  laboratoryClock (clockAt initial current) time

theorem rootClock_hasDerivAt (initial : GeneratedWholeRestartCurrent nu) (current : NativeTemporalCurrent initial) (time : ℝ) :
    HasDerivAt (rootClock initial current) 1 time := laboratoryClock_hasDerivAt _ _

theorem rootClock_finite_next (initial : GeneratedWholeRestartCurrent nu) (index : ℕ) (time : ℝ) :
    rootClock initial (.finite (index + 1)) time =
      rootClock initial (.finite index) ((run initial index).contact.time.1 + time) := by
  simp only [rootClock, clockAt, elapsedTime_succ, laboratoryClock]
  ring

theorem rootClock_cofinal_next (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    rootClock initial (.galerkin 0) time = rootClock initial .cofinal time := rfl

theorem rootClock_galerkin_next (initial : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) :
    rootClock initial (.galerkin (radius + 1)) time = rootClock initial (.galerkin radius) time := rfl

variable {initial : GeneratedWholeRestartCurrent nu} {current : NativeTemporalCurrent initial}
    {occurrence : Occurrence initial current}

theorem view_predict (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (time : ℝ) :
    carrier.view lag time = predict nu lag carrier.history time := rfl

theorem view_laboratory_read (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (time : ℝ) :
    carrier.view lag time = laboratoryRead nu lag (NativeUnifiedCompleteSource.source initial)
      (rootClock initial current time) := by
  rw [CarrierAt.view_generated]
  have clock : rootClock initial current time - 2 = clockAt initial current + time := by
    unfold rootClock laboratoryClock
    ring
  unfold laboratoryRead
  rw [clock]
  rfl

theorem view_past_local (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (time : ℝ)
    (samples : ℝ → FullSpace)
    (same : EqOn samples (NativeUnifiedCompleteSource.source initial)
      (Icc (rootClock initial current time - 1) (rootClock initial current time))) :
    predict nu lag (fun sample => samples (clockAt initial current + sample)) time = carrier.view lag time := by
  rw [view_predict, carrier.history_eq]
  exact predict_past_local nu lag samples (NativeUnifiedCompleteSource.source initial) _ time same

/-- The prepared initial state is the same complete measurement at laboratory time origin+2. -/
def preparedInitial (carrier : CarrierAt initial occurrence) (query : HeatQuery) : FullSpace := carrier.view query.1 0

theorem prepared_integral (carrier : CarrierAt initial occurrence) (query : HeatQuery) :
    preparedInitial carrier query = fullHeatCLM nu query.1 (∫ shift : ℝ,
      NativeForwardWindowSource.kernel shift • NativeUnifiedCompleteSource.source initial (clockAt initial current - shift)) := by
  change fullHeatCLM nu query.1 (∫ shift : ℝ,
    NativeForwardWindowSource.kernel shift • carrier.history (0 - shift)) = _
  rw [carrier.history_eq]
  simp only [sub_eq_add_neg, zero_add]

def preparedData (carrier : CarrierAt initial occurrence) (query : HeatQuery) : NativeStressPairingCarrier.Data :=
  NativeWindowRootPairing.data carrier query 0

theorem prepared_readbacks (carrier : CarrierAt initial occurrence) (query : HeatQuery) :
    (preparedData carrier query).mean = (preparedInitial carrier query).fst ∧
      (preparedData carrier query).stress = NativeCompleteStressCarrier.read (preparedInitial carrier query).snd ∧
      (preparedData carrier query).stress - NativeStressSource.quadraticFlux (wholeVelocity (preparedData carrier query).mean) =
        NativeCompleteCorrectionRead.residual (preparedInitial carrier query) :=
  ⟨NativeWindowRootPairing.data_mean carrier query 0, NativeWindowRootPairing.data_stress carrier query 0,
    NativeWindowRootPairing.data_residual carrier query 0⟩

theorem prepared_canonical_current (carrier : CarrierAt initial occurrence) (query : HeatQuery)
    (direction : Fin 4) (wave : IntegerWavevector) :
    NativeHilbertDiracCurrent.diracCurrent (preparedData carrier query) direction wave =
      NativePairedCurrentFourier.coefficient (wholeVelocity (preparedInitial carrier query).fst)
        (NativeCompleteStressCarrier.read (preparedInitial carrier query).snd) direction wave :=
  NativeWindowRootPairing.canonical_current carrier query 0 direction wave

theorem authority_prepared_initial (seed : GeneratedWholeRestartCurrent nu)
    (visit : SourceNativeTemporalVisitAt (nativeTemporalRoot seed)) (query : HeatQuery) :
    let carrier := authorityCarrier seed visit query
    preparedInitial carrier query = fullHeatCLM nu query.1 (∫ shift : ℝ,
      NativeForwardWindowSource.kernel shift • NativeUnifiedCompleteSource.source seed (clockAt seed visit.current - shift)) ∧
      ∀ shift : ℝ, NativeForwardWindowSource.kernel shift ≠ 0 →
        clockAt seed visit.current - shift ∈ Ioo (rootClock seed visit.current 0 - 1) (rootClock seed visit.current 0) := by
  dsimp only
  refine ⟨prepared_integral _ _, ?_⟩
  intro shift nonzero
  simpa only [rootClock, sub_eq_add_neg, zero_add] using
    sample_before_laboratoryClock (clockAt seed visit.current) 0 shift nonzero

theorem finite_prepared_next (seed : GeneratedWholeRestartCurrent nu) (index : ℕ) (query : HeatQuery) :
    preparedInitial (generatedCarrier seed (nativeTemporalEmitted seed (.finite (index + 1)))) query =
      (generatedCarrier seed (nativeTemporalEmitted seed (.finite index))).view query.1 (run seed index).contact.time.1 := by
  simpa only [preparedInitial, add_zero] using finite_next_view seed index query 0

theorem macro_next_exact (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (lag : ℝ≥0) (origin time : ℝ) (nonnegative : 0 ≤ time) :
    (NativeWindowHeatEvolution.source response.1 lag time, laboratoryClock (origin + response.2.clockAdvance) time) =
      (NativeWindowHeatEvolution.source seed lag (response.2.clockAdvance + time),
        laboratoryClock origin (response.2.clockAdvance + time)) :=
  Prod.ext (NativeWindowHeatEvolution.source_next seed lag response generated time nonnegative).symm
    (laboratoryClock_advance origin response.2.clockAdvance time)

end
end SaturationMonoid.NavierStokes.NativeViewPreparation
