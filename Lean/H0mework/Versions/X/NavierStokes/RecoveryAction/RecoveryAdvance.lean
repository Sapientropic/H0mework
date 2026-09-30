import H0mework.Versions.X.NavierStokes.RecoveryAction.Recovery
import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryWindow

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryWindowAdvance

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalTimeConsumer
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open ThreeDimensionalVorticityCoefficientSourceOwnedLocalCompactnessBudget
open NativeRecoveryControlProducer NativeEndpointPositiveTime NativeFullOrderFlux
open NativeRecoveryStrongWindow NativeRecoveryRowAction

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}

def localGradientAllowance (nu : Viscosity) (ceiling duration : ℝ) : ℝ :=
  (ceiling / 2 + sourceOwnedLocalQuadraticCoefficient nu ceiling * ceiling ^ 2 * duration) /
    ((3 * nu.coeff / 8) * (2 * Real.pi) ^ 2)

def localActivityAllowance (nu : Viscosity) (ceiling duration : ℝ) : ℝ :=
  2 * sourceOwnedLocalCoreVelocityCoefficient nu ceiling * ceiling * duration +
    2 * biotSavartSerrinConstant * sourceOwnedKernelTailTolerance nu ceiling * localGradientAllowance nu ceiling duration

theorem endpoint_local_control
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) (anchor ceiling duration : ℝ) (anchorNonnegative : 0 ≤ anchor) (durationNonnegative : 0 ≤ duration)
    (lastLe : anchor + duration ≤ 1)
    (initialFits : finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius)
      ((ledger.family.stage radius).trajectory anchor) + 1 ≤ ceiling)
    (durationFits : duration ≤ sourceOwnedWholeStateDuration nu ceiling) :
    (∀ time ∈ Icc anchor (anchor + duration), finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius)
      ((ledger.family.stage radius).trajectory time) ≤ ceiling) ∧
      (∫ time in anchor..(anchor + duration), finiteStateVelocityMajorant (wholeRestartModes radius)
        ((ledger.family.stage radius).trajectory time) ^ 2) ≤ localActivityAllowance nu ceiling duration := by
  let path := fun time => (ledger.family.stage radius).trajectory (anchor + time)
  have actualTime (time : ℝ) (inside : time ∈ Icc (0 : ℝ) duration) : anchor + time ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [inside.1, inside.2]
  have budget := finiteStateVorticity_sourceOwnedWholeStateCompactnessBudget_on_Icc
    (wholeRestartModes radius) (fun _ member => puncturedIntegerWaveFrequencyCube_waveNeg_mem radius member)
    nu ceiling path duration durationNonnegative (by simpa only [path, add_zero] using initialFits) durationFits
    (fun time inside => HasDerivAt.comp_const_add anchor time
      ((ledger.family.stage radius).physical (anchor + time) (actualTime time inside)).1)
    (fun time inside => ((ledger.family.stage radius).physical (anchor + time) (actualTime time inside)).2.2.2)
    (fun time inside wave _ => ((ledger.family.stage radius).physical (anchor + time) (actualTime time inside)).2.2.1 wave)
  have gradient : (∫ time in 0..duration, finiteStateVorticityEnstrophyMass (wholeRestartModes radius) (path time)) ≤
      localGradientAllowance nu ceiling duration := by
    apply (le_div_iff₀ (wholeRestartGradientCoefficient_pos nu)).mpr
    rw [mul_comm]
    apply budget.2.1.trans
    have initial : finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius) (path 0) + 1 ≤ ceiling := by
      simpa only [path, add_zero] using initialFits
    dsimp only [finiteStateVorticityHalfEnstrophy]
    linarith
  have activity : (∫ time in 0..duration, finiteStateVelocityMajorant (wholeRestartModes radius) (path time) ^ 2) ≤
      localActivityAllowance nu ceiling duration := by
    apply budget.2.2.1.trans
    unfold localActivityAllowance
    gcongr
    exact mul_nonneg (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
      (sourceOwnedKernelTailTolerance_pos nu _).le
  refine ⟨?_, ?_⟩
  · intro time inside
    have original := budget.1 (time - anchor) ⟨by linarith [inside.1], by linarith [inside.2]⟩
    simpa only [path, add_sub_cancel] using original
  · have same := intervalIntegral.integral_comp_add_left
      (fun time => finiteStateVelocityMajorant (wholeRestartModes radius) ((ledger.family.stage radius).trajectory time) ^ 2)
      (a := 0) (b := duration) anchor
    simp only [add_zero] at same
    rw [← same]
    exact activity

structure ControlSpan (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal : ℝ) where
  first : ℝ
  last : ℝ
  first_nonnegative : 0 ≤ first
  ordered : first < last
  last_lt : last < terminal
  terminal_le_one : terminal ≤ 1
  ceiling : ℝ
  activity : ℝ
  extraction : ℕ → ℕ
  extraction_strict : StrictMono extraction
  paid : ∀ᶠ index in atTop,
    (∀ time ∈ Icc first last, finiteStateVorticityCoefficientEnstrophy
      (wholeRestartModes (receipt.core.subsequence (extraction index)))
      ((ledger.family.stage (receipt.core.subsequence (extraction index))).trajectory time) ≤ ceiling) ∧
    (∫ time in first..last, finiteStateVelocityMajorant
      (wholeRestartModes (receipt.core.subsequence (extraction index)))
      ((ledger.family.stage (receipt.core.subsequence (extraction index))).trajectory time) ^ 2) ≤ activity

variable {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {terminal : ℝ}

def generatedSpan (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal : ℝ) (positive : 0 < terminal) (terminalLe : terminal ≤ 1) : ControlSpan receipt terminal := Classical.choice (by
  let lower := terminal / 4
  let upper := terminal / 2
  have lowerNonnegative : 0 ≤ lower := by dsimp [lower]; positivity
  have ordered : lower < upper := by dsimp [lower, upper]; linarith
  have upperLt : upper < 1 := by dsimp [upper]; linarith
  obtain ⟨center, centerInside, extraction, extractionStrict, source⟩ :=
    common_source_control_window ledger receipt.core lower upper lowerNonnegative ordered upperLt
  let duration := bandDuration ledger lower upper
  have durationPositive : 0 < duration := bandDuration_pos ledger lower upper ordered upperLt
  have durationLe : duration ≤ upper - lower := bandDuration_le_width ledger lower upper
  refine ⟨{ first := center + duration / 3
            last := center + 2 * duration / 3
            first_nonnegative := by linarith [centerInside.1]
            ordered := by linarith
            last_lt := by dsimp [lower, upper] at durationLe centerInside; linarith [centerInside.2]
            terminal_le_one := terminalLe
            ceiling := bandCeiling ledger lower upper
            activity := bandVelocityAllowance ledger lower upper
            extraction := extraction
            extraction_strict := extractionStrict
            paid := ?_ }⟩
  filter_upwards [source] with index paid
  exact ⟨fun time inside => (paid.1 time inside).2.2, paid.2⟩)

def ControlSpan.duration (span : ControlSpan receipt terminal) : ℝ :=
  min (sourceOwnedWholeStateDuration nu (span.ceiling + 1)) ((terminal - span.last) / 2)

theorem ControlSpan.duration_pos (span : ControlSpan receipt terminal) : 0 < span.duration :=
  lt_min (sourceOwnedWholeStateDuration_pos nu _) (half_pos (sub_pos.mpr span.last_lt))

theorem ControlSpan.advance_last_lt (span : ControlSpan receipt terminal) : span.last + span.duration < terminal := by
  have durationLe : span.duration ≤ (terminal - span.last) / 2 := min_le_right _ _
  linarith [span.last_lt]

def ControlSpan.advance (span : ControlSpan receipt terminal) : ControlSpan receipt terminal where
  first := span.first
  last := span.last + span.duration
  first_nonnegative := span.first_nonnegative
  ordered := by linarith [span.ordered, span.duration_pos]
  last_lt := span.advance_last_lt
  terminal_le_one := span.terminal_le_one
  ceiling := span.ceiling + 1
  activity := span.activity + localActivityAllowance nu (span.ceiling + 1) span.duration
  extraction := span.extraction
  extraction_strict := span.extraction_strict
  paid := by
    filter_upwards [span.paid] with index previous
    let radius := receipt.core.subsequence (span.extraction index)
    have rightNonnegative : 0 ≤ span.last := span.first_nonnegative.trans span.ordered.le
    have rightInside : span.last ∈ Icc span.first span.last := ⟨span.ordered.le, le_rfl⟩
    have future := endpoint_local_control ledger radius span.last (span.ceiling + 1) span.duration
      rightNonnegative span.duration_pos.le (span.advance_last_lt.le.trans span.terminal_le_one)
      (by have actual := previous.1 span.last rightInside; linarith) (min_le_left _ _)
    constructor
    · intro time inside
      by_cases earlier : time ≤ span.last
      · have old := previous.1 time ⟨inside.1, earlier⟩
        linarith
      · exact future.1 time ⟨(lt_of_not_ge earlier).le, inside.2⟩
    · let density (time : ℝ) := finiteStateVelocityMajorant (wholeRestartModes radius)
        ((ledger.family.stage radius).trajectory time) ^ 2
      have integrable : IntervalIntegrable density volume 0 1 := by
        apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
        intro time inside
        exact ((finiteStateVelocityMajorant_continuousAt_of_hasDerivAt (wholeRestartModes radius)
          (ledger.family.stage radius).trajectory time _ ((ledger.family.stage radius).physical time inside).1).pow 2).continuousWithinAt
      have oldIntegrable : IntervalIntegrable density volume span.first span.last := integrable.mono_set (by
        rw [uIcc_of_le span.ordered.le, uIcc_of_le zero_le_one]
        exact Icc_subset_Icc span.first_nonnegative (span.last_lt.le.trans span.terminal_le_one))
      have newIntegrable : IntervalIntegrable density volume span.last (span.last + span.duration) := integrable.mono_set (by
        rw [uIcc_of_le (by linarith [span.duration_pos]), uIcc_of_le zero_le_one]
        exact Icc_subset_Icc rightNonnegative (span.advance_last_lt.le.trans span.terminal_le_one))
      have total := add_le_add previous.2 future.2
      change (∫ time in span.first..span.last, density time) +
        (∫ time in span.last..(span.last + span.duration), density time) ≤ _ at total
      rw [intervalIntegral.integral_add_adjacent_intervals oldIntegrable newIntegrable] at total
      exact total

theorem ControlSpan.last_lt_advance (span : ControlSpan receipt terminal) : span.last < span.advance.last := by
  change span.last < span.last + span.duration
  linarith [span.duration_pos]

theorem ControlSpan.advance_geometry (span : ControlSpan receipt terminal) :
    span.advance.first = span.first ∧ span.last < span.advance.last ∧
      span.advance.extraction = span.extraction :=
  ⟨rfl, span.last_lt_advance, rfl⟩

theorem ControlSpan.moment_control (span : ControlSpan receipt terminal) (order : ℕ) (delta : ℝ)
    (deltaPositive : 0 < delta) (fits : span.first + delta ≤ span.last)
    (time : Icc (0 : ℝ) 1) (afterStart : span.first + delta ≤ time.1) (beforeEnd : time.1 ≤ span.last) :
    Summable (velocityMomentDensity order (receipt.wholePath time)) ∧
      (∑' wave, velocityMomentDensity order (receipt.wholePath time) wave) ≤ endpointBudget ledger span.activity order delta := by
  rw [receipt.wholePath_apply]
  apply wholeMild_moment_of_eventual_stage_control ledger receipt.core span.extraction span.extraction_strict order _ time
  intro ceiling ceilingNonnegative
  filter_upwards [span.paid] with index paid
  exact endpoint_positive_time_energy_bound ledger (receipt.core.subsequence (span.extraction index))
    span.first span.last span.first_nonnegative span.ordered.le (span.last_lt.le.trans span.terminal_le_one)
    span.activity paid.2 order delta deltaPositive fits ceiling ceilingNonnegative time.1 ⟨afterStart, beforeEnd⟩

def ControlSpan.regularFirst (span : ControlSpan receipt terminal) : ℝ := (span.first + span.last) / 2

theorem ControlSpan.advance_regular_geometry (span : ControlSpan receipt terminal) :
    span.first < span.regularFirst ∧ span.regularFirst < span.last ∧
      span.last < span.advance.last ∧ span.advance.last < terminal := by
  refine ⟨?_, ?_, span.last_lt_advance, span.advance.last_lt⟩
  · unfold ControlSpan.regularFirst
    linarith [span.ordered]
  · unfold ControlSpan.regularFirst
    linarith [span.ordered]

theorem ControlSpan.regular_moment_control (span : ControlSpan receipt terminal)
    (order : ℕ) (time : Icc (0 : ℝ) 1) (afterStart : span.regularFirst ≤ time.1) (beforeEnd : time.1 ≤ span.last) :
    Summable (velocityMomentDensity order (receipt.wholePath time)) ∧
      (∑' wave, velocityMomentDensity order (receipt.wholePath time) wave) ≤
        endpointBudget ledger span.activity order ((span.last - span.first) / 2) := by
  apply span.moment_control order ((span.last - span.first) / 2) (by linarith [span.ordered])
    (by linarith [span.ordered]) time _ beforeEnd
  dsimp only [ControlSpan.regularFirst] at afterStart
  linarith

theorem ControlSpan.advance_moment_control (span : ControlSpan receipt terminal)
    (order : ℕ) (time : Icc (0 : ℝ) 1)
    (afterStart : span.regularFirst ≤ time.1) (beforeEnd : time.1 ≤ span.advance.last) :
    Summable (velocityMomentDensity order (receipt.wholePath time)) ∧
      (∑' wave, velocityMomentDensity order (receipt.wholePath time) wave) ≤
        endpointBudget ledger span.advance.activity order ((span.last - span.first) / 2) := by
  apply span.advance.moment_control order ((span.last - span.first) / 2) (by linarith [span.ordered]) _ time _ beforeEnd
  · change span.first + (span.last - span.first) / 2 ≤ span.advance.last
    linarith [span.ordered, span.last_lt_advance]
  · change span.first + (span.last - span.first) / 2 ≤ time.1
    unfold ControlSpan.regularFirst at afterStart
    linarith

def sourceSpan (initial : GeneratedWholeRestartCurrent nu) :
    ControlSpan (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 :=
  generatedSpan (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time_pos
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2

theorem source_advance_geometry (initial : GeneratedWholeRestartCurrent nu) :
    (sourceSpan initial).first < (sourceSpan initial).regularFirst ∧
      (sourceSpan initial).regularFirst < (sourceSpan initial).last ∧
      (sourceSpan initial).last < (sourceSpan initial).advance.last ∧
      (sourceSpan initial).advance.last < (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 ∧
      (sourceSpan initial).advance.extraction = (sourceSpan initial).extraction := by
  have actual := (sourceSpan initial).advance_regular_geometry
  exact ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2, rfl⟩

theorem source_advance_all_moments (initial : GeneratedWholeRestartCurrent nu)
    (order : ℕ) (time : Icc (0 : ℝ) 1)
    (afterStart : (sourceSpan initial).regularFirst ≤ time.1)
    (beforeEnd : time.1 ≤ (sourceSpan initial).advance.last) :
    Summable (velocityMomentDensity order
      ((sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).wholePath time)) ∧
      (∑' wave, velocityMomentDensity order
        ((sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).wholePath time) wave) ≤
          endpointBudget (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore initial)
            (sourceSpan initial).advance.activity order (((sourceSpan initial).last - (sourceSpan initial).first) / 2) :=
  (sourceSpan initial).advance_moment_control order time afterStart beforeEnd

def ControlSpan.iterate (span : ControlSpan receipt terminal) : ℕ → ControlSpan receipt terminal
  | 0 => span
  | index + 1 => (span.iterate index).advance

theorem ControlSpan.iterate_last_strictMono (span : ControlSpan receipt terminal) :
    StrictMono (fun index => (span.iterate index).last) := by
  apply strictMono_nat_of_lt_succ
  intro index
  exact (span.iterate index).last_lt_advance

theorem ControlSpan.iterate_first (span : ControlSpan receipt terminal) (index : ℕ) :
    (span.iterate index).first = span.first := by
  induction index with
  | zero => rfl
  | succ index previous => exact previous

theorem ControlSpan.iterate_extraction (span : ControlSpan receipt terminal) (index : ℕ) :
    (span.iterate index).extraction = span.extraction := by
  induction index with
  | zero => rfl
  | succ index previous => exact previous

def ControlSpan.toControlledWindow (span : ControlSpan receipt terminal) (delta : ℝ)
    (positive : 0 < delta) (fits : span.first + delta < span.last) :
    ControlledWindow receipt span.first terminal where
  first := span.first + delta
  last := span.last
  lower_lt := by linarith
  ordered := fits
  upper_lt := span.last_lt
  first_pos := by linarith [span.first_nonnegative]
  last_lt_one := span.last_lt.trans_le span.terminal_le_one
  budget := fun order => endpointBudget ledger span.activity order delta
  paid := by
    intro order time inside
    let original : Icc (0 : ℝ) 1 := ⟨time, by
      constructor <;> linarith [span.first_nonnegative, span.last_lt, span.terminal_le_one, inside.1, inside.2]⟩
    rw [velocity_on_interval receipt original]
    exact (span.moment_control order delta positive fits.le original inside.1 inside.2).1
  bound := by
    intro order time inside
    let original : Icc (0 : ℝ) 1 := ⟨time, by
      constructor <;> linarith [span.first_nonnegative, span.last_lt, span.terminal_le_one, inside.1, inside.2]⟩
    rw [velocity_on_interval receipt original]
    exact (span.moment_control order delta positive fits.le original inside.1 inside.2).2

def sourceAdvanceWindow (initial : GeneratedWholeRestartCurrent nu) :
    ControlledWindow (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceSpan initial).first (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 :=
  (sourceSpan initial).advance.toControlledWindow
    (((sourceSpan initial).last - (sourceSpan initial).first) / 2)
    (by linarith [(sourceSpan initial).ordered])
    (by
      change (sourceSpan initial).first + ((sourceSpan initial).last - (sourceSpan initial).first) / 2 <
        (sourceSpan initial).advance.last
      linarith [(sourceSpan initial).ordered, (sourceSpan initial).last_lt_advance])

theorem sourceAdvanceWindow_reads_span (initial : GeneratedWholeRestartCurrent nu) :
    (sourceAdvanceWindow initial).first = (sourceSpan initial).regularFirst ∧
      (sourceAdvanceWindow initial).last = (sourceSpan initial).advance.last := by
  constructor
  · change (sourceSpan initial).first + ((sourceSpan initial).last - (sourceSpan initial).first) / 2 =
      ((sourceSpan initial).first + (sourceSpan initial).last) / 2
    ring
  · rfl

end
end SaturationMonoid.NavierStokes.NativeRecoveryWindowAdvance
