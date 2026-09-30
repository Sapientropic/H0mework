import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryAE

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryCoverage

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
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open NativeRecoveryControlProducer NativeRecoveryWindowAdvance NativeRecoveryAEWindows

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}

theorem controlSpan_through_of_frequent_source_bound
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal point anchor ceiling : ℝ) (terminalLe : terminal ≤ 1)
    (anchorNonnegative : 0 ≤ anchor) (beforePoint : anchor < point) (beforeTerminal : point < terminal)
    (withinLife : point - anchor < sourceOwnedWholeStateDuration nu ceiling)
    (paid : ∃ᶠ index in atTop, enstrophy ledger (receipt.core.subsequence index) anchor + 1 ≤ ceiling) :
    Nonempty {span : ControlSpan receipt terminal // span.first = anchor ∧ point < span.last} := by
  obtain ⟨extraction, strict, extracted⟩ := extraction_of_frequently_atTop paid
  let duration := min (sourceOwnedWholeStateDuration nu ceiling) ((point + terminal) / 2 - anchor)
  have pastPoint : point - anchor < duration := by
    apply lt_min withinLife
    linarith
  have positive : 0 < duration := (sub_pos.mpr beforePoint).trans pastPoint
  have endsBefore : anchor + duration < terminal := by
    have right : duration ≤ (point + terminal) / 2 - anchor := min_le_right _ _
    linarith
  let span : ControlSpan receipt terminal := {
    first := anchor
    last := anchor + duration
    first_nonnegative := anchorNonnegative
    ordered := by linarith
    last_lt := endsBefore
    terminal_le_one := terminalLe
    ceiling := ceiling
    activity := localActivityAllowance nu ceiling duration
    extraction := extraction
    extraction_strict := strict
    paid := Eventually.of_forall (fun index =>
      endpoint_local_control ledger (receipt.core.subsequence (extraction index)) anchor ceiling duration
        anchorNonnegative positive.le (endsBefore.le.trans terminalLe) (extracted index) (min_le_left _ _)) }
  exact ⟨⟨span, rfl, by change point < anchor + duration; linarith⟩⟩

theorem regular_of_frequent_source_bound
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal point anchor ceiling : ℝ) (terminalLe : terminal ≤ 1)
    (anchorNonnegative : 0 ≤ anchor) (beforePoint : anchor < point) (beforeTerminal : point < terminal)
    (withinLife : point - anchor < sourceOwnedWholeStateDuration nu ceiling)
    (paid : ∃ᶠ index in atTop, enstrophy ledger (receipt.core.subsequence index) anchor + 1 ≤ ceiling) :
    point ∈ regularSet receipt terminal := by
  obtain ⟨⟨span, same, past⟩⟩ := controlSpan_through_of_frequent_source_bound receipt terminal point anchor ceiling
    terminalLe anchorNonnegative beforePoint beforeTerminal withinLife paid
  apply mem_iUnion.mpr
  exact ⟨span, by rw [same]; exact ⟨beforePoint, past⟩⟩

theorem uncovered_eventually_large_source_enstrophy
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal point anchor ceiling : ℝ) (terminalLe : terminal ≤ 1)
    (anchorNonnegative : 0 ≤ anchor) (beforePoint : anchor < point) (beforeTerminal : point < terminal)
    (withinLife : point - anchor < sourceOwnedWholeStateDuration nu ceiling)
    (uncovered : point ∉ regularSet receipt terminal) :
    ∀ᶠ index in atTop, ceiling < enstrophy ledger (receipt.core.subsequence index) anchor + 1 := by
  have failure : ¬ ∃ᶠ index in atTop, enstrophy ledger (receipt.core.subsequence index) anchor + 1 ≤ ceiling := by
    intro paid
    exact uncovered (regular_of_frequent_source_bound receipt terminal point anchor ceiling terminalLe
      anchorNonnegative beforePoint beforeTerminal withinLife paid)
  simpa only [not_le] using not_frequently.mp failure

def approachTime (point prior ceiling : ℝ) : ℝ :=
  point - min ((point - prior) / 2) (sourceOwnedWholeStateDuration nu ceiling / 2)

theorem approachTime_spec (point prior ceiling : ℝ) (earlier : prior < point) :
    prior < approachTime (nu := nu) point prior ceiling ∧
      approachTime (nu := nu) point prior ceiling < point ∧
      point - approachTime (nu := nu) point prior ceiling < sourceOwnedWholeStateDuration nu ceiling := by
  have left := min_le_left ((point - prior) / 2) (sourceOwnedWholeStateDuration nu ceiling / 2)
  have right := min_le_right ((point - prior) / 2) (sourceOwnedWholeStateDuration nu ceiling / 2)
  have positive : 0 < min ((point - prior) / 2) (sourceOwnedWholeStateDuration nu ceiling / 2) :=
    lt_min (half_pos (sub_pos.mpr earlier)) (half_pos (sourceOwnedWholeStateDuration_pos nu ceiling))
  unfold approachTime
  constructor
  · linarith
  constructor
  · linarith
  · linarith [sourceOwnedWholeStateDuration_pos nu ceiling]

theorem finite_initial_band
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (point : ℝ) (positive : 0 < point) (pointLe : point ≤ 1) :
    ∃ anchor ∈ Ioo (0 : ℝ) point, ∃ budget : ℝ, ∃ extraction : ℕ → ℕ,
      StrictMono extraction ∧ ∀ᶠ index in atTop,
        enstrophy ledger (receipt.core.subsequence (extraction index)) anchor ≤ budget := by
  let left := point / 4
  let right := point / 2
  have leftNonnegative : 0 ≤ left := by dsimp [left]; positivity
  have ordered : left < right := by dsimp [left, right]; linarith
  have rightLt : right < 1 := by dsimp [right]; linarith
  obtain ⟨center, centerInside, extraction, strict, account⟩ :=
    common_source_control_window ledger receipt.core left right leftNonnegative ordered rightLt
  let duration := bandDuration ledger left right
  have durationPositive : 0 < duration := bandDuration_pos ledger left right ordered rightLt
  have width : duration ≤ right - left := bandDuration_le_width ledger left right
  refine ⟨center + duration / 2, ?_, bandCeiling ledger left right, extraction, strict, ?_⟩
  · dsimp [left, right] at centerInside width
    constructor <;> linarith [centerInside.1, centerInside.2]
  · filter_upwards [account] with index source
    exact (source.1 (center + duration / 2) ⟨by linarith, by linarith⟩).2.2

def netEnstrophyWork (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) (first last : ℝ) : ℝ :=
  ∫ time in first..last, finiteStateVorticityNonlinearWork (wholeRestartModes radius)
    ((ledger.family.stage radius).trajectory time) - nu.coeff * (2 * Real.pi) ^ 2 *
      finiteStateVorticityEnstrophyMass (wholeRestartModes radius) ((ledger.family.stage radius).trajectory time)

theorem netEnstrophyWork_eq_actual_increment
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) (first last : ℝ) (firstNonnegative : 0 ≤ first) (ordered : first ≤ last) (lastLe : last ≤ 1) :
    netEnstrophyWork ledger radius first last =
      (enstrophy ledger radius last - enstrophy ledger radius first) / 2 := by
  have actual := finiteStateVorticityHalfEnstrophy_integral_nonlinearWork (wholeRestartModes radius) nu.coeff
    (ledger.family.stage radius).trajectory first last ordered
    (fun time inside => ((ledger.family.stage radius).physical time
      ⟨firstNonnegative.trans inside.1, inside.2.trans lastLe⟩).1)
  unfold netEnstrophyWork
  rw [actual]
  unfold finiteStateVorticityHalfEnstrophy enstrophy
  ring

theorem uncovered_generates_actual_work_escape
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal point : ℝ) (terminalLe : terminal ≤ 1) (pointInside : point ∈ Ioo (0 : ℝ) terminal)
    (uncovered : point ∉ regularSet receipt terminal) :
    ∃ anchor ∈ Ioo (0 : ℝ) point, ∃ initialBudget : ℝ, ∃ extraction : ℕ → ℕ, StrictMono extraction ∧
      ∀ requested : ℝ, ∃ sample ∈ Ioo anchor point,
        ∀ᶠ index in atTop,
          enstrophy ledger (receipt.core.subsequence (extraction index)) anchor ≤ initialBudget ∧
          requested < netEnstrophyWork ledger (receipt.core.subsequence (extraction index)) anchor sample := by
  obtain ⟨anchor, anchorInside, initialBudget, extraction, strict, initial⟩ :=
    finite_initial_band receipt point pointInside.1 (pointInside.2.le.trans terminalLe)
  refine ⟨anchor, anchorInside, initialBudget, extraction, strict, ?_⟩
  intro requested
  let ceiling := 2 * requested + initialBudget + 1
  let sample := approachTime (nu := nu) point anchor ceiling
  have location := approachTime_spec (nu := nu) point anchor ceiling anchorInside.2
  have high := uncovered_eventually_large_source_enstrophy receipt terminal point sample ceiling terminalLe
    (anchorInside.1.le.trans location.1.le) location.2.1 pointInside.2 location.2.2 uncovered
  refine ⟨sample, ⟨location.1, location.2.1⟩, ?_⟩
  filter_upwards [initial, strict.tendsto_atTop high] with index low high
  refine ⟨low, ?_⟩
  rw [netEnstrophyWork_eq_actual_increment ledger _ anchor sample anchorInside.1.le location.1.le
    (location.2.1.le.trans (pointInside.2.le.trans terminalLe))]
  dsimp only [ceiling] at high
  change 2 * requested + initialBudget + 1 <
    enstrophy ledger (receipt.core.subsequence (extraction index)) sample + 1 at high
  linarith

def finiteObservationAllowance
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector) : ℝ :=
  (∑ wave ∈ observed, integerWaveViscousMultiplier wave) * ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2

theorem source_vorticity_row_bound
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) (time : Icc (0 : ℝ) 1) (wave : IntegerWavevector) :
    complexCoordinateAmplitudeSq ((ledger.family.stage radius).trajectory time.1 wave) ≤
      integerWaveViscousMultiplier wave * ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
  let stage := ledger.family.stage radius
  have lambdaNonnegative : 0 ≤ integerWaveViscousMultiplier wave := mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg _)
  by_cases member : wave ∈ wholeRestartModes radius
  · have nonzero : wave ≠ 0 := fun same => zero_not_mem_puncturedIntegerWaveFrequencyCube radius (same ▸ member)
    have mass := Finset.single_le_sum (s := wholeRestartModes radius)
      (f := fun frequency => complexCoordinateVectorNormSq (finiteStateVelocityCoefficient (stage.trajectory time.1) frequency))
      (fun _ _ => complexCoordinateVectorNormSq_nonneg _) member
    have energy := ledger.kinetic_energy_le radius time
    unfold finiteStateVorticityKineticEnergy at energy
    have velocityBound : complexCoordinateVectorNormSq (finiteStateVelocityCoefficient (stage.trajectory time.1) wave) ≤
        ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by linarith
    have paid := mul_le_mul_of_nonneg_left velocityBound lambdaNonnegative
    rw [finiteStateVelocityCoefficient, biotSavartVelocityCoefficient_normSq_of_transverse wave _ nonzero
      ((stage.physical time.1 time.2).2.2.1 wave)] at paid
    have lambdaNe : integerWaveViscousMultiplier wave ≠ 0 := mul_ne_zero (pow_ne_zero _ (by positivity))
      (integerWaveNormSq_ne_zero nonzero)
    change integerWaveViscousMultiplier wave *
      (complexCoordinateVectorNormSq (stage.trajectory time.1 wave) / integerWaveViscousMultiplier wave) ≤ _ at paid
    rw [mul_div_cancel₀ _ lambdaNe] at paid
    simpa only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using paid
  · rw [(stage.physical time.1 time.2).2.1 wave member]
    simpa only [complexCoordinateAmplitudeSq, Pi.zero_apply, Complex.normSq_zero, Finset.sum_const_zero] using
      mul_nonneg lambdaNonnegative (sq_nonneg ‖ledger.family.endpointReceipt.velocityEndpoint‖)

theorem finiteObservation_enstrophy_bound
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) (time : Icc (0 : ℝ) 1) (observed : Finset IntegerWavevector) :
    (∑ wave ∈ observed, complexCoordinateAmplitudeSq ((ledger.family.stage radius).trajectory time.1 wave)) ≤
      finiteObservationAllowance ledger observed := by
  unfold finiteObservationAllowance
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun wave _ => source_vorticity_row_bound ledger radius time wave)

def highFrequencyEnstrophy
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) (observed : Finset IntegerWavevector) (time : ℝ) : ℝ :=
  ∑ wave ∈ wholeRestartModes radius \ observed,
    complexCoordinateAmplitudeSq ((ledger.family.stage radius).trajectory time wave)

theorem enstrophy_le_observed_add_high
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) (time : Icc (0 : ℝ) 1) (observed : Finset IntegerWavevector) :
    enstrophy ledger radius time.1 ≤ finiteObservationAllowance ledger observed + highFrequencyEnstrophy ledger radius observed time.1 := by
  have split := Finset.sum_inter_add_sum_sdiff (wholeRestartModes radius) observed
    (fun wave => complexCoordinateAmplitudeSq ((ledger.family.stage radius).trajectory time.1 wave))
  have low : (∑ wave ∈ wholeRestartModes radius ∩ observed,
      complexCoordinateAmplitudeSq ((ledger.family.stage radius).trajectory time.1 wave)) ≤
      finiteObservationAllowance ledger observed :=
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun _ _ _ => complexCoordinateAmplitudeSq_nonneg _)).trans
      (finiteObservation_enstrophy_bound ledger radius time observed)
  change (∑ wave ∈ wholeRestartModes radius, complexCoordinateAmplitudeSq ((ledger.family.stage radius).trajectory time.1 wave)) ≤ _
  rw [← split]
  exact add_le_add low le_rfl

theorem uncovered_generates_highFrequency_action
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal point : ℝ) (terminalLe : terminal ≤ 1) (pointInside : point ∈ Ioo (0 : ℝ) terminal)
    (uncovered : point ∉ regularSet receipt terminal) :
    ∃ anchor ∈ Ioo (0 : ℝ) point, ∃ initialBudget : ℝ, ∃ extraction : ℕ → ℕ, StrictMono extraction ∧
      ∀ (observed : Finset IntegerWavevector) (requested epsilon : ℝ), 0 < epsilon →
        ∃ sample ∈ Ioo (max anchor (point - epsilon)) point,
        ∀ᶠ index in atTop,
          enstrophy ledger (receipt.core.subsequence (extraction index)) anchor ≤ initialBudget ∧
          requested < highFrequencyEnstrophy ledger (receipt.core.subsequence (extraction index)) observed sample ∧
          requested < netEnstrophyWork ledger (receipt.core.subsequence (extraction index)) anchor sample := by
  obtain ⟨anchor, anchorInside, initialBudget, extraction, strict, initial⟩ :=
    finite_initial_band receipt point pointInside.1 (pointInside.2.le.trans terminalLe)
  refine ⟨anchor, anchorInside, initialBudget, extraction, strict, ?_⟩
  intro observed requested epsilon epsilonPositive
  let ceiling := max (requested + finiteObservationAllowance ledger observed)
    (2 * requested + initialBudget) + 1
  let prior := max anchor (point - epsilon)
  have priorBefore : prior < point := max_lt anchorInside.2 (by linarith)
  let sample := approachTime (nu := nu) point prior ceiling
  have location := approachTime_spec (nu := nu) point prior ceiling priorBefore
  have afterAnchor : anchor < sample := (le_max_left _ _).trans_lt location.1
  have high := uncovered_eventually_large_source_enstrophy receipt terminal point sample ceiling terminalLe
    (anchorInside.1.le.trans afterAnchor.le) location.2.1 pointInside.2 location.2.2 uncovered
  refine ⟨sample, ⟨location.1, location.2.1⟩, ?_⟩
  filter_upwards [initial, strict.tendsto_atTop high] with index low high
  change ceiling < enstrophy ledger (receipt.core.subsequence (extraction index)) sample + 1 at high
  have realHigh : max (requested + finiteObservationAllowance ledger observed) (2 * requested + initialBudget) <
      enstrophy ledger (receipt.core.subsequence (extraction index)) sample := by dsimp [ceiling] at high; linarith
  have waveHigh := (le_max_left (requested + finiteObservationAllowance ledger observed) (2 * requested + initialBudget)).trans_lt realHigh
  have workHigh := (le_max_right (requested + finiteObservationAllowance ledger observed) (2 * requested + initialBudget)).trans_lt realHigh
  have sampleInside : sample ∈ Icc (0 : ℝ) 1 :=
    ⟨anchorInside.1.le.trans afterAnchor.le, location.2.1.le.trans (pointInside.2.le.trans terminalLe)⟩
  refine ⟨low, ?_, ?_⟩
  · have actual := enstrophy_le_observed_add_high ledger (receipt.core.subsequence (extraction index)) ⟨sample, sampleInside⟩ observed
    linarith
  · rw [netEnstrophyWork_eq_actual_increment ledger _ anchor sample anchorInside.1.le afterAnchor.le sampleInside.2]
    linarith

theorem regular_of_native_work_account
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal point : ℝ) (span : ControlSpan receipt terminal) (afterSpan : span.last < point)
    (beforeTerminal : point < terminal) (workBudget : ℝ)
    (paid : ∀ sample ∈ Ioo span.last point, ∃ᶠ index in atTop,
      netEnstrophyWork ledger (receipt.core.subsequence (span.extraction index)) span.last sample ≤ workBudget) :
    point ∈ regularSet receipt terminal := by
  let ceiling := 2 * workBudget + span.ceiling + 1
  let sample := approachTime (nu := nu) point span.last ceiling
  have location := approachTime_spec (nu := nu) point span.last ceiling afterSpan
  have sampleNonnegative : 0 ≤ sample := (span.first_nonnegative.trans span.ordered.le).trans location.1.le
  have sampleLe : sample ≤ 1 := location.2.1.le.trans (beforeTerminal.le.trans span.terminal_le_one)
  have work := paid sample ⟨location.1, location.2.1⟩
  have selected : ∃ᶠ index in atTop,
      enstrophy ledger (receipt.core.subsequence (span.extraction index)) sample + 1 ≤ ceiling := by
    have both := work.and_eventually span.paid
    apply both.mono
    intro index evidence
    have initial := evidence.2.1 span.last ⟨span.ordered.le, le_rfl⟩
    have action := evidence.1
    rw [netEnstrophyWork_eq_actual_increment ledger _ span.last sample
      (span.first_nonnegative.trans span.ordered.le) location.1.le sampleLe] at action
    change enstrophy ledger (receipt.core.subsequence (span.extraction index)) span.last ≤ span.ceiling at initial
    dsimp [ceiling]
    linarith
  exact regular_of_frequent_source_bound receipt terminal point sample ceiling span.terminal_le_one
    sampleNonnegative location.2.1 beforeTerminal location.2.2
    (span.extraction_strict.tendsto_atTop.frequently selected)

structure SourceActionEscape
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (point : ℝ) where
  anchor : ℝ
  anchor_inside : anchor ∈ Ioo (0 : ℝ) point
  initialBudget : ℝ
  extraction : ℕ → ℕ
  extraction_strict : StrictMono extraction
  sample : ℕ → ℝ
  index : ℕ → ℕ
  index_ge : ∀ order, order ≤ index order
  sample_inside : ∀ order : ℕ, sample order ∈ Ioo (max anchor (point - 1 / (order + 1 : ℝ))) point
  initial_bound : ∀ order, enstrophy ledger (receipt.core.subsequence (extraction (index order))) anchor ≤ initialBudget
  high_frequency : ∀ order : ℕ, (order : ℝ) <
    highFrequencyEnstrophy ledger (receipt.core.subsequence (extraction (index order))) (wholeRestartModes order) (sample order)
  action_work : ∀ order : ℕ, (order : ℝ) <
    netEnstrophyWork ledger (receipt.core.subsequence (extraction (index order))) anchor (sample order)

def sourceActionEscape
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal point : ℝ) (terminalLe : terminal ≤ 1) (pointInside : point ∈ Ioo (0 : ℝ) terminal)
    (uncovered : point ∉ regularSet receipt terminal) : SourceActionEscape receipt point := Classical.choice (by
  obtain ⟨anchor, anchorInside, initialBudget, extraction, strict, source⟩ :=
    uncovered_generates_highFrequency_action receipt terminal point terminalLe pointInside uncovered
  have selected (order : ℕ) : ∃ sample ∈ Ioo (max anchor (point - 1 / (order + 1 : ℝ))) point,
      ∃ index : ℕ, order ≤ index ∧
        enstrophy ledger (receipt.core.subsequence (extraction index)) anchor ≤ initialBudget ∧
        (order : ℝ) < highFrequencyEnstrophy ledger (receipt.core.subsequence (extraction index)) (wholeRestartModes order) sample ∧
        (order : ℝ) < netEnstrophyWork ledger (receipt.core.subsequence (extraction index)) anchor sample := by
    obtain ⟨sample, inside, generated⟩ := source (wholeRestartModes order) order (1 / (order + 1 : ℝ)) (by positivity)
    have both := generated.and (eventually_ge_atTop order)
    obtain ⟨index, evidence⟩ := both.exists
    exact ⟨sample, inside, index, evidence.2, evidence.1⟩
  choose sample inside index indexGe initial tail work using selected
  exact ⟨{
    anchor := anchor
    anchor_inside := anchorInside
    initialBudget := initialBudget
    extraction := extraction
    extraction_strict := strict
    sample := sample
    index := index
    index_ge := indexGe
    sample_inside := inside
    initial_bound := initial
    high_frequency := tail
    action_work := work }⟩)

theorem SourceActionEscape.sample_tendsto
    {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
    (escape : SourceActionEscape receipt point) : Tendsto escape.sample atTop (𝓝 point) := by
  have reciprocal : Tendsto (fun order : ℕ => 1 / (order + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div, Nat.cast_add, Nat.cast_one] using tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun order : ℕ => (order : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1))
  have difference := squeeze_zero' (f := fun order => point - escape.sample order)
    (Eventually.of_forall fun order => (sub_pos.mpr (escape.sample_inside order).2).le)
    (Eventually.of_forall fun order => by
      have lower := (le_max_right escape.anchor (point - 1 / (order + 1 : ℝ))).trans_lt (escape.sample_inside order).1
      linarith) reciprocal
  convert! difference.const_sub point using 1 <;> simp

theorem SourceActionEscape.radius_tendsto
    {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
    (escape : SourceActionEscape receipt point) :
    Tendsto (fun order => receipt.core.subsequence (escape.extraction (escape.index order))) atTop atTop := by
  apply receipt.core.subsequence_strictMono.tendsto_atTop.comp
  apply escape.extraction_strict.tendsto_atTop.comp
  exact tendsto_atTop_mono escape.index_ge tendsto_id

theorem SourceActionEscape.highFrequency_tendsto
    {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
    (escape : SourceActionEscape receipt point) :
    Tendsto (fun order => highFrequencyEnstrophy ledger
      (receipt.core.subsequence (escape.extraction (escape.index order))) (wholeRestartModes order) (escape.sample order)) atTop atTop :=
  tendsto_atTop_mono (fun order => (escape.high_frequency order).le) tendsto_natCast_atTop_atTop

theorem SourceActionEscape.actionWork_tendsto
    {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
    (escape : SourceActionEscape receipt point) :
    Tendsto (fun order => netEnstrophyWork ledger
      (receipt.core.subsequence (escape.extraction (escape.index order))) escape.anchor (escape.sample order)) atTop atTop :=
  tendsto_atTop_mono (fun order => (escape.action_work order).le) tendsto_natCast_atTop_atTop

theorem SourceActionEscape.actual_action
    {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
    (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (order : ℕ) :
    let radius := receipt.core.subsequence (escape.extraction (escape.index order))
    HasDerivAt (ledger.family.stage radius).trajectory
      (finiteStateVorticityGenerator (wholeRestartModes radius) nu.coeff
        ((ledger.family.stage radius).trajectory (escape.sample order))) (escape.sample order) ∧
      netEnstrophyWork ledger radius escape.anchor (escape.sample order) =
        (enstrophy ledger radius (escape.sample order) - enstrophy ledger radius escape.anchor) / 2 := by
  have after : escape.anchor < escape.sample order :=
    (le_max_left _ _).trans_lt (escape.sample_inside order).1
  have inside : escape.sample order ∈ Icc (0 : ℝ) 1 :=
    ⟨escape.anchor_inside.1.le.trans after.le, (escape.sample_inside order).2.le.trans pointLe⟩
  exact ⟨((ledger.family.stage _).physical _ inside).1,
    netEnstrophyWork_eq_actual_increment ledger _ _ _ escape.anchor_inside.1.le after.le inside.2⟩

def sourceUncoveredAction (initial : GeneratedWholeRestartCurrent nu)
    (point : ℝ)
    (inside : point ∈ Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (uncovered : point ∉ regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) :
    SourceActionEscape (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) point :=
  sourceActionEscape (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 point
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2 inside uncovered

theorem native_work_account_generates_cover
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal point : ℝ) (span : ControlSpan receipt terminal) (afterSpan : span.last < point)
    (beforeTerminal : point < terminal) (workBudget : ℝ)
    (paid : ∀ sample ∈ Ioo span.last point, ∃ᶠ index in atTop,
      netEnstrophyWork ledger (receipt.core.subsequence (span.extraction index)) span.last sample ≤ workBudget) :
    Nonempty {next : ControlSpan receipt terminal // next.first < point ∧ point < next.last} := by
  have covered := regular_of_native_work_account receipt terminal point span afterSpan beforeTerminal workBudget paid
  obtain ⟨next, inside⟩ := mem_iUnion.mp covered
  exact ⟨⟨next, inside⟩⟩

end
end SaturationMonoid.NavierStokes.NativeRecoveryCoverage
