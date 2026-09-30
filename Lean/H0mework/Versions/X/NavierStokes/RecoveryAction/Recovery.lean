import H0mework.Versions.X.NavierStokes.SourceAction.EndpointEnergy
import H0mework.NavierStokes.MacroRuntime.GlobalAbsoluteVelocity
import H0mework.Versions.X.NavierStokes.SourceAction.EndpointGain
import H0mework.Versions.X.NavierStokes.SourceAction.Flux
import H0mework.NavierStokes.InitialData.SourceOwnedLocalCompactnessBudget
import Mathlib.Topology.Sequences

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryControlProducer

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
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointLerayHopfReceipt
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open ThreeDimensionalVorticityCoefficientSourceOwnedLocalCompactnessBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalTimeConsumer
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeFullOrderEnergy NativeFullOrderAction NativeFullOrderLimit NativeFullOrderFlux NativeFullOrderEvolution
open NativeEndpointPositiveTime

noncomputable section

variable {nu : Viscosity}

def kineticAllowance (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) : ℝ :=
  ((1 / 2 : ℝ) * ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2) / nu.coeff

theorem kineticAllowance_nonneg (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) :
    0 ≤ kineticAllowance ledger := by
  unfold kineticAllowance
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) nu.coeff_pos.le

theorem enstrophy_integral_le (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) {left right : ℝ} (leftNonnegative : 0 ≤ left) (ordered : left ≤ right) (rightLe : right ≤ 1) :
    (∫ time in left..right, finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius)
      ((ledger.family.stage radius).trajectory time)) ≤ kineticAllowance ledger := by
  have integrable := ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger.GeneratedWholeRestartVelocityEndpointGalerkinStage.vorticityMass_intervalIntegrable
    (ledger.family.stage radius) ⟨1, by norm_num⟩
  have comparison := intervalIntegral.integral_mono_interval leftNonnegative ordered rightLe
    (Filter.Eventually.of_forall fun time => by
      unfold finiteStateVorticityMass
      exact Finset.sum_nonneg fun _ _ => complexCoordinateVectorNormSq_nonneg _) integrable
  have source : (∫ time in 0..1, finiteStateVorticityMass (wholeRestartModes radius)
      ((ledger.family.stage radius).trajectory time)) ≤ kineticAllowance ledger := by
    apply (le_div_iff₀ nu.coeff_pos).mpr
    simpa only [mul_comm] using ledger.viscous_integral_le radius ⟨1, by norm_num⟩
  apply le_trans _ source
  simpa only [finiteStateVorticityMass, finiteStateVorticityCoefficientEnstrophy,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using comparison

def bandCeiling (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (left right : ℝ) : ℝ := kineticAllowance ledger / (right - left) + 1

theorem exists_low_enstrophy_time
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) {left right : ℝ} (leftNonnegative : 0 ≤ left) (ordered : left < right) (rightLe : right ≤ 1) :
    ∃ time ∈ Icc left right, finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius)
      ((ledger.family.stage radius).trajectory time) + 1 ≤ bandCeiling ledger left right := by
  have continuousMass : ContinuousOn (fun time => finiteStateVorticityCoefficientEnstrophy
      (wholeRestartModes radius) ((ledger.family.stage radius).trajectory time)) (Icc left right) := by
    intro time inside
    have physical := ((ledger.family.stage radius).physical time
      ⟨leftNonnegative.trans inside.1, inside.2.trans rightLe⟩).1
    have continuous := finiteStateVorticityMass_continuousAt_of_hasDerivAt
      (wholeRestartModes radius) _ time _ physical
    simpa only [finiteStateVorticityMass, finiteStateVorticityCoefficientEnstrophy,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using continuous.continuousWithinAt
  obtain ⟨time, inside, average⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (μ := volume) (f := fun time => finiteStateVorticityCoefficientEnstrophy
      (wholeRestartModes radius) ((ledger.family.stage radius).trajectory time))
    (g := fun _ => (1 : ℝ)) (a := left) (b := right)
    (by simpa only [uIcc_of_le ordered.le] using continuousMass) intervalIntegrable_const
    (fun _ _ => zero_le_one)
  refine ⟨time, by simpa only [uIcc_of_le ordered.le] using inside, ?_⟩
  have point : finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius)
      ((ledger.family.stage radius).trajectory time) ≤ kineticAllowance ledger / (right - left) := by
    apply (le_div_iff₀ (sub_pos.mpr ordered)).mpr
    simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul] at average
    exact average.symm.le.trans (enstrophy_integral_le ledger radius leftNonnegative ordered.le rightLe)
  unfold bandCeiling
  linarith

def bandStart (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (left right : ℝ) (leftNonnegative : 0 ≤ left) (ordered : left < right) (rightLe : right ≤ 1)
    (radius : ℕ) : ℝ := Classical.choose
  (exists_low_enstrophy_time ledger radius leftNonnegative ordered rightLe)

theorem bandStart_spec (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (left right : ℝ) (leftNonnegative : 0 ≤ left) (ordered : left < right) (rightLe : right ≤ 1)
    (radius : ℕ) :
    bandStart ledger left right leftNonnegative ordered rightLe radius ∈ Icc left right ∧
      finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius)
        ((ledger.family.stage radius).trajectory (bandStart ledger left right leftNonnegative ordered rightLe radius)) + 1 ≤
          bandCeiling ledger left right :=
  Classical.choose_spec (exists_low_enstrophy_time ledger radius leftNonnegative ordered rightLe)

def bandDuration (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (left right : ℝ) : ℝ :=
  min (sourceOwnedWholeStateDuration nu (bandCeiling ledger left right)) (min (1 - right) (right - left))

theorem bandDuration_pos (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (left right : ℝ) (ordered : left < right) (rightLt : right < 1) : 0 < bandDuration ledger left right :=
  lt_min (sourceOwnedWholeStateDuration_pos nu _) (lt_min (sub_pos.mpr rightLt) (sub_pos.mpr ordered))

theorem bandDuration_le_remaining (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (left right : ℝ) : bandDuration ledger left right ≤ 1 - right :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem bandDuration_le_width (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (left right : ℝ) : bandDuration ledger left right ≤ right - left :=
  (min_le_right _ _).trans (min_le_right _ _)

def bandGradientAllowance (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (left right : ℝ) : ℝ :=
  (bandCeiling ledger left right / 2 + sourceOwnedLocalQuadraticCoefficient nu (bandCeiling ledger left right) *
    bandCeiling ledger left right ^ 2 * bandDuration ledger left right) / ((3 * nu.coeff / 8) * (2 * Real.pi) ^ 2)

def bandVelocityAllowance (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (left right : ℝ) : ℝ :=
  2 * sourceOwnedLocalCoreVelocityCoefficient nu (bandCeiling ledger left right) *
    bandCeiling ledger left right * bandDuration ledger left right +
    2 * biotSavartSerrinConstant * sourceOwnedKernelTailTolerance nu (bandCeiling ledger left right) *
      bandGradientAllowance ledger left right

theorem shifted_source_control (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (left right : ℝ) (leftNonnegative : 0 ≤ left) (ordered : left < right) (rightLt : right < 1)
    (radius : ℕ) :
    let start := bandStart ledger left right leftNonnegative ordered rightLt.le radius
    let path := fun time => (ledger.family.stage radius).trajectory (start + time)
    (∀ time ∈ Icc (0 : ℝ) (bandDuration ledger left right),
      finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius) (path time) ≤ bandCeiling ledger left right) ∧
      (∫ time in 0..bandDuration ledger left right,
        finiteStateVelocityMajorant (wholeRestartModes radius) (path time) ^ 2) ≤ bandVelocityAllowance ledger left right := by
  dsimp only
  let start := bandStart ledger left right leftNonnegative ordered rightLt.le radius
  let path := fun time => (ledger.family.stage radius).trajectory (start + time)
  have sourceTime := bandStart_spec ledger left right leftNonnegative ordered rightLt.le radius
  have actualTime (time : ℝ) (inside : time ∈ Icc (0 : ℝ) (bandDuration ledger left right)) :
      start + time ∈ Icc (0 : ℝ) 1 := by
    have horizon := bandDuration_le_remaining ledger left right
    dsimp only [start]
    constructor <;> linarith [sourceTime.1.1, sourceTime.1.2, inside.1, inside.2]
  have budget := finiteStateVorticity_sourceOwnedWholeStateCompactnessBudget_on_Icc
    (wholeRestartModes radius) (fun _ member => puncturedIntegerWaveFrequencyCube_waveNeg_mem radius member)
    nu (bandCeiling ledger left right) path (bandDuration ledger left right)
    (bandDuration_pos ledger left right ordered rightLt).le
    (by simpa only [path, add_zero] using sourceTime.2)
    (min_le_left _ _)
    (fun time inside => by
      exact HasDerivAt.comp_const_add start time
        ((ledger.family.stage radius).physical (start + time) (actualTime time inside)).1)
    (fun time inside => ((ledger.family.stage radius).physical (start + time) (actualTime time inside)).2.2.2)
    (fun time inside wave _ => ((ledger.family.stage radius).physical (start + time) (actualTime time inside)).2.2.1 wave)
  refine ⟨budget.1, budget.2.2.1.trans ?_⟩
  have gradient : (∫ time in 0..bandDuration ledger left right,
      finiteStateVorticityEnstrophyMass (wholeRestartModes radius) (path time)) ≤ bandGradientAllowance ledger left right := by
    apply (le_div_iff₀ (wholeRestartGradientCoefficient_pos nu)).mpr
    rw [mul_comm]
    apply budget.2.1.trans
    dsimp only [finiteStateVorticityHalfEnstrophy]
    have initial : finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius) (path 0) + 1 ≤
        bandCeiling ledger left right := by simpa only [path, add_zero] using sourceTime.2
    linarith
  unfold bandVelocityAllowance
  gcongr
  exact mul_nonneg (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
    (sourceOwnedKernelTailTolerance_pos nu _).le

theorem bandVelocityAllowance_nonneg
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (left right : ℝ) (leftNonnegative : 0 ≤ left) (ordered : left < right) (rightLt : right < 1) :
    0 ≤ bandVelocityAllowance ledger left right := by
  have paid := (shifted_source_control ledger left right leftNonnegative ordered rightLt 0).2
  exact (intervalIntegral.integral_nonneg (bandDuration_pos ledger left right ordered rightLt).le
    (fun _ _ => sq_nonneg _)).trans paid

theorem common_source_control_window
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (core : GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (left right : ℝ) (leftNonnegative : 0 ≤ left) (ordered : left < right) (rightLt : right < 1) :
    ∃ center ∈ Icc left right, ∃ extraction : ℕ → ℕ, StrictMono extraction ∧
      ∀ᶠ index in atTop,
        let radius := core.subsequence (extraction index)
        let start := bandStart ledger left right leftNonnegative ordered rightLt.le radius
        let duration := bandDuration ledger left right
        (∀ time ∈ Icc (center + duration / 3) (center + 2 * duration / 3),
          duration / 6 ≤ time - start ∧ time - start ≤ duration ∧
            finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius)
              ((ledger.family.stage radius).trajectory time) ≤ bandCeiling ledger left right) ∧
        (∫ time in (center + duration / 3)..(center + 2 * duration / 3),
          finiteStateVelocityMajorant (wholeRestartModes radius)
            ((ledger.family.stage radius).trajectory time) ^ 2) ≤ bandVelocityAllowance ledger left right := by
  let duration := bandDuration ledger left right
  have durationPositive : 0 < duration := bandDuration_pos ledger left right ordered rightLt
  obtain ⟨center, centerInside, extraction, extractionStrict, converges⟩ :=
    isCompact_Icc.tendsto_subseq (fun index => (bandStart_spec ledger left right leftNonnegative ordered rightLt.le
      (core.subsequence index)).1)
  refine ⟨center, centerInside, extraction, extractionStrict, ?_⟩
  have near := converges (Ioo_mem_nhds (by linarith : center - duration / 6 < center)
    (by linarith : center < center + duration / 6))
  filter_upwards [near] with index nearStart
  let radius := core.subsequence (extraction index)
  let selected := bandStart ledger left right leftNonnegative ordered rightLt.le radius
  let path := fun time => (ledger.family.stage radius).trajectory (selected + time)
  have selectedNear : selected ∈ Ioo (center - duration / 6) (center + duration / 6) := nearStart
  have selectedSpec := bandStart_spec ledger left right leftNonnegative ordered rightLt.le radius
  have account := shifted_source_control ledger left right leftNonnegative ordered rightLt radius
  have localTime (time : ℝ) (inside : time ∈ Icc (center + duration / 3) (center + 2 * duration / 3)) :
      duration / 6 ≤ time - selected ∧ time - selected ≤ duration := by
    constructor <;> linarith [selectedNear.1, selectedNear.2, inside.1, inside.2]
  constructor
  · intro time inside
    have location := localTime time inside
    refine ⟨location.1, location.2, ?_⟩
    have bounded := account.1 (time - selected) ⟨by linarith, location.2⟩
    have same : selected + (time - selected) = time := by ring
    change finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius)
      ((ledger.family.stage radius).trajectory (selected + (time - selected))) ≤ _ at bounded
    rwa [same] at bounded
  · have shiftedIntegrable : IntervalIntegrable
        (fun time => finiteStateVelocityMajorant (wholeRestartModes radius) (path time) ^ 2) volume 0 duration := by
      apply ContinuousOn.intervalIntegrable_of_Icc durationPositive.le
      intro time inside
      have actualInside : selected + time ∈ Icc (0 : ℝ) 1 := by
        have durationLe : duration ≤ 1 - right := bandDuration_le_remaining ledger left right
        constructor <;> linarith [selectedSpec.1.1, selectedSpec.1.2, inside.1, inside.2]
      have shifted := HasDerivAt.comp_const_add selected time
        ((ledger.family.stage radius).physical (selected + time) actualInside).1
      exact ((finiteStateVelocityMajorant_continuousAt_of_hasDerivAt (wholeRestartModes radius)
        path time _ shifted).pow 2).continuousWithinAt
    have first : 0 ≤ center + duration / 3 - selected := by linarith [selectedNear.2]
    have orderedLocal : center + duration / 3 - selected ≤ center + 2 * duration / 3 - selected := by linarith
    have last : center + 2 * duration / 3 - selected ≤ duration := by linarith [selectedNear.1]
    have payment := (intervalIntegral.integral_mono_interval first orderedLocal last
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) shiftedIntegrable).trans account.2
    have integralSame := intervalIntegral.integral_comp_add_left
      (fun time => finiteStateVelocityMajorant (wholeRestartModes radius)
        ((ledger.family.stage radius).trajectory time) ^ 2)
      (a := center + duration / 3 - selected) (b := center + 2 * duration / 3 - selected) selected
    simp only [add_sub_cancel] at integralSame
    change (∫ time in (center + duration / 3)..(center + 2 * duration / 3),
      finiteStateVelocityMajorant (wholeRestartModes radius) ((ledger.family.stage radius).trajectory time) ^ 2) ≤ _
    rw [← integralSame]
    exact payment

theorem endpoint_velocity_row_tendsto
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (core : GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1) (wave : IntegerWavevector) :
    Tendsto (fun index => finiteStateVelocityCoefficient
      ((ledger.family.stage (core.subsequence index)).trajectory time.1) wave) atTop
        (𝓝 (velocityEndpointWholeMildState core time wave)) := by
  have source := generatedVelocityEndpointGalerkinWholeState_tendsto_mildCoefficient core time wave
  apply source.congr'
  apply Filter.Eventually.of_forall
  intro index
  change generatedVelocityEndpointGalerkinWholeState ledger (core.subsequence index) time wave = _
  rw [generatedVelocityEndpointGalerkinWholeState_apply]
  by_cases inside : wave ∈ wholeRestartModes (core.subsequence index)
  · rw [if_pos inside]
  · rw [if_neg inside]
    simp [finiteStateVelocityCoefficient,
      ((ledger.family.stage (core.subsequence index)).physical time.1 time.2).2.1 wave inside]

theorem wholeMild_moment_of_eventual_stage_control
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (core : GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (extraction : ℕ → ℕ) (extractionStrict : StrictMono extraction)
    (order : ℕ) (bound : ℝ) (time : Icc (0 : ℝ) 1)
    (finiteControl : ∀ ceiling : ℝ, 0 ≤ ceiling → ∀ᶠ index in atTop,
      weightedVelocityEnergy (wholeRestartModes (core.subsequence (extraction index)))
        (wordWeight order ceiling)
        ((ledger.family.stage (core.subsequence (extraction index))).trajectory time.1) ≤ bound) :
    Summable (velocityMomentDensity order (velocityEndpointWholeMildState core time)) ∧
      (∑' wave, velocityMomentDensity order (velocityEndpointWholeMildState core time) wave) ≤ bound := by
  have nonnegative (wave : IntegerWavevector) :
      0 ≤ velocityMomentDensity order (velocityEndpointWholeMildState core time) wave :=
    mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _)
  have finiteBound (observed : Finset IntegerWavevector) :
      (∑ wave ∈ observed, velocityMomentDensity order (velocityEndpointWholeMildState core time) wave) ≤ bound := by
    have squareContinuous : Continuous complexCoordinateVectorNormSq := by
      unfold complexCoordinateVectorNormSq
      fun_prop
    have converges : Tendsto (fun index => weightedVelocityEnergy observed
        (wordWeight order (frequencyCeiling observed))
        ((ledger.family.stage (core.subsequence (extraction index))).trajectory time.1)) atTop
        (𝓝 (∑ wave ∈ observed, wordWeight order (frequencyCeiling observed) wave ^ 2 *
          complexCoordinateVectorNormSq (velocityEndpointWholeMildState core time wave))) := by
      unfold weightedVelocityEnergy
      apply tendsto_finsetSum
      intro wave _
      exact tendsto_const_nhds.mul ((squareContinuous.tendsto _).comp
        ((endpoint_velocity_row_tendsto ledger core time wave).comp extractionStrict.tendsto_atTop))
    have controlled : (∑ wave ∈ observed, wordWeight order (frequencyCeiling observed) wave ^ 2 *
        complexCoordinateVectorNormSq (velocityEndpointWholeMildState core time wave)) ≤ bound := by
      apply le_of_tendsto converges
      filter_upwards [finiteControl (frequencyCeiling observed) (frequencyCeiling_nonneg observed)] with index paid
      exact (weightedVelocityEnergy_le_of_support observed
        (wholeRestartModes (core.subsequence (extraction index))) (wordWeight order (frequencyCeiling observed))
        ((ledger.family.stage (core.subsequence (extraction index))).trajectory time.1)
        ((ledger.family.stage (core.subsequence (extraction index))).physical time.1 time.2).2.1).trans paid
    convert controlled using 1
    apply Finset.sum_congr rfl
    intro wave inside
    rw [wordWeight_full_on_modes observed order wave inside]
    rfl
  exact ⟨summable_of_sum_le nonnegative finiteBound, Real.tsum_le_of_sum_le nonnegative finiteBound⟩

theorem wholeMild_generated_control_window
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (core : GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (left right : ℝ) (leftNonnegative : 0 ≤ left) (ordered : left < right) (rightLt : right < 1) :
    ∃ center ∈ Icc left right, ∀ order : ℕ, ∀ time : Icc (0 : ℝ) 1,
      center + bandDuration ledger left right / 2 ≤ time.1 →
      time.1 ≤ center + 2 * bandDuration ledger left right / 3 →
      Summable (velocityMomentDensity order (velocityEndpointWholeMildState core time)) ∧
        (∑' wave, velocityMomentDensity order (velocityEndpointWholeMildState core time) wave) ≤
          endpointBudget ledger (bandVelocityAllowance ledger left right) order (bandDuration ledger left right / 6) := by
  obtain ⟨center, centerInside, extraction, extractionStrict, account⟩ :=
    common_source_control_window ledger core left right leftNonnegative ordered rightLt
  let duration := bandDuration ledger left right
  have durationPositive : 0 < duration := bandDuration_pos ledger left right ordered rightLt
  have durationLe : duration ≤ 1 - right := bandDuration_le_remaining ledger left right
  have firstNonnegative : 0 ≤ center + duration / 3 := by linarith [centerInside.1]
  have timeOrdered : center + duration / 3 ≤ center + 2 * duration / 3 := by linarith
  have lastLe : center + 2 * duration / 3 ≤ 1 := by linarith [centerInside.2]
  refine ⟨center, centerInside, ?_⟩
  intro order time afterStart beforeEnd
  apply wholeMild_moment_of_eventual_stage_control ledger core extraction extractionStrict order _ time
  intro ceiling ceilingNonnegative
  filter_upwards [account] with index paid
  exact endpoint_positive_time_energy_bound ledger (core.subsequence (extraction index))
    (center + duration / 3) (center + 2 * duration / 3) firstNonnegative timeOrdered lastLe
    (bandVelocityAllowance ledger left right) paid.2 order (duration / 6) (by linarith) (by linarith)
    ceiling ceilingNonnegative time.1 ⟨by change center + duration / 2 ≤ time.1 at afterStart; linarith, beforeEnd⟩

theorem wholeMild_controlled_subinterval
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (left right : ℝ) (leftNonnegative : 0 ≤ left) (ordered : left < right) (rightLe : right ≤ 1) :
    ∃ first last : ℝ, left < first ∧ first < last ∧ last < right ∧
      ∀ order : ℕ, ∃ bound : ℝ, ∀ time : Icc (0 : ℝ) 1,
        first ≤ time.1 → time.1 ≤ last →
        Summable (velocityMomentDensity order (receipt.wholePath time)) ∧
          (∑' wave, velocityMomentDensity order (receipt.wholePath time) wave) ≤ bound := by
  let start := left + (right - left) / 4
  let stop := left + (right - left) / 2
  have startNonnegative : 0 ≤ start := by dsimp [start]; linarith
  have startStop : start < stop := by dsimp [start, stop]; linarith
  have stopLt : stop < 1 := by dsimp [stop]; linarith
  obtain ⟨center, centerInside, control⟩ := wholeMild_generated_control_window
    ledger receipt.core start stop startNonnegative startStop stopLt
  let duration := bandDuration ledger start stop
  have positive : 0 < duration := bandDuration_pos ledger start stop startStop stopLt
  have width : duration ≤ stop - start := bandDuration_le_width ledger start stop
  refine ⟨center + duration / 2, center + 2 * duration / 3, ?_, ?_, ?_, ?_⟩
  · dsimp [start] at centerInside
    linarith [centerInside.1]
  · linarith
  · dsimp [start, stop] at width centerInside
    linarith [centerInside.2]
  · intro order
    refine ⟨endpointBudget ledger (bandVelocityAllowance ledger start stop) order (duration / 6), ?_⟩
    intro time afterStart beforeEnd
    rw [receipt.wholePath_apply]
    exact control order time afterStart beforeEnd

theorem source_recovery_controlled_subinterval (initial : GeneratedWholeRestartCurrent nu) :
    ∃ first last : ℝ, 0 < first ∧ first < last ∧
      last < (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 ∧
      ∀ order : ℕ, ∃ bound : ℝ, ∀ time : Icc (0 : ℝ) 1,
        first ≤ time.1 → time.1 ≤ last →
        Summable (velocityMomentDensity order
          ((sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).wholePath time)) ∧
          (∑' wave, velocityMomentDensity order
            ((sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).wholePath time) wave) ≤ bound :=
  wholeMild_controlled_subinterval (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore initial)
    (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) 0
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 le_rfl
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time_pos
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2

theorem source_absolute_recovery_controlled_subinterval (initial : GeneratedWholeRestartCurrent nu) :
    ∃ first last : ℝ,
      wholeRestartVelocityAccumulationTime initial < first ∧ first < last ∧
        last < (sourceGeneratedNativeTemporalSelectedAbsoluteTime initial).1 ∧
        ∀ order : ℕ, ∃ bound : ℝ,
          ∀ time : Icc (wholeRestartVelocityAccumulationTime initial) (wholeRestartVelocityAccumulationTime initial + 1),
            first ≤ time.1 → time.1 ≤ last →
            Summable (velocityMomentDensity order (sourceGeneratedNativeTemporalAbsoluteWholePath initial time)) ∧
              (∑' wave, velocityMomentDensity order (sourceGeneratedNativeTemporalAbsoluteWholePath initial time) wave) ≤ bound := by
  obtain ⟨first, last, firstPositive, ordered, beforeSelected, controls⟩ := source_recovery_controlled_subinterval initial
  let accumulation := wholeRestartVelocityAccumulationTime initial
  refine ⟨accumulation + first, accumulation + last, by dsimp [accumulation]; linarith, by linarith, ?_, ?_⟩
  · change accumulation + last < accumulation + (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1
    linarith
  · intro order
    obtain ⟨bound, boundControls⟩ := controls order
    refine ⟨bound, ?_⟩
    intro time afterStart beforeEnd
    exact boundControls (endpointAbsoluteToLocalTime accumulation time) (by
      change first ≤ time.1 - accumulation
      linarith) (by
      change time.1 - accumulation ≤ last
      linarith)

end
end SaturationMonoid.NavierStokes.NativeRecoveryControlProducer
