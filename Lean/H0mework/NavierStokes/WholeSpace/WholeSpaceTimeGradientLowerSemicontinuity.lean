import H0mework.NavierStokes.ShellSources.InfiniteLineageWeakSolution

/-!
# Whole space-time gradient lower semicontinuity

This module transports the finite Galerkin vorticity-gradient budget through
the actual strong whole-carrier subsequence.  The gradient density is formed
from every fixed Fourier row of the space-time `L²` state.  Uniform finite
partial-sum bounds generate summability of the full lattice density and the
same bound for its `tsum`.

For a strict-critical infinite source lineage, the physical punctured-cube
trajectories supply those bounds from their generated enstrophy-absorption
ledger.  Consequently the whole-lattice weak Fourier limit carries a finite
space-time gradient mass.  Summability, the limit, the subsequence, and the
bound are conclusions rather than certificate fields.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity

open scoped BigOperators ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCriticalPathCompactness
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageWeakSolution

noncomputable section

/-- One wave's contribution to the whole space-time vorticity-gradient mass. -/
def wholeSpaceTimeVorticityGradientDensity
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (wave : IntegerWavevector) : ℝ :=
  integerWaveNormSq wave *
    ‖fixedWaveSpaceTimeRestriction requestedTime wave state‖ ^ 2

/-- The whole Fourier-gradient mass of a space-time `L²` state. -/
def wholeSpaceTimeVorticityGradientMass
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime) : ℝ :=
  ∑' wave : IntegerWavevector,
    wholeSpaceTimeVorticityGradientDensity requestedTime state wave

theorem wholeSpaceTimeVorticityGradientDensity_nonneg
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (wave : IntegerWavevector) :
    0 ≤
      wholeSpaceTimeVorticityGradientDensity
        requestedTime state wave := by
  exact mul_nonneg (integerWaveNormSq_nonneg wave) (sq_nonneg _)

theorem fixedWaveSpaceTimeState_norm_sq_eq_integral
    (requestedTime : ℝ)
    (state : FixedWaveSpaceTimeState requestedTime) :
    ‖state‖ ^ 2 =
      ∫ time,
        ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime) := by
  rw [MeasureTheory.Lp.norm_def]
  rw [MeasureTheory.toReal_eLpNorm
    (MeasureTheory.Lp.aestronglyMeasurable state)]
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ℝ≥0∞)) (by norm_num) (by simp)
    (MeasureTheory.Lp.aestronglyMeasurable state)]
  norm_num
  have powerIdentity :
      ((∫ time,
          ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime)) ^
            ((2 : ℝ)⁻¹)) ^ 2 =
        ∫ time,
          ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime) :=
    Real.rpow_inv_natCast_pow (n := 2)
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)
  convert powerIdentity using 1
  all_goals norm_num

theorem
    fixedWaveSpaceTimeRestriction_wholeTrajectory_norm_sq_eq_intervalIntegral
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Set.Icc (0 : ℝ) requestedTime))
    (wave : IntegerWavevector) :
    ‖fixedWaveSpaceTimeRestriction requestedTime wave
        (wholeTrajectorySpaceTimePath
          requestedTime trajectory trajectoryContinuous)‖ ^ 2 =
      ∫ time in (0 : ℝ)..requestedTime,
        ‖trajectory time wave‖ ^ 2 := by
  rw [fixedWaveSpaceTimeState_norm_sq_eq_integral]
  let stateLp :=
    wholeTrajectorySpaceTimePath
      requestedTime trajectory trajectoryContinuous
  have stateAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (wholeTrajectoryBoundedPath
        requestedTime trajectory trajectoryContinuous)
  have rowAE :=
    fixedWaveSpaceTimeRestriction_coeFn
      requestedTime wave stateLp
  calc
    (∫ time,
        ‖fixedWaveSpaceTimeRestriction requestedTime wave
          (wholeTrajectorySpaceTimePath
            requestedTime trajectory trajectoryContinuous) time‖ ^ 2
        ∂(commonTimeMeasure requestedTime)) =
        ∫ time : Set.Icc (0 : ℝ) requestedTime,
          ‖trajectory time.1 wave‖ ^ 2
        ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards [rowAE, stateAE] with time rowEq stateEq
      change
        ‖fixedWaveSpaceTimeRestriction requestedTime wave
          stateLp time‖ ^ 2 = _
      rw [rowEq]
      have statePoint : stateLp time = trajectory time.1 := by
        have statePoint' :
            stateLp time =
              wholeTrajectoryBoundedPath requestedTime trajectory
                trajectoryContinuous time := by
          simpa [stateLp, wholeTrajectorySpaceTimePath] using stateEq
        exact statePoint'.trans rfl
      rw [statePoint]
    _ =
        ∫ time in (0 : ℝ)..requestedTime,
          ‖trajectory time wave‖ ^ 2 := by
      exact
        commonTime_integral_eq_intervalIntegral
          requestedTime requestedTimePos.le
          (fun time => ‖trajectory time wave‖ ^ 2)

theorem
    wholeTrajectory_gradientDensity_finsetSum_le_enstrophyIntegral
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (modes waves : Finset IntegerWavevector)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (evolves :
      ∀ time ∈ Set.Icc (0 : ℝ) requestedTime,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory time)) time)
    (supported :
      ∀ time ∈ Set.Icc (0 : ℝ) requestedTime,
        ∀ wave, wave ∉ modes → trajectory time wave = 0) :
    (∑ wave ∈ waves,
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (wholeTrajectorySpaceTimePath requestedTime trajectory
            (fun time timeMem =>
              (evolves time timeMem).continuousAt.continuousWithinAt))
          wave) ≤
      ∫ time in (0 : ℝ)..requestedTime,
        finiteStateVorticityEnstrophyMass
          modes (trajectory time) := by
  let trajectoryContinuous :
      ContinuousOn trajectory (Set.Icc (0 : ℝ) requestedTime) :=
    fun time timeMem =>
      (evolves time timeMem).continuousAt.continuousWithinAt
  have rowIntegrable :
      ∀ wave : IntegerWavevector,
        IntervalIntegrable
          (fun time =>
            integerWaveNormSq wave *
              ‖trajectory time wave‖ ^ 2)
          volume 0 requestedTime := by
    intro wave
    apply ContinuousOn.intervalIntegrable_of_Icc
      requestedTimePos.le
    have rowContinuous :
        ContinuousOn
          (fun time => trajectory time wave)
          (Set.Icc (0 : ℝ) requestedTime) := by
      exact
        ((lp.evalCLM ℂ
          (fun _ : IntegerWavevector =>
            ComplexCoordinateVector)
          2 wave).continuous.comp_continuousOn
            trajectoryContinuous)
    exact continuousOn_const.mul (rowContinuous.norm.pow 2)
  have enstrophyIntegrable :
      IntervalIntegrable
        (fun time =>
          finiteStateVorticityEnstrophyMass
            modes (trajectory time))
        volume 0 requestedTime := by
    apply ContinuousOn.intervalIntegrable_of_Icc
      requestedTimePos.le
    intro time timeMem
    exact
      (finiteStateVorticityEnstrophyMass_continuousAt_of_hasDerivAt
        modes trajectory time
        (finiteStateVorticityGenerator
          modes ν (trajectory time))
        (evolves time timeMem)).continuousWithinAt
  have pointwise :
      ∀ time ∈ Set.Icc (0 : ℝ) requestedTime,
        (∑ wave ∈ waves,
            integerWaveNormSq wave *
              ‖trajectory time wave‖ ^ 2) ≤
          finiteStateVorticityEnstrophyMass
            modes (trajectory time) := by
    intro time timeMem
    let active := waves.filter fun wave => wave ∈ modes
    have removeSilent :
        (∑ wave ∈ waves,
            integerWaveNormSq wave *
              ‖trajectory time wave‖ ^ 2) =
          ∑ wave ∈ active,
            integerWaveNormSq wave *
              ‖trajectory time wave‖ ^ 2 := by
      classical
      rw [show active = waves.filter (fun wave => wave ∈ modes) from rfl]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro wave waveMem
      by_cases waveInModes : wave ∈ modes
      · simp [waveInModes]
      · simp [waveInModes, supported time timeMem wave waveInModes]
    rw [removeSilent]
    calc
      (∑ wave ∈ active,
          integerWaveNormSq wave *
            ‖trajectory time wave‖ ^ 2) ≤
          ∑ wave ∈ active,
            integerWaveNormSq wave *
              complexCoordinateAmplitudeSq
                (trajectory time wave) := by
        apply Finset.sum_le_sum
        intro wave waveMem
        exact mul_le_mul_of_nonneg_left
          (complexCoordinateVector_norm_sq_le_amplitudeSq
            (trajectory time wave))
          (integerWaveNormSq_nonneg wave)
      _ ≤
          ∑ wave ∈ modes,
            integerWaveNormSq wave *
              complexCoordinateAmplitudeSq
                (trajectory time wave) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro wave waveMem
          exact (Finset.mem_filter.mp waveMem).2
        · intro wave waveNotMem waveMem
          exact mul_nonneg
            (integerWaveNormSq_nonneg wave)
            (complexCoordinateAmplitudeSq_nonneg _)
      _ =
          finiteStateVorticityEnstrophyMass
            modes (trajectory time) := rfl
  calc
    (∑ wave ∈ waves,
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (wholeTrajectorySpaceTimePath requestedTime trajectory
            (fun time timeMem =>
              (evolves time timeMem).continuousAt.continuousWithinAt))
          wave) =
        ∑ wave ∈ waves,
          ∫ time in (0 : ℝ)..requestedTime,
            integerWaveNormSq wave *
              ‖trajectory time wave‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro wave waveMem
      unfold wholeSpaceTimeVorticityGradientDensity
      rw [
        fixedWaveSpaceTimeRestriction_wholeTrajectory_norm_sq_eq_intervalIntegral
          requestedTime requestedTimePos trajectory
          trajectoryContinuous wave,
        intervalIntegral.integral_const_mul]
    _ =
        ∫ time in (0 : ℝ)..requestedTime,
          ∑ wave ∈ waves,
            integerWaveNormSq wave *
              ‖trajectory time wave‖ ^ 2 := by
      symm
      exact intervalIntegral.integral_finsetSum
        (fun wave waveMem => rowIntegrable wave)
    _ ≤
        ∫ time in (0 : ℝ)..requestedTime,
          finiteStateVorticityEnstrophyMass
            modes (trajectory time) := by
      apply intervalIntegral.integral_mono_on
        requestedTimePos.le
      · apply ContinuousOn.intervalIntegrable_of_Icc
          requestedTimePos.le
        apply continuousOn_finsetSum waves
        intro wave waveMem
        have rowContinuous :
            ContinuousOn
              (fun time => trajectory time wave)
              (Set.Icc (0 : ℝ) requestedTime) := by
          exact
            ((lp.evalCLM ℂ
              (fun _ : IntegerWavevector =>
                ComplexCoordinateVector)
              2 wave).continuous.comp_continuousOn
                trajectoryContinuous)
        exact continuousOn_const.mul (rowContinuous.norm.pow 2)
      · exact enstrophyIntegrable
      · exact pointwise

theorem
    puncturedCanonicalCriticalSpaceTimePath_gradientDensity_finsetSum_le_uniform
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ requestedTime : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (requestedTimePos : 0 < requestedTime)
    (radius : ℕ)
    (waves : Finset IntegerWavevector) :
    (∑ wave ∈ waves,
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (puncturedCanonicalCriticalSpaceTimePath
            lineage ν θ θLtOne criticalMargin
            requestedTime requestedTimePos radius)
          wave) ≤
      ((1 / 2 : ℝ) *
          criticalCoefficientEnstrophyCeiling ν θ) /
        criticalEnstrophyAbsorptionCoefficient θ ν := by
  let path :=
    puncturedCanonicalCriticalScalePath
      lineage ν θ criticalMargin radius
  let budget :=
    path.commonTimeBudget θLtOne requestedTimePos
  let trajectory :=
    puncturedCanonicalCriticalTrajectory
      lineage ν θ θLtOne criticalMargin
      requestedTime requestedTimePos radius
  have evolves :
      ∀ time ∈ Set.Icc (0 : ℝ) requestedTime,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            (puncturedIntegerWaveFrequencyCube radius)
            ν.coeff (trajectory time)) time := by
    intro time timeMem
    exact
      (puncturedCanonicalCriticalTrajectory_physicalProperties
        lineage ν θ θLtOne criticalMargin
        requestedTime requestedTimePos radius
        time timeMem).1
  have supported :
      ∀ time ∈ Set.Icc (0 : ℝ) requestedTime,
        ∀ wave,
          wave ∉ puncturedIntegerWaveFrequencyCube radius →
            trajectory time wave = 0 := by
    intro time timeMem wave waveNotMem
    exact
      (puncturedCanonicalCriticalTrajectory_physicalProperties
        lineage ν θ θLtOne criticalMargin
        requestedTime requestedTimePos radius
        time timeMem).2.1 wave waveNotMem
  have finiteSumLe :
      (∑ wave ∈ waves,
          wholeSpaceTimeVorticityGradientDensity requestedTime
            (puncturedCanonicalCriticalSpaceTimePath
              lineage ν θ θLtOne criticalMargin
              requestedTime requestedTimePos radius)
            wave) ≤
        ∫ time in (0 : ℝ)..requestedTime,
          finiteStateVorticityEnstrophyMass
            (puncturedIntegerWaveFrequencyCube radius)
            (trajectory time) := by
    rw [
      puncturedCanonicalCriticalSpaceTimePath_eq_wholeTrajectorySpaceTimePath
        lineage ν θ θLtOne criticalMargin
        requestedTime requestedTimePos radius]
    simpa only [trajectory, evolves] using
      wholeTrajectory_gradientDensity_finsetSum_le_enstrophyIntegral
        requestedTime requestedTimePos
        (puncturedIntegerWaveFrequencyCube radius)
        waves ν.coeff trajectory evolves supported
  have terminalNonneg :
      0 ≤
        finiteStateVorticityHalfEnstrophy
          (generatedSupport path.current)
          (budget.trajectory requestedTime) := by
    unfold finiteStateVorticityHalfEnstrophy
      finiteStateVorticityCoefficientEnstrophy
    exact mul_nonneg (by norm_num) <|
      Finset.sum_nonneg fun wave waveMem =>
        complexCoordinateAmplitudeSq_nonneg _
  have absorptionToInitial :
      criticalEnstrophyAbsorptionCoefficient θ ν *
            (∫ time in (0 : ℝ)..requestedTime,
              finiteStateVorticityEnstrophyMass
                (generatedSupport path.current)
                (budget.trajectory time)) ≤
        finiteStateVorticityHalfEnstrophy
          (generatedSupport path.current)
          (budget.trajectory 0) :=
    budget.enstrophyAbsorption.trans
      (sub_le_self _ terminalNonneg)
  have absorptionPos :
      0 < criticalEnstrophyAbsorptionCoefficient θ ν :=
    criticalEnstrophyAbsorptionCoefficient_pos θ θLtOne ν
  have integralLeInitial :
      (∫ time in (0 : ℝ)..requestedTime,
          finiteStateVorticityEnstrophyMass
            (generatedSupport path.current)
            (budget.trajectory time)) ≤
        finiteStateVorticityHalfEnstrophy
            (generatedSupport path.current)
            (budget.trajectory 0) /
          criticalEnstrophyAbsorptionCoefficient θ ν :=
    (le_div_iff₀ absorptionPos).2 (by
      simpa only [mul_comm] using absorptionToInitial)
  have initialHalfLe :
      finiteStateVorticityHalfEnstrophy
            (generatedSupport path.current)
            (budget.trajectory 0) ≤
        (1 / 2 : ℝ) *
          criticalCoefficientEnstrophyCeiling ν θ := by
    unfold finiteStateVorticityHalfEnstrophy
    apply mul_le_mul_of_nonneg_left
    · rw [budget.initial]
      exact path.initialEnstrophy_le_ceiling
    · norm_num
  have integralLeUniform :
      (∫ time in (0 : ℝ)..requestedTime,
          finiteStateVorticityEnstrophyMass
            (generatedSupport path.current)
            (budget.trajectory time)) ≤
        ((1 / 2 : ℝ) *
            criticalCoefficientEnstrophyCeiling ν θ) /
          criticalEnstrophyAbsorptionCoefficient θ ν :=
    integralLeInitial.trans
      (div_le_div_of_nonneg_right initialHalfLe absorptionPos.le)
  have supportEq :
      generatedSupport path.current =
        puncturedIntegerWaveFrequencyCube radius := by
    exact
      puncturedCanonicalCriticalScalePath_generatedSupport
        lineage ν θ criticalMargin radius
  have trajectoryEq : budget.trajectory = trajectory := by
    rfl
  rw [supportEq, trajectoryEq] at integralLeUniform
  exact finiteSumLe.trans integralLeUniform

theorem tendsto_wholeSpaceTimeVorticityGradientDensity
    (requestedTime : ℝ)
    (stateSequence : ℕ → SpaceTimeState requestedTime)
    (stateLimit : SpaceTimeState requestedTime)
    (stateTendsto :
      Tendsto stateSequence atTop (𝓝 stateLimit))
    (wave : IntegerWavevector) :
    Tendsto
      (fun index =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime (stateSequence index) wave)
      atTop
      (𝓝
        (wholeSpaceTimeVorticityGradientDensity
          requestedTime stateLimit wave)) := by
  have rowTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction requestedTime wave
            (stateSequence index))
        atTop
        (𝓝
          (fixedWaveSpaceTimeRestriction requestedTime wave
            stateLimit)) :=
    ((fixedWaveSpaceTimeRestriction requestedTime wave).continuous.tendsto
      stateLimit).comp stateTendsto
  exact
    (tendsto_const_nhds.mul (rowTendsto.norm.pow 2))

theorem
    wholeSpaceTimeVorticityGradientDensity_finsetSum_le_of_uniform_bound
    (requestedTime : ℝ)
    (stateSequence : ℕ → SpaceTimeState requestedTime)
    (stateLimit : SpaceTimeState requestedTime)
    (stateTendsto :
      Tendsto stateSequence atTop (𝓝 stateLimit))
    (ceiling : ℝ)
    (finiteSumBound :
      ∀ index : ℕ, ∀ waves : Finset IntegerWavevector,
        (∑ wave ∈ waves,
          wholeSpaceTimeVorticityGradientDensity
            requestedTime (stateSequence index) wave) ≤
          ceiling)
    (waves : Finset IntegerWavevector) :
    (∑ wave ∈ waves,
        wholeSpaceTimeVorticityGradientDensity
          requestedTime stateLimit wave) ≤
      ceiling := by
  have finiteSumTendsto :
      Tendsto
        (fun index =>
          ∑ wave ∈ waves,
            wholeSpaceTimeVorticityGradientDensity
              requestedTime (stateSequence index) wave)
        atTop
        (𝓝
          (∑ wave ∈ waves,
            wholeSpaceTimeVorticityGradientDensity
              requestedTime stateLimit wave)) := by
    apply tendsto_finsetSum
    intro wave waveMem
    exact
      tendsto_wholeSpaceTimeVorticityGradientDensity
        requestedTime stateSequence stateLimit stateTendsto wave
  exact le_of_tendsto finiteSumTendsto
    (Filter.Eventually.of_forall fun index =>
      finiteSumBound index waves)

theorem summable_wholeSpaceTimeVorticityGradientDensity_of_uniform_bound
    (requestedTime : ℝ)
    (stateSequence : ℕ → SpaceTimeState requestedTime)
    (stateLimit : SpaceTimeState requestedTime)
    (stateTendsto :
      Tendsto stateSequence atTop (𝓝 stateLimit))
    (ceiling : ℝ)
    (finiteSumBound :
      ∀ index : ℕ, ∀ waves : Finset IntegerWavevector,
        (∑ wave ∈ waves,
          wholeSpaceTimeVorticityGradientDensity
            requestedTime (stateSequence index) wave) ≤
          ceiling) :
    Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime stateLimit wave := by
  apply summable_of_sum_le
    (wholeSpaceTimeVorticityGradientDensity_nonneg
      requestedTime stateLimit)
  intro waves
  exact
    wholeSpaceTimeVorticityGradientDensity_finsetSum_le_of_uniform_bound
      requestedTime stateSequence stateLimit stateTendsto
      ceiling finiteSumBound waves

theorem wholeSpaceTimeVorticityGradientMass_le_of_uniform_bound
    (requestedTime : ℝ)
    (stateSequence : ℕ → SpaceTimeState requestedTime)
    (stateLimit : SpaceTimeState requestedTime)
    (stateTendsto :
      Tendsto stateSequence atTop (𝓝 stateLimit))
    (ceiling : ℝ)
    (finiteSumBound :
      ∀ index : ℕ, ∀ waves : Finset IntegerWavevector,
        (∑ wave ∈ waves,
          wholeSpaceTimeVorticityGradientDensity
            requestedTime (stateSequence index) wave) ≤
          ceiling) :
    wholeSpaceTimeVorticityGradientMass
        requestedTime stateLimit ≤ ceiling := by
  unfold wholeSpaceTimeVorticityGradientMass
  have summable :=
    summable_wholeSpaceTimeVorticityGradientDensity_of_uniform_bound
      requestedTime stateSequence stateLimit stateTendsto
      ceiling finiteSumBound
  apply le_of_tendsto summable.hasSum
  exact Filter.Eventually.of_forall fun waves =>
    wholeSpaceTimeVorticityGradientDensity_finsetSum_le_of_uniform_bound
      requestedTime stateSequence stateLimit stateTendsto
      ceiling finiteSumBound waves

theorem GeneratedIntegerShellInfiniteLineage.exists_weakFourierLimit_with_gradientMass
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ requestedTime : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (requestedTimePos : 0 < requestedTime) :
    ∃ stateLimit : SpaceTimeState requestedTime,
      stateLimit ∈
          closure
            (generatedCriticalSpaceTimePathFamily
              (ν := ν) θLtOne requestedTimePos) ∧
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
        Tendsto
            (fun index =>
              puncturedCanonicalCriticalSpaceTimePath
                lineage ν θ θLtOne criticalMargin
                requestedTime requestedTimePos
                (subsequence index))
            atTop (𝓝 stateLimit) ∧
        (∀ wave : IntegerWavevector, wave ≠ 0 →
          ∃ nonlinearLimit :
              NonlinearRowSpaceTimeState requestedTime,
            Tendsto
                (fun index =>
                  wholeNonlinearRowSpaceTimePath requestedTime
                    (puncturedCanonicalCriticalTrajectory
                      lineage ν θ θLtOne criticalMargin
                      requestedTime requestedTimePos
                      (subsequence index))
                    (fun time timeMem =>
                      ((puncturedCanonicalCriticalTrajectory_physicalProperties
                        lineage ν θ θLtOne criticalMargin
                        requestedTime requestedTimePos
                        (subsequence index) time timeMem).1).continuousAt.continuousWithinAt)
                    (fun time timeMem =>
                      (puncturedCanonicalCriticalTrajectory_physicalProperties
                        lineage ν θ θLtOne criticalMargin
                        requestedTime requestedTimePos
                        (subsequence index) time timeMem).2.2.1)
                    wave)
                atTop (𝓝 nonlinearLimit) ∧
              ∀ (test testDerivative : ℝ → ℂ),
                ∀ (testHasDeriv :
                    ∀ t ∈ Set.Icc (0 : ℝ) requestedTime,
                      HasDerivAt test (testDerivative t) t)
                  (testDerivativeContinuous :
                    ContinuousOn testDerivative
                      (Set.Icc (0 : ℝ) requestedTime))
                  (_testZero : test 0 = 0)
                  (_testRequestedTimeZero :
                    test requestedTime = 0),
                fixedWaveWeakAction requestedTime ν.coeff wave
                    (restrictedScalarL2 requestedTime test
                      (fun time timeMem =>
                        (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
                    (restrictedScalarL2 requestedTime testDerivative
                      testDerivativeContinuous)
                    (restrictedScalarLInf requestedTime test
                      (fun time timeMem =>
                        (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
                    stateLimit nonlinearLimit =
                  0) ∧
        Summable
          (fun wave : IntegerWavevector =>
            wholeSpaceTimeVorticityGradientDensity
              requestedTime stateLimit wave) ∧
        wholeSpaceTimeVorticityGradientMass
            requestedTime stateLimit ≤
          ((1 / 2 : ℝ) *
              criticalCoefficientEnstrophyCeiling ν θ) /
            criticalEnstrophyAbsorptionCoefficient θ ν := by
  obtain
      ⟨stateLimit, stateLimitMem, subsequence, subsequenceMono,
        stateTendsto, weakRows⟩ :=
    ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageWeakSolution.GeneratedIntegerShellInfiniteLineage.exists_weakFourierLimit
      lineage ν θ requestedTime θLtOne criticalMargin requestedTimePos
  let stateSequence : ℕ → SpaceTimeState requestedTime :=
    fun index =>
      puncturedCanonicalCriticalSpaceTimePath
        lineage ν θ θLtOne criticalMargin
        requestedTime requestedTimePos (subsequence index)
  let ceiling : ℝ :=
    ((1 / 2 : ℝ) *
        criticalCoefficientEnstrophyCeiling ν θ) /
      criticalEnstrophyAbsorptionCoefficient θ ν
  have stateTendsto' :
      Tendsto stateSequence atTop (𝓝 stateLimit) := by
    simpa only [stateSequence] using stateTendsto
  have finiteSumBound :
      ∀ index : ℕ, ∀ waves : Finset IntegerWavevector,
        (∑ wave ∈ waves,
          wholeSpaceTimeVorticityGradientDensity
            requestedTime (stateSequence index) wave) ≤
          ceiling := by
    intro index waves
    simpa only [stateSequence, ceiling] using
      puncturedCanonicalCriticalSpaceTimePath_gradientDensity_finsetSum_le_uniform
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos (subsequence index) waves
  have gradientSummable :
      Summable
        (fun wave : IntegerWavevector =>
          wholeSpaceTimeVorticityGradientDensity
            requestedTime stateLimit wave) :=
    summable_wholeSpaceTimeVorticityGradientDensity_of_uniform_bound
      requestedTime stateSequence stateLimit stateTendsto'
      ceiling finiteSumBound
  have gradientMassLe :
      wholeSpaceTimeVorticityGradientMass
          requestedTime stateLimit ≤ ceiling :=
    wholeSpaceTimeVorticityGradientMass_le_of_uniform_bound
      requestedTime stateSequence stateLimit stateTendsto'
      ceiling finiteSumBound
  exact
    ⟨stateLimit, stateLimitMem, subsequence, subsequenceMono,
      stateTendsto, weakRows, gradientSummable, gradientMassLe⟩

end

end ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
end NavierStokes
end SaturationMonoid
