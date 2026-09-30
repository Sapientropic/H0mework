import H0mework.NavierStokes.ShellSources.FixedWaveNonlinearL2
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Source-generated infinite mild/Duhamel passage

This module passes the actual fixed-wave finite Galerkin mild identity
through the source-generated subsequence already carrying the strong state
and nonlinear-row limits.  Every nonzero Fourier row of the resulting
whole state has a continuous representative satisfying the genuine
heat/Duhamel law.  The same nonlinear row is then identified with the
unweighted row of the source-generated whole `L²_t H⁻¹_x` forcing.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel

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
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCriticalPathCompactness
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellClosedNonlinearWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellCriticalSerrinWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellNonlinearNegativeOneForcing
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellFixedWaveNonlinearL2
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow

noncomputable section

theorem commonTime_integral_Iic_eq_intervalIntegral
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (requestedTime : ℝ)
    (requestedTimeNonneg : 0 ≤ requestedTime)
    (time : Icc (0 : ℝ) requestedTime)
    (function : ℝ → E) :
    (∫ earlier in Iic time,
        function earlier.1
        ∂(commonTimeMeasure requestedTime)) =
      ∫ earlier in (0 : ℝ)..time.1, function earlier := by
  rw [← MeasureTheory.integral_indicator measurableSet_Iic]
  calc
    (∫ earlier,
        (Iic time).indicator
          (fun actual : Icc (0 : ℝ) requestedTime =>
            function actual.1) earlier
        ∂(commonTimeMeasure requestedTime)) =
        ∫ earlier,
          {actual : ℝ | actual ≤ time.1}.indicator function
            earlier.1
          ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards with earlier
      rfl
    _ =
        ∫ earlier in (0 : ℝ)..requestedTime,
          {actual : ℝ | actual ≤ time.1}.indicator function earlier :=
      commonTime_integral_eq_intervalIntegral_vector
        requestedTime requestedTimeNonneg
        ({actual : ℝ | actual ≤ time.1}.indicator function)
    _ =
        ∫ earlier in (0 : ℝ)..time.1, function earlier :=
      intervalIntegral.integral_indicator time.2

/--
The genuine fixed-wave heat/Duhamel value formed from one initial Fourier
row and one common-time `L¹` nonlinear row.
-/
def fixedWaveHeatDuhamelValue
    (requestedTime ν : ℝ)
    (wave : IntegerWavevector)
    (initial : ComplexCoordinateVector)
    (nonlinear : NonlinearRowSpaceTimeState requestedTime)
    (time : Icc (0 : ℝ) requestedTime) :
    ComplexCoordinateVector :=
  finiteStateVorticityHeatMultiplier ν time.1 wave • initial +
    ∫ earlier in Iic time,
      finiteStateVorticityHeatMultiplier
          ν (time.1 - earlier.1) wave •
        nonlinear earlier
      ∂(commonTimeMeasure requestedTime)

theorem finiteStateVorticityHeatMultiplier_nonneg
    (ν duration : ℝ)
    (wave : IntegerWavevector) :
    0 ≤ finiteStateVorticityHeatMultiplier ν duration wave :=
  Real.exp_nonneg _

theorem finiteStateVorticityHeatMultiplier_le_one
    (νNonneg : 0 ≤ ν)
    (durationNonneg : 0 ≤ duration)
    (wave : IntegerWavevector) :
    finiteStateVorticityHeatMultiplier ν duration wave ≤ 1 := by
  rw [finiteStateVorticityHeatMultiplier, Real.exp_le_one_iff]
  have multiplierNonneg :
      0 ≤ integerWaveViscousMultiplier wave := by
    unfold integerWaveViscousMultiplier
    exact mul_nonneg (sq_nonneg _)
      (integerWaveNormSq_nonneg wave)
  simpa only [neg_mul] using
    neg_nonpos.mpr
      (mul_nonneg (mul_nonneg νNonneg multiplierNonneg)
        durationNonneg)

/-- The causal fixed-wave heat kernel on the compact common-time carrier. -/
def fixedWaveHeatKernelFunction
    (requestedTime ν : ℝ)
    (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    Icc (0 : ℝ) requestedTime → ℂ :=
  (Iic time).indicator fun earlier =>
    (finiteStateVorticityHeatMultiplier
      ν (time.1 - earlier.1) wave : ℂ)

theorem fixedWaveHeatKernelFunction_aestronglyMeasurable
    (requestedTime ν : ℝ)
    (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    AEStronglyMeasurable
      (fixedWaveHeatKernelFunction requestedTime ν wave time)
      (commonTimeMeasure requestedTime) := by
  apply AEStronglyMeasurable.indicator
  · apply Continuous.aestronglyMeasurable
    apply Complex.continuous_ofReal.comp
    unfold finiteStateVorticityHeatMultiplier
    apply Real.continuous_exp.comp
    fun_prop
  · exact measurableSet_Iic

theorem fixedWaveHeatKernelFunction_norm_le_one
    (requestedTime ν : ℝ)
    (νNonneg : 0 ≤ ν)
    (wave : IntegerWavevector)
    (time earlier : Icc (0 : ℝ) requestedTime) :
    ‖fixedWaveHeatKernelFunction
        requestedTime ν wave time earlier‖ ≤ 1 := by
  by_cases earlierLe : earlier ≤ time
  · simp only [fixedWaveHeatKernelFunction,
      Set.indicator_apply, Set.mem_Iic, earlierLe, if_true]
    rw [Complex.norm_real,
      Real.norm_of_nonneg
        (finiteStateVorticityHeatMultiplier_nonneg
          ν (time.1 - earlier.1) wave)]
    exact
      finiteStateVorticityHeatMultiplier_le_one
        νNonneg (sub_nonneg.mpr earlierLe) wave
  · simp only [fixedWaveHeatKernelFunction,
      Set.indicator_apply, Set.mem_Iic, earlierLe, if_false]
    norm_num

noncomputable def fixedWaveHeatKernelLInf
    (requestedTime ν : ℝ)
    (νNonneg : 0 ≤ ν)
    (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    MeasureTheory.Lp ℂ ∞
      (commonTimeMeasure requestedTime) :=
  (MemLp.of_bound
      (fixedWaveHeatKernelFunction_aestronglyMeasurable
        requestedTime ν wave time)
      1
      (ae_of_all _ fun earlier =>
        fixedWaveHeatKernelFunction_norm_le_one
          requestedTime ν νNonneg wave time earlier)).toLp
    (fixedWaveHeatKernelFunction requestedTime ν wave time)

/-- The causal heat integral is a genuine continuous linear readout of the
actual time-`L¹` nonlinear row. -/
def fixedWaveHeatDuhamelIntegralAt
    (requestedTime ν : ℝ)
    (νNonneg : 0 ≤ ν)
    (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    NonlinearRowSpaceTimeState requestedTime →L[ℂ]
      ComplexCoordinateVector :=
  fixedLInfScalarL1IntegralCLM requestedTime
    (fixedWaveHeatKernelLInf
      requestedTime ν νNonneg wave time)

theorem fixedWaveHeatDuhamelIntegralAt_apply
    (requestedTime ν : ℝ)
    (νNonneg : 0 ≤ ν)
    (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime)
    (nonlinear : NonlinearRowSpaceTimeState requestedTime) :
    fixedWaveHeatDuhamelIntegralAt
        requestedTime ν νNonneg wave time nonlinear =
      ∫ earlier in Iic time,
        finiteStateVorticityHeatMultiplier
            ν (time.1 - earlier.1) wave •
          nonlinear earlier
        ∂(commonTimeMeasure requestedTime) := by
  let kernel :=
    fixedWaveHeatKernelLInf
      requestedTime ν νNonneg wave time
  have kernelAE :
      ⇑kernel =ᵐ[commonTimeMeasure requestedTime]
        fixedWaveHeatKernelFunction
          requestedTime ν wave time := by
    dsimp [kernel, fixedWaveHeatKernelLInf]
    exact MemLp.coeFn_toLp _
  have productAE :
      ⇑(kernel • nonlinear :
          MeasureTheory.Lp ComplexCoordinateVector 1
            (commonTimeMeasure requestedTime)) =ᵐ[
          commonTimeMeasure requestedTime]
        ⇑kernel • ⇑nonlinear :=
    MeasureTheory.Lp.coeFn_lpSMul kernel nonlinear
  change
    (MeasureTheory.L1.integralCLM' ℂ)
        (kernel • nonlinear) =
      _
  rw [← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  calc
    (∫ earlier,
        (kernel • nonlinear) earlier
        ∂(commonTimeMeasure requestedTime)) =
        ∫ earlier,
          fixedWaveHeatKernelFunction
              requestedTime ν wave time earlier •
            nonlinear earlier
          ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards [productAE, kernelAE] with
        earlier productEq kernelEq
      rw [productEq]
      change kernel earlier • nonlinear earlier = _
      rw [kernelEq]
    _ =
        ∫ earlier in Iic time,
          finiteStateVorticityHeatMultiplier
              ν (time.1 - earlier.1) wave •
            nonlinear earlier
          ∂(commonTimeMeasure requestedTime) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Iic]
      apply integral_congr_ae
      filter_upwards with earlier
      by_cases earlierLe : earlier ≤ time
      · simp only [fixedWaveHeatKernelFunction,
          Set.indicator_apply, Set.mem_Iic,
          earlierLe, if_true]
        ext coordinate
        simp only [Pi.smul_apply, Complex.real_smul,
          smul_eq_mul]
      · simp only [fixedWaveHeatKernelFunction,
          Set.indicator_apply, Set.mem_Iic,
          earlierLe, if_false, zero_smul]

theorem fixedWaveHeatDuhamelValue_eq
    (requestedTime ν : ℝ)
    (νNonneg : 0 ≤ ν)
    (wave : IntegerWavevector)
    (initial : ComplexCoordinateVector)
    (nonlinear : NonlinearRowSpaceTimeState requestedTime)
    (time : Icc (0 : ℝ) requestedTime) :
    fixedWaveHeatDuhamelValue
        requestedTime ν wave initial nonlinear time =
      finiteStateVorticityHeatMultiplier ν time.1 wave • initial +
        fixedWaveHeatDuhamelIntegralAt
          requestedTime ν νNonneg wave time nonlinear := by
  rw [fixedWaveHeatDuhamelValue,
    fixedWaveHeatDuhamelIntegralAt_apply]

theorem tendsto_fixedWaveHeatDuhamelValue
    {ι : Type*}
    {filter : Filter ι}
    (requestedTime ν : ℝ)
    (νNonneg : 0 ≤ ν)
    (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime)
    (initialSequence : ι → ComplexCoordinateVector)
    (nonlinearSequence :
      ι → NonlinearRowSpaceTimeState requestedTime)
    (initialLimit : ComplexCoordinateVector)
    (nonlinearLimit :
      NonlinearRowSpaceTimeState requestedTime)
    (initialTendsto :
      Tendsto initialSequence filter (𝓝 initialLimit))
    (nonlinearTendsto :
      Tendsto nonlinearSequence filter (𝓝 nonlinearLimit)) :
    Tendsto
      (fun index =>
        fixedWaveHeatDuhamelValue requestedTime ν wave
          (initialSequence index) (nonlinearSequence index)
          time)
      filter
      (𝓝
        (fixedWaveHeatDuhamelValue requestedTime ν wave
          initialLimit nonlinearLimit time)) := by
  simp_rw [fixedWaveHeatDuhamelValue_eq
    requestedTime ν νNonneg wave]
  exact
    (initialTendsto.const_smul
      (finiteStateVorticityHeatMultiplier
        ν time.1 wave)).add
      (((fixedWaveHeatDuhamelIntegralAt
        requestedTime ν νNonneg wave time).continuous.tendsto
          nonlinearLimit).comp nonlinearTendsto)

/--
Every retained row of an actual finite-support physical trajectory is
pointwise the causal heat/Duhamel value of its genuine common-time nonlinear
row.  The `L¹` row is reconstructed from the same trajectory.
-/
theorem finiteSupportWave_eq_fixedWaveHeatDuhamelValue
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ modes)
    (ν requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (evolves :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t)
    (supported :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ∀ output : IntegerWavevector,
          output ∉ modes → trajectory t output = 0)
    (transverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        WholeStateTransverse (trajectory t))
    (time : Icc (0 : ℝ) requestedTime) :
    trajectory time.1 wave =
      fixedWaveHeatDuhamelValue requestedTime ν wave
        (trajectory 0 wave)
        (wholeNonlinearRowSpaceTimePath requestedTime
          trajectory
          (fun t timeMem =>
            (evolves t timeMem).continuousAt.continuousWithinAt)
          transverse wave)
        time := by
  let trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime) :=
    fun t timeMem =>
      (evolves t timeMem).continuousAt.continuousWithinAt
  let nonlinearLp : NonlinearRowSpaceTimeState requestedTime :=
    wholeNonlinearRowSpaceTimePath requestedTime
      trajectory trajectoryContinuous transverse wave
  have nonlinearBoundedAE :
      ⇑nonlinearLp =ᵐ[commonTimeMeasure requestedTime]
        ⇑(wholeNonlinearRowBoundedPath requestedTime
          trajectory trajectoryContinuous transverse wave) := by
    dsimp [nonlinearLp, wholeNonlinearRowSpaceTimePath]
    exact
      BoundedContinuousFunction.coeFn_toLp
        (p := (1 : ℝ≥0∞))
        (μ := commonTimeMeasure requestedTime)
        ℂ
        (wholeNonlinearRowBoundedPath requestedTime
          trajectory trajectoryContinuous transverse wave)
  have nonlinearAE :
      ⇑nonlinearLp =ᵐ[commonTimeMeasure requestedTime]
        fun actual =>
          wholeStateVorticityNonlinearCoefficientAt
            (trajectory actual.1) wave := by
    filter_upwards [nonlinearBoundedAE] with
      actual nonlinearEq
    exact nonlinearEq.trans rfl
  have setIntegralEq :
      (∫ earlier in Iic time,
          finiteStateVorticityHeatMultiplier
              ν (time.1 - earlier.1) wave •
            nonlinearLp earlier
          ∂(commonTimeMeasure requestedTime)) =
        ∫ earlier in Iic time,
          finiteStateVorticityHeatMultiplier
              ν (time.1 - earlier.1) wave •
            wholeStateVorticityNonlinearCoefficientAt
              (trajectory earlier.1) wave
          ∂(commonTimeMeasure requestedTime) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae nonlinearAE] with
      earlier nonlinearEq
    rw [nonlinearEq]
  have integralEq :
      (∫ earlier in Iic time,
          finiteStateVorticityHeatMultiplier
              ν (time.1 - earlier.1) wave •
            nonlinearLp earlier
          ∂(commonTimeMeasure requestedTime)) =
        ∫ earlier in (0 : ℝ)..time.1,
          finiteStateVorticityHeatMultiplier
              ν (time.1 - earlier) wave •
            wholeStateVorticityNonlinearCoefficientAt
              (trajectory earlier) wave := by
    rw [setIntegralEq]
    exact
      commonTime_integral_Iic_eq_intervalIntegral
        requestedTime requestedTimePos.le time
        (fun earlier =>
          finiteStateVorticityHeatMultiplier
              ν (time.1 - earlier) wave •
            wholeStateVorticityNonlinearCoefficientAt
              (trajectory earlier) wave)
  have mild :=
    finiteModesWave_infiniteRow_mild_identity
      modes wave waveMem ν trajectory 0 time.1 time.2.1
      (fun t tMem =>
        evolves t
          ⟨tMem.1,
            tMem.2.trans time.2.2⟩)
      (fun t tMem =>
        supported t
          ⟨tMem.1,
            tMem.2.trans time.2.2⟩)
  rw [fixedWaveHeatDuhamelValue, integralEq]
  simpa only [sub_zero] using mild

theorem puncturedCanonicalCriticalTrajectory_eq_fixedWaveHeatDuhamelValue
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
    (wave : IntegerWavevector)
    (waveMem :
      wave ∈ puncturedIntegerWaveFrequencyCube radius)
    (time : Icc (0 : ℝ) requestedTime) :
    puncturedCanonicalCriticalTrajectory
        lineage ν θ θLtOne criticalMargin
        requestedTime requestedTimePos radius time.1 wave =
      fixedWaveHeatDuhamelValue requestedTime ν.coeff wave
        (puncturedCanonicalInitialState lineage radius wave)
        (transverseSpaceTimeNonlinearRow
          (puncturedCanonicalCriticalTransverseSpaceTimePath
            lineage ν θ requestedTime θLtOne criticalMargin
            requestedTimePos radius)
          wave)
        time := by
  let trajectory :=
    puncturedCanonicalCriticalTrajectory
      lineage ν θ θLtOne criticalMargin
      requestedTime requestedTimePos radius
  have evolves :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            (puncturedIntegerWaveFrequencyCube radius)
            ν.coeff (trajectory t)) t := by
    intro t timeMem
    exact
      (puncturedCanonicalCriticalTrajectory_physicalProperties
        lineage ν θ θLtOne criticalMargin requestedTime
        requestedTimePos radius t timeMem).1
  have supported :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ∀ output : IntegerWavevector,
          output ∉ puncturedIntegerWaveFrequencyCube radius →
            trajectory t output = 0 := by
    intro t timeMem
    exact
      (puncturedCanonicalCriticalTrajectory_physicalProperties
        lineage ν θ θLtOne criticalMargin requestedTime
        requestedTimePos radius t timeMem).2.1
  have transverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        WholeStateTransverse (trajectory t) := by
    intro t timeMem
    exact
      (puncturedCanonicalCriticalTrajectory_physicalProperties
        lineage ν θ θLtOne criticalMargin requestedTime
        requestedTimePos radius t timeMem).2.2.1
  have actual :=
    finiteSupportWave_eq_fixedWaveHeatDuhamelValue
      (puncturedIntegerWaveFrequencyCube radius)
      wave waveMem ν.coeff requestedTime requestedTimePos
      trajectory evolves supported transverse time
  have rowEq :
      transverseSpaceTimeNonlinearRow
          (puncturedCanonicalCriticalTransverseSpaceTimePath
            lineage ν θ requestedTime θLtOne criticalMargin
            requestedTimePos radius) wave =
        wholeNonlinearRowSpaceTimePath requestedTime trajectory
          (fun t timeMem =>
            (evolves t timeMem).continuousAt.continuousWithinAt)
          transverse wave := by
    unfold puncturedCanonicalCriticalTransverseSpaceTimePath
    exact transverseSpaceTimeNonlinearRow_wholeTransverseTrajectory
      requestedTime trajectory
        (fun t timeMem =>
          (evolves t timeMem).continuousAt.continuousWithinAt)
        transverse wave
  rw [rowEq]
  simpa only [trajectory,
    puncturedCanonicalCriticalTrajectory_initial] using actual

/-- A continuous representative of one actual fixed Fourier row, together
with its source-generated initial state and genuine nonlinear Duhamel law. -/
structure FixedWaveContinuousMildData
    (requestedTime ν : ℝ)
    (wave : IntegerWavevector)
    (initialSequence : ℕ → ComplexVorticityHilbertState)
    (state : SpaceTimeState requestedTime)
    (nonlinear : NonlinearRowSpaceTimeState requestedTime) where
  initialLimit : ComplexVorticityHilbertState
  initial_tendsto :
    Tendsto initialSequence atTop (𝓝 initialLimit)
  rowPath :
    BoundedContinuousFunction
      (Icc (0 : ℝ) requestedTime)
      ComplexCoordinateVector
  row_represents :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      rowPath time =
        fixedWaveSpaceTimeRestriction
          requestedTime wave state time
  mild_identity :
    ∀ time : Icc (0 : ℝ) requestedTime,
      rowPath time =
        fixedWaveHeatDuhamelValue
          requestedTime ν wave
          (initialLimit wave) nonlinear time

/--
Every fixed nonzero Fourier wave of the source-generated closed nonlinear
receipt has a continuous representative satisfying the genuine mild law.
The compact refinement is generated inside the proof; the state and
nonlinear limits remain the ones carried by the original receipt.
-/
theorem
    ClosedNonlinearWeakLimitReceipt.exists_fixedWaveContinuousMildData
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
    (receipt :
      ClosedNonlinearWeakLimitReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    Nonempty
      (FixedWaveContinuousMildData
        requestedTime ν.coeff wave
        (puncturedCanonicalInitialState lineage)
        receipt.stateLimit
        (transverseSpaceTimeNonlinearRow
          receipt.transverseLimit wave)) := by
  classical
  let observed : Finset IntegerWavevector := {wave}
  let coordinate :
      {actual : IntegerWavevector // actual ∈ observed} :=
    ⟨wave, by simp [observed]⟩
  let pathSequence :
      ℕ → GeneratedCriticalScalePath ν θ :=
    fun index =>
      puncturedCanonicalCriticalScalePath
        lineage ν θ criticalMargin
        (receipt.subsequence index)
  let observedSequence :
      ℕ →
        BoundedContinuousFunction
          (Icc (0 : ℝ) requestedTime)
          (FiniteObservedCoefficientState observed) :=
    fun index =>
      generatedFiniteObservedBoundedPath
        θLtOne requestedTimePos observed
        (pathSequence index)
  have observedSequenceMem :
      ∀ index,
        observedSequence index ∈
          closure
            (generatedFiniteObservedPathFamily
              (ν := ν) θLtOne requestedTimePos observed) := by
    intro index
    apply subset_closure
    exact ⟨pathSequence index, rfl⟩
  rcases
      (generatedFiniteObservedPathFamily_isCompact_closure
        (ν := ν) θLtOne requestedTimePos observed).tendsto_subseq
        observedSequenceMem with
    ⟨observedLimit, _observedLimitMem, refinement,
      refinementStrictMono, observedTendsto⟩
  rcases
      endpointHilbertState_puncturedFrequencyCube_tendsto_limit
        lineage ν θ criticalMargin with
    ⟨initialLimit, _endpointTendsto, initialTendsto⟩
  let observedRowMap :
      BoundedContinuousFunction
          (Icc (0 : ℝ) requestedTime)
          (FiniteObservedCoefficientState observed) →L[ℂ]
        BoundedContinuousFunction
          (Icc (0 : ℝ) requestedTime)
          ComplexCoordinateVector :=
    (ContinuousLinearMap.proj coordinate).compLeftContinuousBounded
      (Icc (0 : ℝ) requestedTime)
  let rowPath :
      BoundedContinuousFunction
        (Icc (0 : ℝ) requestedTime)
        ComplexCoordinateVector :=
    observedRowMap observedLimit
  have observedRowTendsto :
      Tendsto
        (fun index =>
          observedRowMap
            (observedSequence (refinement index)))
        atTop (𝓝 rowPath) := by
    have mapped :=
      (observedRowMap.continuous.tendsto observedLimit).comp
        observedTendsto
    change
      Tendsto
        (observedRowMap ∘ observedSequence ∘ refinement)
        atTop (𝓝 rowPath)
    simpa only [rowPath] using mapped
  have observedRowSpaceTimeTendsto :
      Tendsto
        (fun index =>
          (BoundedContinuousFunction.toLp 2
            (commonTimeMeasure requestedTime) ℂ)
            (observedRowMap
              (observedSequence (refinement index))))
        atTop
        (𝓝
          ((BoundedContinuousFunction.toLp 2
            (commonTimeMeasure requestedTime) ℂ) rowPath)) := by
    exact
      ((BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ).continuous.tendsto
          rowPath).comp observedRowTendsto
  have stateRefinedTendsto :
      Tendsto
        (fun index =>
          puncturedCanonicalCriticalSpaceTimePath
            lineage ν θ θLtOne criticalMargin
            requestedTime requestedTimePos
            (receipt.subsequence (refinement index)))
        atTop (𝓝 receipt.stateLimit) := by
    have refined :=
      receipt.state_tendsto.comp
        refinementStrictMono.tendsto_atTop
    change
      Tendsto
        ((fun index =>
          puncturedCanonicalCriticalSpaceTimePath
            lineage ν θ θLtOne criticalMargin
            requestedTime requestedTimePos
            (receipt.subsequence index)) ∘ refinement)
        atTop (𝓝 receipt.stateLimit)
    exact refined
  have fixedStateRefinedTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction requestedTime wave
            (puncturedCanonicalCriticalSpaceTimePath
              lineage ν θ θLtOne criticalMargin
              requestedTime requestedTimePos
              (receipt.subsequence (refinement index))))
        atTop
        (𝓝
          (fixedWaveSpaceTimeRestriction
            requestedTime wave receipt.stateLimit)) := by
    exact
      ((fixedWaveSpaceTimeRestriction
        requestedTime wave).continuous.tendsto
          receipt.stateLimit).comp stateRefinedTendsto
  have observedRowSpaceTime_eq_fixedWave :
      ∀ index,
        (BoundedContinuousFunction.toLp 2
          (commonTimeMeasure requestedTime) ℂ)
            (observedRowMap
              (observedSequence (refinement index))) =
          fixedWaveSpaceTimeRestriction requestedTime wave
            (puncturedCanonicalCriticalSpaceTimePath
              lineage ν θ θLtOne criticalMargin
              requestedTime requestedTimePos
              (receipt.subsequence (refinement index))) := by
    intro index
    apply MeasureTheory.Lp.ext
    let actualPath : GeneratedCriticalScalePath ν θ :=
      pathSequence (refinement index)
    have rowAE :=
      BoundedContinuousFunction.coeFn_toLp
        (2 : ℝ≥0∞) (commonTimeMeasure requestedTime) ℂ
        (observedRowMap
          (observedSequence (refinement index)))
    have restrictionAE :=
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave
        (puncturedCanonicalCriticalSpaceTimePath
          lineage ν θ θLtOne criticalMargin
          requestedTime requestedTimePos
          (receipt.subsequence (refinement index)))
    have wholeAE :=
      BoundedContinuousFunction.coeFn_toLp
        (2 : ℝ≥0∞) (commonTimeMeasure requestedTime) ℂ
        (generatedWholeBoundedPath
          θLtOne requestedTimePos actualPath)
    filter_upwards [rowAE, restrictionAE, wholeAE] with
      time rowEq restrictionEq wholeEq
    rw [rowEq, restrictionEq]
    change
      observedRowMap
          (observedSequence (refinement index)) time =
        ((BoundedContinuousFunction.toLp 2
          (commonTimeMeasure requestedTime) ℂ)
            (generatedWholeBoundedPath
              θLtOne requestedTimePos actualPath)) time wave
    rw [wholeEq]
    rfl
  have observedAsFixedTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction requestedTime wave
            (puncturedCanonicalCriticalSpaceTimePath
              lineage ν θ θLtOne criticalMargin
              requestedTime requestedTimePos
              (receipt.subsequence (refinement index))))
        atTop
        (𝓝
          ((BoundedContinuousFunction.toLp 2
            (commonTimeMeasure requestedTime) ℂ) rowPath)) := by
    simpa only [observedRowSpaceTime_eq_fixedWave] using
      observedRowSpaceTimeTendsto
  have rowSpaceTimeEq :
      (BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ) rowPath =
        fixedWaveSpaceTimeRestriction
          requestedTime wave receipt.stateLimit :=
    tendsto_nhds_unique
      observedAsFixedTendsto fixedStateRefinedTendsto
  have rowRepresents :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        rowPath time =
          fixedWaveSpaceTimeRestriction
            requestedTime wave receipt.stateLimit time := by
    have rowAE :=
      BoundedContinuousFunction.coeFn_toLp
        (2 : ℝ≥0∞) (commonTimeMeasure requestedTime) ℂ
        rowPath
    rw [rowSpaceTimeEq] at rowAE
    exact rowAE.symm
  have combinedIndexTendsto :
      Tendsto
        (receipt.subsequence ∘ refinement)
        atTop atTop :=
    receipt.subsequence_strictMono.tendsto_atTop.comp
      refinementStrictMono.tendsto_atTop
  have initialRefinedTendsto :
      Tendsto
        (fun index =>
          puncturedCanonicalInitialState lineage
            (receipt.subsequence (refinement index)))
        atTop (𝓝 initialLimit) := by
    have refined := initialTendsto.comp combinedIndexTendsto
    change
      Tendsto
        (puncturedCanonicalInitialState lineage ∘
          receipt.subsequence ∘ refinement)
        atTop (𝓝 initialLimit)
    convert refined using 1
    all_goals rfl
  have initialRowRefinedTendsto :
      Tendsto
        (fun index =>
          puncturedCanonicalInitialState lineage
            (receipt.subsequence (refinement index)) wave)
        atTop (𝓝 (initialLimit wave)) := by
    exact
      (((lp.evalCLM ℂ
        (fun _ : IntegerWavevector =>
          ComplexCoordinateVector)
        2 wave).continuous.tendsto initialLimit).comp
          initialRefinedTendsto)
  have nonlinearRefinedTendsto :
      Tendsto
        (fun index =>
          transverseSpaceTimeNonlinearRow
            (puncturedCanonicalCriticalTransverseSpaceTimePath
              lineage ν θ requestedTime θLtOne criticalMargin
              requestedTimePos
              (receipt.subsequence (refinement index)))
            wave)
        atTop
        (𝓝
          (transverseSpaceTimeNonlinearRow
            receipt.transverseLimit wave)) := by
    have base :=
      tendsto_transverseSpaceTimeNonlinearRow
        (fun index =>
          puncturedCanonicalCriticalTransverseSpaceTimePath
            lineage ν θ requestedTime θLtOne criticalMargin
            requestedTimePos (receipt.subsequence index))
        receipt.transverseLimit receipt.transverse_tendsto wave
    have refined :=
      base.comp refinementStrictMono.tendsto_atTop
    change
      Tendsto
        ((fun index =>
          transverseSpaceTimeNonlinearRow
            (puncturedCanonicalCriticalTransverseSpaceTimePath
              lineage ν θ requestedTime θLtOne criticalMargin
              requestedTimePos (receipt.subsequence index))
            wave) ∘ refinement)
        atTop
        (𝓝
          (transverseSpaceTimeNonlinearRow
            receipt.transverseLimit wave))
    exact refined
  have mildIdentity :
      ∀ time : Icc (0 : ℝ) requestedTime,
        rowPath time =
          fixedWaveHeatDuhamelValue
            requestedTime ν.coeff wave
            (initialLimit wave)
            (transverseSpaceTimeNonlinearRow
              receipt.transverseLimit wave)
            time := by
    intro time
    have observedValueTendsto :
        Tendsto
          (fun index =>
            observedRowMap
              (observedSequence (refinement index)) time)
          atTop (𝓝 (rowPath time)) := by
      have evaluated :=
        ((BoundedContinuousFunction.evalCLM
          ℂ time).continuous.tendsto rowPath).comp
            observedRowTendsto
      change
        Tendsto
          ((BoundedContinuousFunction.evalCLM ℂ time) ∘
            (fun index =>
              observedRowMap
                (observedSequence (refinement index))))
          atTop (𝓝 (rowPath time))
      exact evaluated
    have duhamelTendsto :
        Tendsto
          (fun index =>
            fixedWaveHeatDuhamelValue
              requestedTime ν.coeff wave
              (puncturedCanonicalInitialState lineage
                (receipt.subsequence (refinement index)) wave)
              (transverseSpaceTimeNonlinearRow
                (puncturedCanonicalCriticalTransverseSpaceTimePath
                  lineage ν θ requestedTime θLtOne criticalMargin
                  requestedTimePos
                  (receipt.subsequence (refinement index)))
                wave)
              time)
          atTop
          (𝓝
            (fixedWaveHeatDuhamelValue
              requestedTime ν.coeff wave
              (initialLimit wave)
              (transverseSpaceTimeNonlinearRow
                receipt.transverseLimit wave)
              time)) :=
      tendsto_fixedWaveHeatDuhamelValue
        requestedTime ν.coeff ν.coeff_pos.le wave time
        (fun index =>
          puncturedCanonicalInitialState lineage
            (receipt.subsequence (refinement index)) wave)
        (fun index =>
          transverseSpaceTimeNonlinearRow
            (puncturedCanonicalCriticalTransverseSpaceTimePath
              lineage ν θ requestedTime θLtOne criticalMargin
              requestedTimePos
              (receipt.subsequence (refinement index)))
            wave)
        (initialLimit wave)
        (transverseSpaceTimeNonlinearRow
          receipt.transverseLimit wave)
        initialRowRefinedTendsto nonlinearRefinedTendsto
    have retainedEventually :
        ∀ᶠ index : ℕ in atTop,
          wave ∈
            puncturedIntegerWaveFrequencyCube
              (receipt.subsequence (refinement index)) :=
      combinedIndexTendsto
        (nonzero_integerWave_eventually_mem_puncturedFrequencyCube
          wave waveNe)
    have finiteMildEventually :
        (fun index =>
          observedRowMap
            (observedSequence (refinement index)) time) =ᶠ[atTop]
          (fun index =>
            fixedWaveHeatDuhamelValue
              requestedTime ν.coeff wave
              (puncturedCanonicalInitialState lineage
                (receipt.subsequence (refinement index)) wave)
              (transverseSpaceTimeNonlinearRow
                (puncturedCanonicalCriticalTransverseSpaceTimePath
                  lineage ν θ requestedTime θLtOne criticalMargin
                  requestedTimePos
                  (receipt.subsequence (refinement index)))
                wave)
              time) := by
      filter_upwards [retainedEventually] with index waveMem
      change
        puncturedCanonicalCriticalTrajectory
            lineage ν θ θLtOne criticalMargin
            requestedTime requestedTimePos
            (receipt.subsequence (refinement index))
            time.1 wave =
          fixedWaveHeatDuhamelValue
            requestedTime ν.coeff wave
            (puncturedCanonicalInitialState lineage
              (receipt.subsequence (refinement index)) wave)
            (transverseSpaceTimeNonlinearRow
              (puncturedCanonicalCriticalTransverseSpaceTimePath
                lineage ν θ requestedTime θLtOne criticalMargin
                requestedTimePos
                (receipt.subsequence (refinement index)))
              wave)
            time
      exact
        puncturedCanonicalCriticalTrajectory_eq_fixedWaveHeatDuhamelValue
          lineage ν θ requestedTime θLtOne criticalMargin
          requestedTimePos
          (receipt.subsequence (refinement index))
          wave waveMem time
    exact
      tendsto_nhds_unique observedValueTendsto
        (duhamelTendsto.congr' finiteMildEventually.symm)
  exact
    ⟨
      { initialLimit := initialLimit
        initial_tendsto := by
          convert initialTendsto using 1
          all_goals rfl
        rowPath := rowPath
        row_represents := rowRepresents
        mild_identity := mildIdentity }⟩

/-! ## Whole forcing receipt with every nonzero mild row -/

/--
One source-generated infinite critical state whose actual whole
`L²_t H⁻¹_x` nonlinear forcing and every nonzero continuous Fourier-row
mild law live on the same receipt.

The selected compact refinement and its auxiliary uniform limit are
internal to `fixedWaveMild`; no subsequence, initial trace, target
trajectory, terminal cutoff, or tail-silence witness is supplied by a
caller.
-/
structure InfiniteMildDuhamelForcingReceipt
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
    extends
      NonlinearNegativeOneForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos where
  initialState : ComplexVorticityHilbertState
  initial_tendsto :
    Tendsto
      (puncturedCanonicalInitialState lineage)
      atTop (𝓝 initialState)
  rowPath :
    ∀ wave : IntegerWavevector,
      wave ≠ 0 →
        BoundedContinuousFunction
          (Icc (0 : ℝ) requestedTime)
          ComplexCoordinateVector
  row_represents :
    ∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0),
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        rowPath wave waveNe time =
          fixedWaveSpaceTimeRestriction
            requestedTime wave stateLimit time
  nonlinearL2_represents :
    ∀ (wave : IntegerWavevector) (_waveNe : wave ≠ 0),
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        NonlinearNegativeOneForcingReceipt.fixedWaveNonlinearL2
            toNonlinearNegativeOneForcingReceipt wave time =
          transverseSpaceTimeNonlinearRow
            transverseLimit wave time
  mild_identity :
    ∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0)
      (time : Icc (0 : ℝ) requestedTime),
      rowPath wave waveNe time =
        fixedWaveHeatDuhamelValue
          requestedTime ν.coeff wave
          (initialState wave)
          (transverseSpaceTimeNonlinearRow
            transverseLimit wave)
          time

/--
The source lineage generates one whole forcing receipt together with
continuous mild/Duhamel representatives for all of its nonzero Fourier
rows.  Each row is driven by the same transverse nonlinear state whose
unweighted realization is already recorded by
`negativeOneForcing_unweighted_row_ae`.
-/
noncomputable def
    GeneratedIntegerShellInfiniteLineage.generates_infiniteMildDuhamelForcing
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
    InfiniteMildDuhamelForcingReceipt
      lineage ν θ requestedTime θLtOne criticalMargin
      requestedTimePos := by
  let forcingReceipt :=
    GeneratedIntegerShellInfiniteLineage.generates_nonlinearNegativeOneForcing
      lineage ν θ requestedTime θLtOne criticalMargin
      requestedTimePos
  let initialWitness :=
    endpointHilbertState_puncturedFrequencyCube_tendsto_limit
      lineage ν θ criticalMargin
  let initialState : ComplexVorticityHilbertState :=
    Classical.choose initialWitness
  have initialTendsto :
      Tendsto
        (puncturedCanonicalInitialState lineage)
        atTop (𝓝 initialState) := by
    have selected :=
      (Classical.choose_spec initialWitness).2
    convert selected using 1
    all_goals rfl
  let fixedWaveData :
      ∀ wave : IntegerWavevector,
        wave ≠ 0 →
          FixedWaveContinuousMildData
            requestedTime ν.coeff wave
            (puncturedCanonicalInitialState lineage)
            forcingReceipt.stateLimit
            (transverseSpaceTimeNonlinearRow
              forcingReceipt.transverseLimit wave) :=
    fun wave waveNe =>
      Classical.choice
        (ClosedNonlinearWeakLimitReceipt.exists_fixedWaveContinuousMildData
          lineage ν θ requestedTime θLtOne criticalMargin
          requestedTimePos
          forcingReceipt.toCriticalSerrinWeakLimitReceipt.toClosedNonlinearWeakLimitReceipt
          wave waveNe)
  have fixedWaveInitialEq :
      ∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0),
        (fixedWaveData wave waveNe).initialLimit =
          initialState := by
    intro wave waveNe
    exact
      tendsto_nhds_unique
        (fixedWaveData wave waveNe).initial_tendsto
        initialTendsto
  exact
    { toNonlinearNegativeOneForcingReceipt := forcingReceipt
      initialState := initialState
      initial_tendsto := initialTendsto
      rowPath := fun wave waveNe =>
        (fixedWaveData wave waveNe).rowPath
      row_represents := by
        intro wave waveNe
        exact (fixedWaveData wave waveNe).row_represents
      nonlinearL2_represents := by
        intro wave waveNe
        exact
          NonlinearNegativeOneForcingReceipt.fixedWaveNonlinearL2_coeFn
            forcingReceipt wave waveNe
      mild_identity := by
        intro wave waveNe time
        have identity :=
          (fixedWaveData wave waveNe).mild_identity time
        rw [fixedWaveInitialEq wave waveNe] at identity
        exact identity }

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
end NavierStokes
end SaturationMonoid
