import H0mework.NavierStokes.ShellSources.WholeContinuousMild

/-!
# Domain-generic whole continuous mild assembly

This module isolates the whole-carrier analytic assembly from the integer
shell lineage which first produced it.  The input contains only one positive
time interval, one initial Hilbert state, one whole weak state, one whole
negative-one forcing, and the exact nonzero Fourier-row laws relating them.

No lineage, critical margin, subsequence, support coverage, cutoff, or target
continuation datum occurs in the input.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeContinuousMildAssembly

open scoped BigOperators ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellNonlinearNegativeOneForcing
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildPhysicalLimit
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCoordinateParseval

noncomputable section

/--
The exact data needed to assemble continuous nonzero Fourier rows into one
whole mild path.

The nonlinear row is retained explicitly: its equality with the weighted
whole forcing is what makes the parabolic estimate a faithful write-back,
rather than a free rowwise majorant.
-/
structure WholeMildAssemblyInput
    (ν : Viscosity)
    (requestedTime : ℝ) where
  time_pos : 0 < requestedTime
  initialState : ComplexVorticityHilbertState
  stateLimit : SpaceTimeState requestedTime
  negativeOneForcing : SpaceTimeState requestedTime
  nonlinearRow :
    ∀ wave : IntegerWavevector,
      wave ≠ 0 → NonlinearRowSpaceTimeState requestedTime
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
  forcing_unweighted_row_ae :
    ∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0),
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        (Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
            (negativeOneForcing time) wave =
          nonlinearRow wave waveNe time
  row_mild_identity :
    ∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0)
      (time : Icc (0 : ℝ) requestedTime),
      rowPath wave waveNe time =
        fixedWaveHeatDuhamelValue
          requestedTime ν.coeff wave
          (initialState wave)
          (nonlinearRow wave waveNe)
          time
  stateLimit_zero_row :
    fixedWaveSpaceTimeRestriction
        requestedTime 0 stateLimit =
      0
  initialState_zero_row :
    initialState 0 = 0

/-- The actual negative-one forcing convolved at one wave and one time. -/
def assemblyWeightedDuhamelAt
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    ComplexCoordinateVector :=
  fixedL2ScalarL2IntegralCLM requestedTime
    (weightedCausalHeatKernelL2
      requestedTime ν.coeff ν.coeff_pos wave waveNe time)
    (fixedWaveSpaceTimeRestriction requestedTime wave
      input.negativeOneForcing)

theorem assemblyWeightedDuhamelAt_norm_sq_le
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    ‖assemblyWeightedDuhamelAt input wave waveNe time‖ ^ 2 ≤
      (2 * ν.coeff)⁻¹ *
        ‖fixedWaveSpaceTimeRestriction requestedTime wave
          input.negativeOneForcing‖ ^ 2 := by
  exact
    fixedL2ScalarL2IntegralCLM_weightedCausalHeatKernel_norm_sq_le
      requestedTime ν.coeff ν.coeff_pos wave waveNe time
      (fixedWaveSpaceTimeRestriction requestedTime wave
        input.negativeOneForcing)

/--
The weighted whole forcing recovers the exact nonlinear row appearing in
the rowwise mild law.
-/
theorem assemblyWeightedDuhamelAt_eq_nonlinear_integral
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    assemblyWeightedDuhamelAt input wave waveNe time =
      ∫ earlier in Iic time,
        finiteStateVorticityHeatMultiplier
            ν.coeff (time.1 - earlier.1) wave •
          input.nonlinearRow wave waveNe earlier
        ∂(commonTimeMeasure requestedTime) := by
  let kernel :=
    weightedCausalHeatKernelL2
      requestedTime ν.coeff ν.coeff_pos wave waveNe time
  let forcingRow :=
    fixedWaveSpaceTimeRestriction requestedTime wave
      input.negativeOneForcing
  have kernelAE :
      ⇑kernel =ᵐ[commonTimeMeasure requestedTime]
        weightedCausalHeatKernelFunction
          requestedTime ν.coeff wave time := by
    dsimp [kernel, weightedCausalHeatKernelL2]
    exact MemLp.coeFn_toLp _
  have forcingRowAE :
      ∀ᵐ earlier ∂(commonTimeMeasure requestedTime),
        forcingRow earlier =
          (input.negativeOneForcing earlier) wave :=
    fixedWaveSpaceTimeRestriction_coeFn
      requestedTime wave input.negativeOneForcing
  have productAE :
      ⇑(kernel • forcingRow :
          MeasureTheory.Lp ComplexCoordinateVector 1
            (commonTimeMeasure requestedTime)) =ᵐ[
          commonTimeMeasure requestedTime]
        ⇑kernel • ⇑forcingRow :=
    MeasureTheory.Lp.coeFn_lpSMul kernel forcingRow
  have nonlinearAE :=
    input.forcing_unweighted_row_ae wave waveNe
  change
    (MeasureTheory.L1.integralCLM' ℂ)
        (kernel • forcingRow) = _
  rw [← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  rw [← MeasureTheory.integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards [productAE, kernelAE, forcingRowAE, nonlinearAE] with
    earlier productEq kernelEq forcingEq nonlinearEq
  rw [productEq]
  change
    kernel earlier • forcingRow earlier =
      (Iic time).indicator
        (fun actual =>
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - actual.1) wave •
            input.nonlinearRow wave waveNe actual)
        earlier
  rw [kernelEq, forcingEq]
  by_cases earlierLe : earlier ≤ time
  · simp only [weightedCausalHeatKernelFunction,
      Set.indicator_apply, Set.mem_Iic, earlierLe, if_true]
    have scalarActionEq :
        ((Real.sqrt (integerWaveViscousMultiplier wave) *
              finiteStateVorticityHeatMultiplier
                ν.coeff (time.1 - earlier.1) wave : ℝ) : ℂ) •
            (input.negativeOneForcing earlier) wave =
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - earlier.1) wave •
            ((Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
              (input.negativeOneForcing earlier) wave) := by
      ext coordinate
      simp [Complex.real_smul]
      ring
    rw [scalarActionEq, nonlinearEq]
  · simp only [weightedCausalHeatKernelFunction,
      Set.indicator_apply, Set.mem_Iic, earlierLe, if_false]
    simp

theorem rowPath_eq_heat_add_assemblyWeightedDuhamel
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    input.rowPath wave waveNe time =
      finiteStateVorticityHeatMultiplier
          ν.coeff time.1 wave • input.initialState wave +
        assemblyWeightedDuhamelAt input wave waveNe time := by
  rw [input.row_mild_identity wave waveNe time]
  unfold fixedWaveHeatDuhamelValue
  rw [assemblyWeightedDuhamelAt_eq_nonlinear_integral
    input wave waveNe time]

/-! ## Coordinatewise table and its summable majorant -/

def assemblyMildCoefficient
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (time : Icc (0 : ℝ) requestedTime)
    (wave : IntegerWavevector) :
    ComplexCoordinateVector :=
  if waveNe : wave ≠ 0
  then input.rowPath wave waveNe time
  else 0

@[simp] theorem assemblyMildCoefficient_zero
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (time : Icc (0 : ℝ) requestedTime) :
    assemblyMildCoefficient input time 0 = 0 := by
  simp [assemblyMildCoefficient]

theorem assemblyMildCoefficient_eq_rowPath
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (time : Icc (0 : ℝ) requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    assemblyMildCoefficient input time wave =
      input.rowPath wave waveNe time := by
  simp only [assemblyMildCoefficient, dif_pos waveNe]

def assemblyMildCoefficientSqMajorant
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (wave : IntegerWavevector) : ℝ :=
  2 * ‖input.initialState wave‖ ^ 2 +
    2 * (2 * ν.coeff)⁻¹ *
      ‖fixedWaveSpaceTimeRestriction requestedTime wave
        input.negativeOneForcing‖ ^ 2

theorem assemblyMildCoefficientSqMajorant_nonneg
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (wave : IntegerWavevector) :
    0 ≤ assemblyMildCoefficientSqMajorant input wave := by
  unfold assemblyMildCoefficientSqMajorant
  apply add_nonneg
  · exact mul_nonneg (by norm_num) (sq_nonneg _)
  · exact
      mul_nonneg
        (mul_nonneg (by norm_num)
          (inv_nonneg.mpr
            (mul_nonneg (by norm_num) ν.coeff_pos.le)))
        (sq_nonneg _)

theorem assemblyMildCoefficient_norm_sq_le_majorant
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (time : Icc (0 : ℝ) requestedTime)
    (wave : IntegerWavevector) :
    ‖assemblyMildCoefficient input time wave‖ ^ 2 ≤
      assemblyMildCoefficientSqMajorant input wave := by
  by_cases waveNe : wave ≠ 0
  · rw [assemblyMildCoefficient_eq_rowPath input time wave waveNe,
      rowPath_eq_heat_add_assemblyWeightedDuhamel
        input wave waveNe time]
    let heatRow :=
      finiteStateVorticityHeatMultiplier
        ν.coeff time.1 wave • input.initialState wave
    let duhamelRow :=
      assemblyWeightedDuhamelAt input wave waveNe time
    have heatMultiplierLe :
        finiteStateVorticityHeatMultiplier
            ν.coeff time.1 wave ≤ 1 :=
      finiteStateVorticityHeatMultiplier_le_one
        ν.coeff_pos.le time.2.1 wave
    have heatRowNormLe :
        ‖heatRow‖ ≤ ‖input.initialState wave‖ := by
      dsimp [heatRow]
      rw [norm_smul, Real.norm_of_nonneg
        (finiteStateVorticityHeatMultiplier_nonneg
          ν.coeff time.1 wave)]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right heatMultiplierLe (norm_nonneg _)
    have rowNormLe :
        ‖heatRow + duhamelRow‖ ≤
          ‖input.initialState wave‖ + ‖duhamelRow‖ :=
      (norm_add_le heatRow duhamelRow).trans
        (add_le_add heatRowNormLe (le_refl _))
    have rowSqLe :
        ‖heatRow + duhamelRow‖ ^ 2 ≤
          (‖input.initialState wave‖ + ‖duhamelRow‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 rowNormLe
    have sumSqLe :
        (‖input.initialState wave‖ + ‖duhamelRow‖) ^ 2 ≤
          2 * ‖input.initialState wave‖ ^ 2 +
            2 * ‖duhamelRow‖ ^ 2 := by
      nlinarith [sq_nonneg
        (‖input.initialState wave‖ - ‖duhamelRow‖)]
    calc
      ‖heatRow + duhamelRow‖ ^ 2 ≤
          2 * ‖input.initialState wave‖ ^ 2 +
            2 * ‖duhamelRow‖ ^ 2 :=
        rowSqLe.trans sumSqLe
      _ ≤
          2 * ‖input.initialState wave‖ ^ 2 +
            2 * ((2 * ν.coeff)⁻¹ *
              ‖fixedWaveSpaceTimeRestriction requestedTime wave
                input.negativeOneForcing‖ ^ 2) := by
        gcongr
        exact assemblyWeightedDuhamelAt_norm_sq_le
          input wave waveNe time
      _ = assemblyMildCoefficientSqMajorant input wave := by
        unfold assemblyMildCoefficientSqMajorant
        ring
  · simpa [assemblyMildCoefficient, waveNe] using
      assemblyMildCoefficientSqMajorant_nonneg input wave

theorem assemblyMildCoefficient_continuous
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (wave : IntegerWavevector) :
    Continuous (fun time => assemblyMildCoefficient input time wave) := by
  by_cases waveNe : wave ≠ 0
  · simpa only [assemblyMildCoefficient, dif_pos waveNe] using
      (input.rowPath wave waveNe).continuous
  · have waveZero : wave = 0 := not_ne_iff.mp waveNe
    subst wave
    simp only [assemblyMildCoefficient_zero]
    exact continuous_const

theorem assemblyMildCoefficientSqMajorant_summable
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime) :
    Summable (assemblyMildCoefficientSqMajorant input) := by
  have initialSummable :
      Summable fun wave : IntegerWavevector =>
        ‖input.initialState wave‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Memℓp.summable (by norm_num) input.initialState.2
  have forcingSummable :
      Summable fun wave : IntegerWavevector =>
        ‖fixedWaveSpaceTimeRestriction requestedTime wave
          input.negativeOneForcing‖ ^ 2 :=
    summable_fixedWaveSpaceTimeRestriction_norm_sq
      requestedTime input.negativeOneForcing
  exact
    ((initialSummable.mul_left 2).add
      (forcingSummable.mul_left
        (2 * (2 * ν.coeff)⁻¹))).congr fun wave => by
          unfold assemblyMildCoefficientSqMajorant
          ring

theorem tsum_assemblyMildCoefficientSqMajorant
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime) :
    (∑' wave : IntegerWavevector,
        assemblyMildCoefficientSqMajorant input wave) =
      2 * ‖input.initialState‖ ^ 2 +
        2 * (2 * ν.coeff)⁻¹ *
          ‖input.negativeOneForcing‖ ^ 2 := by
  have initialSummable :
      Summable fun wave : IntegerWavevector =>
        ‖input.initialState wave‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Memℓp.summable (by norm_num) input.initialState.2
  have forcingSummable :
      Summable fun wave : IntegerWavevector =>
        ‖fixedWaveSpaceTimeRestriction requestedTime wave
          input.negativeOneForcing‖ ^ 2 :=
    summable_fixedWaveSpaceTimeRestriction_norm_sq
      requestedTime input.negativeOneForcing
  rw [show
    assemblyMildCoefficientSqMajorant input =
      fun wave =>
        2 * ‖input.initialState wave‖ ^ 2 +
          (2 * (2 * ν.coeff)⁻¹) *
            ‖fixedWaveSpaceTimeRestriction requestedTime wave
              input.negativeOneForcing‖ ^ 2 by
      funext wave
      unfold assemblyMildCoefficientSqMajorant
      ring]
  rw [(initialSummable.mul_left 2).tsum_add
    (forcingSummable.mul_left (2 * (2 * ν.coeff)⁻¹)),
    tsum_mul_left, tsum_mul_left]
  have initialTsum :
      (∑' wave : IntegerWavevector,
          ‖input.initialState wave‖ ^ 2) =
        ‖input.initialState‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.norm_rpow_eq_tsum
        (p := (2 : ℝ≥0∞)) (by norm_num)
        input.initialState).symm
  rw [initialTsum,
    tsum_fixedWaveSpaceTimeRestriction_norm_sq
      requestedTime input.negativeOneForcing]

/-! ## Whole-state assembly from the coordinate table -/

def assemblyWholeMildState
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (time : Icc (0 : ℝ) requestedTime) :
    ComplexVorticityHilbertState :=
  ⟨assemblyMildCoefficient input time, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (assemblyMildCoefficientSqMajorant_summable input).of_nonneg_of_le
        (fun wave => sq_nonneg _)
        (fun wave =>
          assemblyMildCoefficient_norm_sq_le_majorant
            input time wave)⟩

@[simp] theorem assemblyWholeMildState_apply
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (time : Icc (0 : ℝ) requestedTime)
    (wave : IntegerWavevector) :
    assemblyWholeMildState input time wave =
      assemblyMildCoefficient input time wave :=
  rfl

theorem assemblyWholeMildState_norm_sq_le
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (time : Icc (0 : ℝ) requestedTime) :
    ‖assemblyWholeMildState input time‖ ^ 2 ≤
      2 * ‖input.initialState‖ ^ 2 +
        2 * (2 * ν.coeff)⁻¹ *
          ‖input.negativeOneForcing‖ ^ 2 := by
  rw [show
      ‖assemblyWholeMildState input time‖ ^ 2 =
        ∑' wave : IntegerWavevector,
          ‖assemblyMildCoefficient input time wave‖ ^ 2 by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      assemblyWholeMildState_apply] using
      lp.norm_rpow_eq_tsum
        (p := (2 : ℝ≥0∞)) (by norm_num)
        (assemblyWholeMildState input time)]
  calc
    (∑' wave : IntegerWavevector,
        ‖assemblyMildCoefficient input time wave‖ ^ 2) ≤
      ∑' wave : IntegerWavevector,
        assemblyMildCoefficientSqMajorant input wave := by
      exact
        Summable.tsum_le_tsum
          (fun wave =>
            assemblyMildCoefficient_norm_sq_le_majorant
              input time wave)
          (by
            have stateSummable :
                Summable fun wave : IntegerWavevector =>
                  ‖assemblyWholeMildState input time wave‖ ^ 2 := by
              simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
                Memℓp.summable (by norm_num)
                  (assemblyWholeMildState input time).2
            exact stateSummable.congr fun wave => by
              rw [assemblyWholeMildState_apply])
          (assemblyMildCoefficientSqMajorant_summable input)
    _ =
        2 * ‖input.initialState‖ ^ 2 +
          2 * (2 * ν.coeff)⁻¹ *
            ‖input.negativeOneForcing‖ ^ 2 :=
      tsum_assemblyMildCoefficientSqMajorant input

private theorem assemblyMildCoefficient_sub_norm_sq_le
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (firstTime secondTime : Icc (0 : ℝ) requestedTime)
    (wave : IntegerWavevector) :
    ‖assemblyMildCoefficient input firstTime wave -
        assemblyMildCoefficient input secondTime wave‖ ^ 2 ≤
      4 * assemblyMildCoefficientSqMajorant input wave := by
  have firstBound :=
    assemblyMildCoefficient_norm_sq_le_majorant
      input firstTime wave
  have secondBound :=
    assemblyMildCoefficient_norm_sq_le_majorant
      input secondTime wave
  have subBound :
      ‖assemblyMildCoefficient input firstTime wave -
          assemblyMildCoefficient input secondTime wave‖ ≤
        ‖assemblyMildCoefficient input firstTime wave‖ +
          ‖assemblyMildCoefficient input secondTime wave‖ :=
    norm_sub_le _ _
  have subSqBound :
      ‖assemblyMildCoefficient input firstTime wave -
          assemblyMildCoefficient input secondTime wave‖ ^ 2 ≤
        (‖assemblyMildCoefficient input firstTime wave‖ +
          ‖assemblyMildCoefficient input secondTime wave‖) ^ 2 :=
    (sq_le_sq₀
      (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 subBound
  nlinarith [sq_nonneg
    (‖assemblyMildCoefficient input firstTime wave‖ -
      ‖assemblyMildCoefficient input secondTime wave‖)]

theorem assemblyWholeMildState_continuous
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime) :
    Continuous (assemblyWholeMildState input) := by
  rw [continuous_iff_continuousAt]
  intro time
  rw [ContinuousAt]
  apply tendsto_sub_nhds_zero_iff.1
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have squareTendsto :
      Tendsto
        (fun approachingTime : Icc (0 : ℝ) requestedTime =>
          ∑' wave : IntegerWavevector,
            ‖assemblyMildCoefficient input approachingTime wave -
                assemblyMildCoefficient input time wave‖ ^ 2)
        (𝓝 time)
        (𝓝 0) := by
    convert
      tendsto_tsum_of_dominated_convergence
        ((assemblyMildCoefficientSqMajorant_summable input).mul_left 4)
        (fun wave => by
          have coefficientDifferenceContinuous :
              ContinuousAt
                (fun approachingTime =>
                  ‖assemblyMildCoefficient input approachingTime wave -
                    assemblyMildCoefficient input time wave‖ ^ 2)
                time :=
            ((assemblyMildCoefficient_continuous input wave).continuousAt.sub
              tendsto_const_nhds).norm.pow 2
          simpa only [ContinuousAt, sub_self, norm_zero,
            ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
            coefficientDifferenceContinuous)
        (Filter.Eventually.of_forall fun approachingTime wave =>
          (by
            rw [Real.norm_eq_abs,
              abs_of_nonneg (sq_nonneg
                ‖assemblyMildCoefficient input approachingTime wave -
                  assemblyMildCoefficient input time wave‖)]
            exact
              assemblyMildCoefficient_sub_norm_sq_le
                input approachingTime time wave))
      using 1
    all_goals simp
  have normSquareTendsto :
      Tendsto
        (fun approachingTime : Icc (0 : ℝ) requestedTime =>
          ‖assemblyWholeMildState input approachingTime -
              assemblyWholeMildState input time‖ ^ 2)
        (𝓝 time)
        (𝓝 0) := by
    convert squareTendsto using 1
    · funext approachingTime
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
        assemblyWholeMildState_apply, lp.coeFn_sub, Pi.sub_apply] using
        lp.norm_rpow_eq_tsum
          (p := (2 : ℝ≥0∞)) (by norm_num)
          (assemblyWholeMildState input approachingTime -
            assemblyWholeMildState input time)
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    normSquareTendsto.sqrt

def assemblyWholeMildPath
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) requestedTime)
      ComplexVorticityHilbertState :=
  BoundedContinuousFunction.mkOfCompact
    ⟨assemblyWholeMildState input,
      assemblyWholeMildState_continuous input⟩

@[simp] theorem assemblyWholeMildPath_apply
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (time : Icc (0 : ℝ) requestedTime) :
    assemblyWholeMildPath input time =
      assemblyWholeMildState input time :=
  rfl

theorem assemblyWholeMildPath_toLp_eq_stateLimit
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime) :
    BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ
        (assemblyWholeMildPath input) =
      input.stateLimit := by
  have rowsRepresent :
      ∀ wave : IntegerWavevector,
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          assemblyMildCoefficient input time wave =
            input.stateLimit time wave := by
    intro wave
    have restrictionAE :=
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave input.stateLimit
    by_cases waveNe : wave ≠ 0
    · filter_upwards [
        input.row_represents wave waveNe,
        restrictionAE] with time rowEq restrictionEq
      rw [assemblyMildCoefficient_eq_rowPath
        input time wave waveNe, rowEq, restrictionEq]
    · have waveZero : wave = 0 := not_ne_iff.mp waveNe
      subst wave
      have zeroRowAE :
          ∀ᵐ time ∂(commonTimeMeasure requestedTime),
            fixedWaveSpaceTimeRestriction
                requestedTime 0 input.stateLimit time =
              0 := by
        rw [input.stateLimit_zero_row]
        exact
          MeasureTheory.Lp.coeFn_zero
            ComplexCoordinateVector 2
            (commonTimeMeasure requestedTime)
      filter_upwards [restrictionAE, zeroRowAE] with
          time restrictionEq zeroEq
      rw [assemblyMildCoefficient_zero, ← restrictionEq, zeroEq]
  apply MeasureTheory.Lp.ext
  filter_upwards [
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ (assemblyWholeMildPath input),
    eventually_countable_forall.2 rowsRepresent] with
      time pathEq timeRows
  rw [pathEq]
  apply lp.ext
  funext wave
  exact timeRows wave

theorem assemblyWholeMildPath_mild_identity
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    assemblyWholeMildPath input time wave =
      finiteStateVorticityHeatMultiplier
          ν.coeff time.1 wave • input.initialState wave +
        assemblyWeightedDuhamelAt input wave waveNe time := by
  rw [assemblyWholeMildPath_apply, assemblyWholeMildState_apply,
    assemblyMildCoefficient_eq_rowPath input time wave waveNe]
  exact rowPath_eq_heat_add_assemblyWeightedDuhamel
    input wave waveNe time

@[simp] theorem assemblyWholeMildPath_zero_row
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (time : Icc (0 : ℝ) requestedTime) :
    assemblyWholeMildPath input time 0 = 0 := by
  rw [assemblyWholeMildPath_apply, assemblyWholeMildState_apply,
    assemblyMildCoefficient_zero]

theorem assemblyWholeMildPath_initial
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime) :
    assemblyWholeMildPath input
        ⟨0, ⟨le_rfl, input.time_pos.le⟩⟩ =
      input.initialState := by
  apply lp.ext
  funext wave
  by_cases waveNe : wave ≠ 0
  · rw [assemblyWholeMildPath_mild_identity
      input wave waveNe
      ⟨0, ⟨le_rfl, input.time_pos.le⟩⟩]
    rw [assemblyWeightedDuhamelAt_eq_nonlinear_integral
      input wave waveNe
      ⟨0, ⟨le_rfl, input.time_pos.le⟩⟩]
    have iicInitial :
        Iic
            (⟨0, ⟨le_rfl, input.time_pos.le⟩⟩ :
              Icc (0 : ℝ) requestedTime) =
          {⟨0, ⟨le_rfl, input.time_pos.le⟩⟩} := by
      ext earlier
      simp only [Set.mem_Iic, Set.mem_singleton_iff]
      constructor
      · intro earlierLe
        apply Subtype.ext
        exact le_antisymm earlierLe earlier.property.1
      · intro earlierEq
        subst earlier
        exact le_rfl
    have singletonMeasureZero :
        commonTimeMeasure requestedTime
            {⟨0, ⟨le_rfl, input.time_pos.le⟩⟩} =
          0 := by
      change
        Measure.comap
            (Subtype.val :
              Icc (0 : ℝ) requestedTime → ℝ)
            (volume.restrict (Icc (0 : ℝ) requestedTime))
            {⟨0, ⟨le_rfl, input.time_pos.le⟩⟩} =
          0
      rw [comap_subtype_coe_apply measurableSet_Icc]
      simp
    have iicMeasureZero :
        commonTimeMeasure requestedTime
            (Iic
              (⟨0, ⟨le_rfl, input.time_pos.le⟩⟩ :
                Icc (0 : ℝ) requestedTime)) =
          0 := by
      rw [iicInitial]
      exact singletonMeasureZero
    rw [MeasureTheory.setIntegral_measure_zero _ iicMeasureZero]
    simp [finiteStateVorticityHeatMultiplier]
  · have waveZero : wave = 0 := not_ne_iff.mp waveNe
    subst wave
    rw [assemblyWholeMildPath_apply, assemblyWholeMildState_apply,
      assemblyMildCoefficient_zero, input.initialState_zero_row]

theorem assemblyWholeMildPath_norm_sq_le
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime)
    (time : Icc (0 : ℝ) requestedTime) :
    ‖assemblyWholeMildPath input time‖ ^ 2 ≤
      2 * ‖input.initialState‖ ^ 2 +
        2 * (2 * ν.coeff)⁻¹ *
          ‖input.negativeOneForcing‖ ^ 2 := by
  rw [assemblyWholeMildPath_apply]
  exact assemblyWholeMildState_norm_sq_le input time

/--
The complete output of the domain-generic whole mild assembly.
-/
structure WholeContinuousMildAssembly
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime) where
  wholePath :
    BoundedContinuousFunction
      (Icc (0 : ℝ) requestedTime)
      ComplexVorticityHilbertState
  wholePath_toLp_eq_stateLimit :
    BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ wholePath =
      input.stateLimit
  wholePath_mild_identity :
    ∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0)
      (time : Icc (0 : ℝ) requestedTime),
      wholePath time wave =
        finiteStateVorticityHeatMultiplier
            ν.coeff time.1 wave • input.initialState wave +
          assemblyWeightedDuhamelAt input wave waveNe time
  wholePath_initial :
    wholePath
        ⟨0, ⟨le_rfl, input.time_pos.le⟩⟩ =
      input.initialState
  wholePath_norm_sq_le :
    ∀ time : Icc (0 : ℝ) requestedTime,
      ‖wholePath time‖ ^ 2 ≤
        2 * ‖input.initialState‖ ^ 2 +
          2 * (2 * ν.coeff)⁻¹ *
            ‖input.negativeOneForcing‖ ^ 2

/--
Assemble the domain-generic input into one faithful whole continuous mild
path.  All choices are determined by the input row paths and whole forcing.
-/
noncomputable def WholeMildAssemblyInput.assemble
    {ν : Viscosity}
    {requestedTime : ℝ}
    (input : WholeMildAssemblyInput ν requestedTime) :
    WholeContinuousMildAssembly input :=
  { wholePath := assemblyWholeMildPath input
    wholePath_toLp_eq_stateLimit :=
      assemblyWholeMildPath_toLp_eq_stateLimit input
    wholePath_mild_identity :=
      assemblyWholeMildPath_mild_identity input
    wholePath_initial :=
      assemblyWholeMildPath_initial input
    wholePath_norm_sq_le :=
      assemblyWholeMildPath_norm_sq_le input }

end

end ThreeDimensionalVorticityCoefficientWholeContinuousMildAssembly
end NavierStokes
end SaturationMonoid
