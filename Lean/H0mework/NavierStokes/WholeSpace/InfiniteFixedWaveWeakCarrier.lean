import H0mework.NavierStokes.GeneratedPaths.InfiniteNonlinearRowLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Infinite fixed-wave weak carrier

This module places the complete fixed-output Fourier nonlinearity on the same
space-time carrier as the whole vorticity state.  It proves continuity of the
distributional fixed-wave action and reconstructs the infinite nonlinear row
from every actual finite-support Galerkin trajectory before deriving its weak
identity.  No target limit, support coverage, or continuation conclusion is
stored in the theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier

open scoped ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow

noncomputable section

def fixedLpScalarSmulCLM
    {p q r : ℝ≥0∞}
    [ENNReal.HolderTriple p q r]
    [Fact (1 ≤ p)]
    [Fact (1 ≤ q)]
    [Fact (1 ≤ r)]
    (requestedTime : ℝ)
    (scalar : MeasureTheory.Lp ℂ p
      (commonTimeMeasure requestedTime)) :
    MeasureTheory.Lp ComplexCoordinateVector q
        (commonTimeMeasure requestedTime) →L[ℂ]
      MeasureTheory.Lp ComplexCoordinateVector r
        (commonTimeMeasure requestedTime) :=
  LinearMap.mkContinuous
    { toFun := fun vector => scalar • vector
      map_add' := fun left right => by
        exact MeasureTheory.Lp.add_smul scalar left right
      map_smul' := fun coefficient vector => by
        exact
          (MeasureTheory.Lp.smul_comm
            coefficient scalar vector).symm }
    ‖scalar‖
    (fun vector => MeasureTheory.Lp.norm_smul_le scalar vector)

def fixedL2ScalarL2IntegralCLM
    (requestedTime : ℝ)
    (scalar : MeasureTheory.Lp ℂ 2
      (commonTimeMeasure requestedTime)) :
    MeasureTheory.Lp ComplexCoordinateVector 2
        (commonTimeMeasure requestedTime) →L[ℂ]
      ComplexCoordinateVector :=
  (MeasureTheory.L1.integralCLM' ℂ).comp
    (fixedLpScalarSmulCLM
      (p := 2) (q := 2) (r := 1)
      requestedTime scalar)

def fixedLInfScalarL1IntegralCLM
    (requestedTime : ℝ)
    (scalar : MeasureTheory.Lp ℂ ∞
      (commonTimeMeasure requestedTime)) :
    MeasureTheory.Lp ComplexCoordinateVector 1
        (commonTimeMeasure requestedTime) →L[ℂ]
      ComplexCoordinateVector :=
  (MeasureTheory.L1.integralCLM' ℂ).comp
    (fixedLpScalarSmulCLM
      (p := ∞) (q := 1) (r := 1)
      requestedTime scalar)

def restrictedScalarBoundedPath
    (requestedTime : ℝ)
    (function : ℝ → ℂ)
    (functionContinuous :
      ContinuousOn function (Icc (0 : ℝ) requestedTime)) :
    BoundedContinuousFunction (Icc (0 : ℝ) requestedTime) ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun time => function time.1,
      functionContinuous.restrict⟩

def restrictedScalarL2
    (requestedTime : ℝ)
    (function : ℝ → ℂ)
    (functionContinuous :
      ContinuousOn function (Icc (0 : ℝ) requestedTime)) :
    MeasureTheory.Lp ℂ 2
      (commonTimeMeasure requestedTime) :=
  BoundedContinuousFunction.toLp 2
    (commonTimeMeasure requestedTime) ℂ
    (restrictedScalarBoundedPath
      requestedTime function functionContinuous)

def restrictedScalarLInf
    (requestedTime : ℝ)
    (function : ℝ → ℂ)
    (functionContinuous :
      ContinuousOn function (Icc (0 : ℝ) requestedTime)) :
    MeasureTheory.Lp ℂ ∞
      (commonTimeMeasure requestedTime) :=
  BoundedContinuousFunction.toLp ∞
    (commonTimeMeasure requestedTime) ℂ
    (restrictedScalarBoundedPath
      requestedTime function functionContinuous)

def fixedWaveWeakAction
    (requestedTime ν : ℝ)
    (wave : IntegerWavevector)
    (testL2 testDerivativeL2 :
      MeasureTheory.Lp ℂ 2
        (commonTimeMeasure requestedTime))
    (testLInf :
      MeasureTheory.Lp ℂ ∞
        (commonTimeMeasure requestedTime))
    (state : SpaceTimeState requestedTime)
    (nonlinear :
      NonlinearRowSpaceTimeState requestedTime) :
    ComplexCoordinateVector :=
  fixedL2ScalarL2IntegralCLM
      requestedTime testDerivativeL2
      (fixedWaveSpaceTimeRestriction
        requestedTime wave state) +
    fixedLInfScalarL1IntegralCLM
      requestedTime testLInf nonlinear -
    fixedL2ScalarL2IntegralCLM
      requestedTime testL2
      (((ν * integerWaveViscousMultiplier wave : ℝ) : ℂ) •
        fixedWaveSpaceTimeRestriction
          requestedTime wave state)

theorem tendsto_fixedWaveWeakAction
    {ι : Type*}
    {filter : Filter ι}
    (requestedTime ν : ℝ)
    (wave : IntegerWavevector)
    (testL2 testDerivativeL2 :
      MeasureTheory.Lp ℂ 2
        (commonTimeMeasure requestedTime))
    (testLInf :
      MeasureTheory.Lp ℂ ∞
        (commonTimeMeasure requestedTime))
    (stateSequence : ι → SpaceTimeState requestedTime)
    (nonlinearSequence :
      ι → NonlinearRowSpaceTimeState requestedTime)
    (stateLimit : SpaceTimeState requestedTime)
    (nonlinearLimit :
      NonlinearRowSpaceTimeState requestedTime)
    (stateTendsto : Tendsto stateSequence filter (𝓝 stateLimit))
    (nonlinearTendsto :
      Tendsto nonlinearSequence filter (𝓝 nonlinearLimit)) :
    Tendsto
      (fun index =>
        fixedWaveWeakAction requestedTime ν wave
          testL2 testDerivativeL2 testLInf
          (stateSequence index)
          (nonlinearSequence index))
      filter
      (𝓝
        (fixedWaveWeakAction requestedTime ν wave
          testL2 testDerivativeL2 testLInf
          stateLimit nonlinearLimit)) := by
  have rowTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction requestedTime wave
            (stateSequence index))
        filter
        (𝓝
          (fixedWaveSpaceTimeRestriction
            requestedTime wave stateLimit)) :=
    ((fixedWaveSpaceTimeRestriction
      requestedTime wave).continuous.tendsto stateLimit).comp
      stateTendsto
  have derivativeActionTendsto :=
    ((fixedL2ScalarL2IntegralCLM
      requestedTime testDerivativeL2).continuous.tendsto
        (fixedWaveSpaceTimeRestriction
          requestedTime wave stateLimit)).comp rowTendsto
  have nonlinearActionTendsto :=
    ((fixedLInfScalarL1IntegralCLM
      requestedTime testLInf).continuous.tendsto
        nonlinearLimit).comp nonlinearTendsto
  have viscousActionTendsto :=
    ((fixedL2ScalarL2IntegralCLM
      requestedTime testL2).continuous.tendsto
        (((ν * integerWaveViscousMultiplier wave : ℝ) : ℂ) •
          fixedWaveSpaceTimeRestriction
            requestedTime wave stateLimit)).comp
      (rowTendsto.const_smul
        ((ν * integerWaveViscousMultiplier wave : ℝ) : ℂ))
  unfold fixedWaveWeakAction
  exact
    (derivativeActionTendsto.add nonlinearActionTendsto).sub
      viscousActionTendsto

/-! ## Whole trajectory carriers independent of finite supports -/

def wholeTrajectoryBoundedPath
    (requestedTime : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime)) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) requestedTime)
      ComplexVorticityHilbertState :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun time => trajectory time.1,
      trajectoryContinuous.restrict⟩

def wholeTrajectorySpaceTimePath
    (requestedTime : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime)) :
    SpaceTimeState requestedTime :=
  BoundedContinuousFunction.toLp 2
    (commonTimeMeasure requestedTime) ℂ
    (wholeTrajectoryBoundedPath
      requestedTime trajectory trajectoryContinuous)

def wholeTransverseTrajectory
    (requestedTime : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.WholeStateTransverse
          (trajectory t)) :
    Icc (0 : ℝ) requestedTime →
      ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.WholeTransverseVorticityState :=
  fun time =>
    ⟨trajectory time.1,
      trajectoryTransverse time.1 time.2⟩

theorem wholeTransverseTrajectory_continuous
    (requestedTime : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime))
    (trajectoryTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.WholeStateTransverse
          (trajectory t)) :
    Continuous
      (wholeTransverseTrajectory
        requestedTime trajectory trajectoryTransverse) := by
  exact
    trajectoryContinuous.restrict.subtype_mk
      (fun time =>
        trajectoryTransverse time.1 time.2)

def wholeNonlinearRowBoundedPath
    (requestedTime : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime))
    (trajectoryTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.WholeStateTransverse
          (trajectory t))
    (output : IntegerWavevector) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) requestedTime)
      ComplexCoordinateVector :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun time =>
        ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
          (trajectory time.1) output,
      (wholeStateVorticityNonlinearCoefficientAt_comp_continuousOn
        trajectory output 0 requestedTime trajectoryContinuous
        trajectoryTransverse).restrict⟩

def wholeNonlinearRowSpaceTimePath
    (requestedTime : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime))
    (trajectoryTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.WholeStateTransverse
          (trajectory t))
    (output : IntegerWavevector) :
    NonlinearRowSpaceTimeState requestedTime :=
  BoundedContinuousFunction.toLp 1
    (commonTimeMeasure requestedTime) ℂ
    (wholeNonlinearRowBoundedPath
      requestedTime trajectory trajectoryContinuous
      trajectoryTransverse output)

theorem wholeTrajectorySpaceTimePath_norm_sq_eq_intervalIntegral
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime)) :
    ‖wholeTrajectorySpaceTimePath
        requestedTime trajectory trajectoryContinuous‖ ^ 2 =
      ∫ t in (0 : ℝ)..requestedTime,
        ‖trajectory t‖ ^ 2 := by
  rw [spaceTime_norm_sq_eq_integral]
  have trajectoryAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (wholeTrajectoryBoundedPath
        requestedTime trajectory trajectoryContinuous)
  calc
    (∫ time,
        ‖wholeTrajectorySpaceTimePath
          requestedTime trajectory trajectoryContinuous time‖ ^ 2
        ∂(commonTimeMeasure requestedTime)) =
        ∫ time : Icc (0 : ℝ) requestedTime,
          ‖trajectory time.1‖ ^ 2
        ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards [trajectoryAE] with time trajectoryEq
      change
        ‖((BoundedContinuousFunction.toLp 2
            (commonTimeMeasure requestedTime) ℂ)
          (wholeTrajectoryBoundedPath
            requestedTime trajectory trajectoryContinuous)) time‖ ^ 2 =
          _
      rw [trajectoryEq]
      rfl
    _ =
        ∫ t in (0 : ℝ)..requestedTime,
          ‖trajectory t‖ ^ 2 := by
      exact
        commonTime_integral_eq_intervalIntegral
          requestedTime requestedTimePos.le
          (fun t => ‖trajectory t‖ ^ 2)

theorem wholeTrajectorySpaceTimePath_sub_norm_sq_eq_intervalIntegral
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (left right : ℝ → ComplexVorticityHilbertState)
    (leftContinuous :
      ContinuousOn left (Icc (0 : ℝ) requestedTime))
    (rightContinuous :
      ContinuousOn right (Icc (0 : ℝ) requestedTime)) :
    ‖wholeTrajectorySpaceTimePath
          requestedTime left leftContinuous -
        wholeTrajectorySpaceTimePath
          requestedTime right rightContinuous‖ ^ 2 =
      ∫ t in (0 : ℝ)..requestedTime,
        ‖left t - right t‖ ^ 2 := by
  rw [spaceTime_norm_sq_eq_integral]
  have leftAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (wholeTrajectoryBoundedPath
        requestedTime left leftContinuous)
  have rightAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (wholeTrajectoryBoundedPath
        requestedTime right rightContinuous)
  have subAE :=
    MeasureTheory.Lp.coeFn_sub
      (wholeTrajectorySpaceTimePath
        requestedTime left leftContinuous)
      (wholeTrajectorySpaceTimePath
        requestedTime right rightContinuous)
  calc
    (∫ time,
        ‖(wholeTrajectorySpaceTimePath
              requestedTime left leftContinuous -
            wholeTrajectorySpaceTimePath
              requestedTime right rightContinuous) time‖ ^ 2
        ∂(commonTimeMeasure requestedTime)) =
        ∫ time : Icc (0 : ℝ) requestedTime,
          ‖left time.1 - right time.1‖ ^ 2
        ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards [subAE, leftAE, rightAE] with
        time subEq leftEq rightEq
      rw [subEq]
      change
        ‖((BoundedContinuousFunction.toLp 2
              (commonTimeMeasure requestedTime) ℂ)
              (wholeTrajectoryBoundedPath
                requestedTime left leftContinuous)) time -
            ((BoundedContinuousFunction.toLp 2
              (commonTimeMeasure requestedTime) ℂ)
              (wholeTrajectoryBoundedPath
                requestedTime right rightContinuous)) time‖ ^ 2 =
          _
      rw [leftEq, rightEq]
      rfl
    _ =
        ∫ t in (0 : ℝ)..requestedTime,
          ‖left t - right t‖ ^ 2 := by
      exact
        commonTime_integral_eq_intervalIntegral
          requestedTime requestedTimePos.le
          (fun t => ‖left t - right t‖ ^ 2)

theorem
    wholeNonlinearRowSpaceTimePath_sub_norm_eq_intervalIntegral
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (left right : ℝ → ComplexVorticityHilbertState)
    (leftContinuous :
      ContinuousOn left (Icc (0 : ℝ) requestedTime))
    (rightContinuous :
      ContinuousOn right (Icc (0 : ℝ) requestedTime))
    (leftTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.WholeStateTransverse
          (left t))
    (rightTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.WholeStateTransverse
          (right t))
    (output : IntegerWavevector) :
    ‖wholeNonlinearRowSpaceTimePath
          requestedTime left leftContinuous leftTransverse output -
        wholeNonlinearRowSpaceTimePath
          requestedTime right rightContinuous rightTransverse output‖ =
      ∫ t in (0 : ℝ)..requestedTime,
        ‖ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
              (left t) output -
            ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
              (right t) output‖ := by
  rw [nonlinearRowSpaceTimeState_norm_eq_integral]
  have leftAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (1 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (wholeNonlinearRowBoundedPath
        requestedTime left leftContinuous leftTransverse output)
  have rightAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (1 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (wholeNonlinearRowBoundedPath
        requestedTime right rightContinuous rightTransverse output)
  have subAE :=
    MeasureTheory.Lp.coeFn_sub
      (wholeNonlinearRowSpaceTimePath
        requestedTime left leftContinuous leftTransverse output)
      (wholeNonlinearRowSpaceTimePath
        requestedTime right rightContinuous rightTransverse output)
  calc
    (∫ time,
        ‖(wholeNonlinearRowSpaceTimePath
              requestedTime left leftContinuous leftTransverse output -
            wholeNonlinearRowSpaceTimePath
              requestedTime right rightContinuous rightTransverse output)
            time‖
        ∂(commonTimeMeasure requestedTime)) =
        ∫ time : Icc (0 : ℝ) requestedTime,
          ‖ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
                (left time.1) output -
              ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
                (right time.1) output‖
        ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards [subAE, leftAE, rightAE] with
        time subEq leftEq rightEq
      rw [subEq]
      change
        ‖((BoundedContinuousFunction.toLp 1
              (commonTimeMeasure requestedTime) ℂ)
              (wholeNonlinearRowBoundedPath
                requestedTime left leftContinuous
                leftTransverse output)) time -
            ((BoundedContinuousFunction.toLp 1
              (commonTimeMeasure requestedTime) ℂ)
              (wholeNonlinearRowBoundedPath
                requestedTime right rightContinuous
                rightTransverse output)) time‖ =
          _
      rw [leftEq, rightEq]
      rfl
    _ =
        ∫ t in (0 : ℝ)..requestedTime,
          ‖ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
                (left t) output -
              ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
                (right t) output‖ := by
      exact
        commonTime_integral_eq_intervalIntegral
          requestedTime requestedTimePos.le
          (fun t =>
            ‖ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
                  (left t) output -
                ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
                  (right t) output‖)

theorem wholeNonlinearRowSpaceTimePath_sub_norm_le
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (left right : ℝ → ComplexVorticityHilbertState)
    (leftContinuous :
      ContinuousOn left (Icc (0 : ℝ) requestedTime))
    (rightContinuous :
      ContinuousOn right (Icc (0 : ℝ) requestedTime))
    (leftTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.WholeStateTransverse
          (left t))
    (rightTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.WholeStateTransverse
          (right t))
    (output : IntegerWavevector) :
    ‖wholeNonlinearRowSpaceTimePath
          requestedTime left leftContinuous leftTransverse output -
        wholeNonlinearRowSpaceTimePath
          requestedTime right rightContinuous rightTransverse output‖ ≤
      6 * Real.sqrt (integerWaveNormSq output) *
        ‖wholeTrajectorySpaceTimePath
              requestedTime left leftContinuous -
            wholeTrajectorySpaceTimePath
              requestedTime right rightContinuous‖ *
        (‖wholeTrajectorySpaceTimePath
              requestedTime left leftContinuous‖ +
          ‖wholeTrajectorySpaceTimePath
              requestedTime right rightContinuous‖) := by
  rw [wholeNonlinearRowSpaceTimePath_sub_norm_eq_intervalIntegral
    requestedTime requestedTimePos left right
    leftContinuous rightContinuous
    leftTransverse rightTransverse output]
  have integrated :=
    wholeStateVorticityNonlinearCoefficientAt_sub_norm_intervalIntegral_le
      left right output 0 requestedTime requestedTimePos.le
      leftContinuous rightContinuous leftTransverse rightTransverse
  rw [
    ← wholeTrajectorySpaceTimePath_sub_norm_sq_eq_intervalIntegral
      requestedTime requestedTimePos left right
      leftContinuous rightContinuous,
    ← wholeTrajectorySpaceTimePath_norm_sq_eq_intervalIntegral
      requestedTime requestedTimePos left leftContinuous,
    ← wholeTrajectorySpaceTimePath_norm_sq_eq_intervalIntegral
      requestedTime requestedTimePos right rightContinuous,
    Real.sqrt_sq (norm_nonneg
      (wholeTrajectorySpaceTimePath
          requestedTime left leftContinuous -
        wholeTrajectorySpaceTimePath
          requestedTime right rightContinuous)),
    Real.sqrt_sq (norm_nonneg
      (wholeTrajectorySpaceTimePath
        requestedTime left leftContinuous)),
    Real.sqrt_sq (norm_nonneg
      (wholeTrajectorySpaceTimePath
        requestedTime right rightContinuous))] at integrated
  exact integrated

theorem wholeNonlinearRowSpaceTimePath_cauchySeq
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (trajectories : ℕ → ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ∀ index,
        ContinuousOn (trajectories index)
          (Icc (0 : ℝ) requestedTime))
    (trajectoryTransverse :
      ∀ index t, t ∈ Icc (0 : ℝ) requestedTime →
        ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.WholeStateTransverse
          (trajectories index t))
    (output : IntegerWavevector)
    (wholeCauchy :
      CauchySeq
        (fun index =>
          wholeTrajectorySpaceTimePath requestedTime
            (trajectories index)
            (trajectoryContinuous index))) :
    CauchySeq
      (fun index =>
        wholeNonlinearRowSpaceTimePath requestedTime
          (trajectories index)
          (trajectoryContinuous index)
          (trajectoryTransverse index) output) := by
  let stateSequence : ℕ → SpaceTimeState requestedTime :=
    fun index =>
      wholeTrajectorySpaceTimePath requestedTime
        (trajectories index) (trajectoryContinuous index)
  let nonlinearSequence :
      ℕ → NonlinearRowSpaceTimeState requestedTime :=
    fun index =>
      wholeNonlinearRowSpaceTimePath requestedTime
        (trajectories index)
        (trajectoryContinuous index)
        (trajectoryTransverse index) output
  obtain ⟨stateLimit, stateTendsto⟩ :=
    cauchySeq_tendsto_of_complete wholeCauchy
  have stateDistanceTendsto :
      Tendsto
        (fun indices : ℕ × ℕ =>
          dist (stateSequence indices.1)
            (stateSequence indices.2))
        atTop (𝓝 0) := by
    apply cauchySeq_iff_tendsto_dist_atTop_0.mp
    simpa [stateSequence] using wholeCauchy
  have fstAtTop :
      Tendsto (fun indices : ℕ × ℕ => indices.1)
        atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have sndAtTop :
      Tendsto (fun indices : ℕ × ℕ => indices.2)
        atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have stateNormSumTendsto :
      Tendsto
        (fun indices : ℕ × ℕ =>
          ‖stateSequence indices.1‖ +
            ‖stateSequence indices.2‖)
        atTop
        (𝓝 (‖stateLimit‖ + ‖stateLimit‖)) := by
    have stateTendsto' :
        Tendsto stateSequence atTop (𝓝 stateLimit) := by
      simpa [stateSequence] using stateTendsto
    exact
      (stateTendsto'.norm.comp fstAtTop).add
        (stateTendsto'.norm.comp sndAtTop)
  let angular : ℝ :=
    6 * Real.sqrt (integerWaveNormSq output)
  have boundTendsto :
      Tendsto
        (fun indices : ℕ × ℕ =>
          angular *
            dist (stateSequence indices.1)
              (stateSequence indices.2) *
            (‖stateSequence indices.1‖ +
              ‖stateSequence indices.2‖))
        atTop (𝓝 0) := by
    simpa using
      ((tendsto_const_nhds.mul stateDistanceTendsto).mul
        stateNormSumTendsto)
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  apply squeeze_zero
    (g := fun indices : ℕ × ℕ =>
      angular *
        dist (stateSequence indices.1)
          (stateSequence indices.2) *
        (‖stateSequence indices.1‖ +
          ‖stateSequence indices.2‖))
  · intro indices
    exact dist_nonneg
  · intro indices
    rw [dist_eq_norm]
    have bound :=
      wholeNonlinearRowSpaceTimePath_sub_norm_le
        requestedTime requestedTimePos
        (trajectories indices.1)
        (trajectories indices.2)
        (trajectoryContinuous indices.1)
        (trajectoryContinuous indices.2)
        (trajectoryTransverse indices.1)
        (trajectoryTransverse indices.2) output
    simpa [nonlinearSequence, stateSequence, angular,
      dist_eq_norm] using bound
  · exact boundTendsto

/-! ## Exact interpretation of the `Lp` weak action -/

theorem commonTime_integral_eq_intervalIntegral_vector
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (requestedTime : ℝ)
    (requestedTimeNonneg : 0 ≤ requestedTime)
    (function : ℝ → E) :
    (∫ time : Icc (0 : ℝ) requestedTime,
        function time.1 ∂(commonTimeMeasure requestedTime)) =
      ∫ time in (0 : ℝ)..requestedTime, function time := by
  rw [MeasureTheory.integral_subtype_comap measurableSet_Icc]
  rw [intervalIntegral.integral_of_le requestedTimeNonneg]
  rw [Measure.restrict_restrict_of_subset Subset.rfl]
  exact MeasureTheory.integral_Icc_eq_integral_Ioc

theorem fixedL2ScalarL2IntegralCLM_wholeTrajectory_eq_intervalIntegral
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (scalar : ℝ → ℂ)
    (scalarContinuous :
      ContinuousOn scalar (Icc (0 : ℝ) requestedTime))
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime))
    (wave : IntegerWavevector) :
    fixedL2ScalarL2IntegralCLM requestedTime
        (restrictedScalarL2
          requestedTime scalar scalarContinuous)
        (fixedWaveSpaceTimeRestriction requestedTime wave
          (wholeTrajectorySpaceTimePath
            requestedTime trajectory trajectoryContinuous)) =
      ∫ t in (0 : ℝ)..requestedTime,
        scalar t • trajectory t wave := by
  let scalarLp :=
    restrictedScalarL2 requestedTime scalar scalarContinuous
  let stateLp :=
    wholeTrajectorySpaceTimePath
      requestedTime trajectory trajectoryContinuous
  let rowLp :=
    fixedWaveSpaceTimeRestriction requestedTime wave stateLp
  have scalarAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (restrictedScalarBoundedPath
        requestedTime scalar scalarContinuous)
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
  have productAE :
      ⇑(scalarLp • rowLp :
          MeasureTheory.Lp ComplexCoordinateVector 1
            (commonTimeMeasure requestedTime)) =ᵐ[
          commonTimeMeasure requestedTime]
        ⇑scalarLp • ⇑rowLp :=
    MeasureTheory.Lp.coeFn_lpSMul scalarLp rowLp
  change
    (MeasureTheory.L1.integralCLM' ℂ)
        (scalarLp • rowLp) =
      _
  rw [← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  calc
    (∫ time,
        (scalarLp • rowLp) time
      ∂(commonTimeMeasure requestedTime)) =
        ∫ time : Icc (0 : ℝ) requestedTime,
          scalar time.1 • trajectory time.1 wave
        ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards
        [productAE, scalarAE, rowAE, stateAE] with
        time productEq scalarEq rowEq stateEq
      rw [productEq]
      change scalarLp time • rowLp time = _
      have scalarPoint :
          scalarLp time = scalar time.1 := by
        have scalarPoint' :
            scalarLp time =
              restrictedScalarBoundedPath
                requestedTime scalar scalarContinuous time := by
          simpa [scalarLp, restrictedScalarL2] using scalarEq
        exact scalarPoint'.trans rfl
      have statePoint :
          stateLp time = trajectory time.1 := by
        have statePoint' :
            stateLp time =
              wholeTrajectoryBoundedPath
                requestedTime trajectory trajectoryContinuous time := by
          simpa [stateLp, wholeTrajectorySpaceTimePath] using stateEq
        exact statePoint'.trans rfl
      rw [scalarPoint, rowEq, statePoint]
    _ =
        ∫ t in (0 : ℝ)..requestedTime,
          scalar t • trajectory t wave :=
      commonTime_integral_eq_intervalIntegral_vector
        requestedTime requestedTimePos.le
        (fun t => scalar t • trajectory t wave)

theorem fixedLInfScalarL1IntegralCLM_wholeNonlinear_eq_intervalIntegral
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (scalar : ℝ → ℂ)
    (scalarContinuous :
      ContinuousOn scalar (Icc (0 : ℝ) requestedTime))
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime))
    (trajectoryTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.WholeStateTransverse
          (trajectory t))
    (wave : IntegerWavevector) :
    fixedLInfScalarL1IntegralCLM requestedTime
        (restrictedScalarLInf
          requestedTime scalar scalarContinuous)
        (wholeNonlinearRowSpaceTimePath requestedTime
          trajectory trajectoryContinuous
          trajectoryTransverse wave) =
      ∫ t in (0 : ℝ)..requestedTime,
        scalar t •
          ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
            (trajectory t) wave := by
  let scalarLp :=
    restrictedScalarLInf requestedTime scalar scalarContinuous
  let nonlinearLp :=
    wholeNonlinearRowSpaceTimePath requestedTime
      trajectory trajectoryContinuous trajectoryTransverse wave
  have scalarAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (∞ : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (restrictedScalarBoundedPath
        requestedTime scalar scalarContinuous)
  have nonlinearAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (1 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (wholeNonlinearRowBoundedPath
        requestedTime trajectory trajectoryContinuous
        trajectoryTransverse wave)
  have productAE :
      ⇑(scalarLp • nonlinearLp :
          MeasureTheory.Lp ComplexCoordinateVector 1
            (commonTimeMeasure requestedTime)) =ᵐ[
          commonTimeMeasure requestedTime]
        ⇑scalarLp • ⇑nonlinearLp :=
    MeasureTheory.Lp.coeFn_lpSMul scalarLp nonlinearLp
  change
    (MeasureTheory.L1.integralCLM' ℂ)
        (scalarLp • nonlinearLp) =
      _
  rw [← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  calc
    (∫ time,
        (scalarLp • nonlinearLp) time
      ∂(commonTimeMeasure requestedTime)) =
        ∫ time : Icc (0 : ℝ) requestedTime,
          scalar time.1 •
            ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
              (trajectory time.1) wave
        ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards
        [productAE, scalarAE, nonlinearAE] with
        time productEq scalarEq nonlinearEq
      rw [productEq]
      change scalarLp time • nonlinearLp time = _
      have scalarPoint :
          scalarLp time = scalar time.1 := by
        have scalarPoint' :
            scalarLp time =
              restrictedScalarBoundedPath
                requestedTime scalar scalarContinuous time := by
          simpa [scalarLp, restrictedScalarLInf] using scalarEq
        exact scalarPoint'.trans rfl
      have nonlinearPoint :
          nonlinearLp time =
            ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
              (trajectory time.1) wave := by
        have nonlinearPoint' :
            nonlinearLp time =
              wholeNonlinearRowBoundedPath requestedTime trajectory
                trajectoryContinuous trajectoryTransverse wave time := by
          simpa [nonlinearLp, wholeNonlinearRowSpaceTimePath] using nonlinearEq
        exact nonlinearPoint'.trans rfl
      rw [scalarPoint, nonlinearPoint]
    _ =
        ∫ t in (0 : ℝ)..requestedTime,
          scalar t •
            ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
              (trajectory t) wave :=
      commonTime_integral_eq_intervalIntegral_vector
        requestedTime requestedTimePos.le
        (fun t =>
          scalar t •
            ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt
              (trajectory t) wave)

theorem
    fixedL2ScalarL2IntegralCLM_viscousWholeTrajectory_eq_intervalIntegral
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (scalar : ℝ → ℂ)
    (scalarContinuous :
      ContinuousOn scalar (Icc (0 : ℝ) requestedTime))
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime))
    (wave : IntegerWavevector)
    (viscousCoefficient : ℝ) :
    fixedL2ScalarL2IntegralCLM requestedTime
        (restrictedScalarL2
          requestedTime scalar scalarContinuous)
        (((viscousCoefficient : ℝ) : ℂ) •
          fixedWaveSpaceTimeRestriction requestedTime wave
            (wholeTrajectorySpaceTimePath
              requestedTime trajectory trajectoryContinuous)) =
      ∫ t in (0 : ℝ)..requestedTime,
        scalar t •
          (viscousCoefficient • trajectory t wave) := by
  rw [map_smul]
  rw [
    fixedL2ScalarL2IntegralCLM_wholeTrajectory_eq_intervalIntegral
      requestedTime requestedTimePos scalar scalarContinuous
      trajectory trajectoryContinuous wave]
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t timeMem
  ext coordinate
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  ring

/-! ## Actual finite Galerkin weak identity -/

/--
Every retained wave of an actual finite Galerkin trajectory satisfies the
full-lattice Fourier vorticity equation against a compactly supported
`C¹` time test.  The complete infinite nonlinear row is read from the
actual finite support; it is not supplied as a premise.
-/
theorem finiteSupportWave_infiniteRow_weak_identity
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
    (test testDerivative : ℝ → ℂ)
    (testHasDeriv :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt test (testDerivative t) t)
    (testDerivativeContinuous :
      ContinuousOn testDerivative
        (Icc (0 : ℝ) requestedTime))
    (testZero : test 0 = 0)
    (testRequestedTimeZero : test requestedTime = 0) :
    fixedWaveWeakAction requestedTime ν wave
        (restrictedScalarL2 requestedTime test
          (fun t timeMem =>
            (testHasDeriv t timeMem).continuousAt.continuousWithinAt))
        (restrictedScalarL2 requestedTime testDerivative
          testDerivativeContinuous)
        (restrictedScalarLInf requestedTime test
          (fun t timeMem =>
            (testHasDeriv t timeMem).continuousAt.continuousWithinAt))
        (wholeTrajectorySpaceTimePath requestedTime trajectory
          (fun t timeMem =>
            (evolves t timeMem).continuousAt.continuousWithinAt))
        (wholeNonlinearRowSpaceTimePath requestedTime trajectory
          (fun t timeMem =>
            (evolves t timeMem).continuousAt.continuousWithinAt)
          transverse wave) =
      0 := by
  let trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime) :=
    fun t timeMem =>
      (evolves t timeMem).continuousAt.continuousWithinAt
  let testContinuous :
      ContinuousOn test (Icc (0 : ℝ) requestedTime) :=
    fun t timeMem =>
      (testHasDeriv t timeMem).continuousAt.continuousWithinAt
  let nonlinearTangent : ℝ → ComplexCoordinateVector :=
    fun t =>
      wholeStateVorticityNonlinearCoefficientAt
          (trajectory t) wave -
        (ν * integerWaveViscousMultiplier wave) •
          trajectory t wave
  have waveDerivative :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt
          (fun time => trajectory time wave)
          (nonlinearTangent t) t := by
    intro t timeMem
    have rowDerivative :=
      complexVorticityTrajectoryWave_hasDerivAt
        trajectory t
        (finiteStateVorticityGenerator
          modes ν (trajectory t))
        wave (evolves t timeMem)
    rw [finiteStateVorticityGenerator_apply,
      if_pos waveMem] at rowDerivative
    have nonlinearEq :
        wholeStateVorticityNonlinearCoefficientAt
            (trajectory t) wave =
          finiteStateVorticityNonlinearCoefficientAt
            modes (trajectory t) wave :=
      wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
        modes (trajectory t) (supported t timeMem) wave
    rw [← nonlinearEq] at rowDerivative
    exact rowDerivative
  have rowContinuous :
      ContinuousOn
        (fun t => trajectory t wave)
        (Icc (0 : ℝ) requestedTime) := by
    exact
      (complexVorticityEvaluation_contDiff wave).continuous.comp_continuousOn
        trajectoryContinuous
  have nonlinearContinuous :
      ContinuousOn
        (fun t =>
          wholeStateVorticityNonlinearCoefficientAt
            (trajectory t) wave)
        (Icc (0 : ℝ) requestedTime) :=
    wholeStateVorticityNonlinearCoefficientAt_comp_continuousOn
      trajectory wave 0 requestedTime trajectoryContinuous transverse
  have viscousContinuous :
      ContinuousOn
        (fun t =>
          (ν * integerWaveViscousMultiplier wave) •
            trajectory t wave)
        (Icc (0 : ℝ) requestedTime) :=
    rowContinuous.const_smul
      (ν * integerWaveViscousMultiplier wave)
  have tangentContinuous :
      ContinuousOn nonlinearTangent
        (Icc (0 : ℝ) requestedTime) :=
    nonlinearContinuous.sub viscousContinuous
  have testDerivativeIntegrable :
      IntervalIntegrable testDerivative volume
        0 requestedTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      requestedTimePos.le testDerivativeContinuous
  have tangentIntegrable :
      IntervalIntegrable nonlinearTangent volume
        0 requestedTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      requestedTimePos.le tangentContinuous
  have interiorToIcc :
      ∀ t ∈ Ioo (min (0 : ℝ) requestedTime)
          (max (0 : ℝ) requestedTime),
        t ∈ Icc (0 : ℝ) requestedTime := by
    intro t timeMem
    have timeMem' : t ∈ Ioo (0 : ℝ) requestedTime := by
      simpa [min_eq_left requestedTimePos.le,
        max_eq_right requestedTimePos.le] using timeMem
    exact ⟨le_of_lt timeMem'.1, le_of_lt timeMem'.2⟩
  have integrationByParts :=
    intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
      (by
        simpa [uIcc_of_le requestedTimePos.le] using testContinuous)
      (by
        simpa [uIcc_of_le requestedTimePos.le] using rowContinuous)
      (fun t timeMem =>
        testHasDeriv t (interiorToIcc t timeMem))
      (fun t timeMem =>
        waveDerivative t (interiorToIcc t timeMem))
      testDerivativeIntegrable tangentIntegrable
  rw [testZero, testRequestedTimeZero] at integrationByParts
  simp only [zero_smul, zero_sub, neg_zero] at integrationByParts
  have weakInterval :
      (∫ t in (0 : ℝ)..requestedTime,
          testDerivative t • trajectory t wave) +
        (∫ t in (0 : ℝ)..requestedTime,
          test t •
            wholeStateVorticityNonlinearCoefficientAt
              (trajectory t) wave) -
        (∫ t in (0 : ℝ)..requestedTime,
          test t •
            ((ν * integerWaveViscousMultiplier wave) •
              trajectory t wave)) =
        0 := by
    have nonlinearIntegrable :
        IntervalIntegrable
          (fun t =>
            test t •
              wholeStateVorticityNonlinearCoefficientAt
                (trajectory t) wave)
          volume 0 requestedTime :=
      ContinuousOn.intervalIntegrable_of_Icc
        requestedTimePos.le
        (testContinuous.smul nonlinearContinuous)
    have viscousIntegrable :
        IntervalIntegrable
          (fun t =>
            test t •
              ((ν * integerWaveViscousMultiplier wave) •
                trajectory t wave))
          volume 0 requestedTime :=
      ContinuousOn.intervalIntegrable_of_Icc
        requestedTimePos.le
        (testContinuous.smul viscousContinuous)
    have splitTangent :
        (∫ t in (0 : ℝ)..requestedTime,
            test t • nonlinearTangent t) =
          (∫ t in (0 : ℝ)..requestedTime,
            test t •
              wholeStateVorticityNonlinearCoefficientAt
                (trajectory t) wave) -
          ∫ t in (0 : ℝ)..requestedTime,
            test t •
              ((ν * integerWaveViscousMultiplier wave) •
                trajectory t wave) := by
      rw [← intervalIntegral.integral_sub
        nonlinearIntegrable viscousIntegrable]
      apply intervalIntegral.integral_congr
      intro t timeMem
      simp [nonlinearTangent, smul_sub]
    rw [splitTangent] at integrationByParts
    calc
      (∫ t in (0 : ℝ)..requestedTime,
          testDerivative t • trajectory t wave) +
          (∫ t in (0 : ℝ)..requestedTime,
            test t •
              wholeStateVorticityNonlinearCoefficientAt
                (trajectory t) wave) -
          (∫ t in (0 : ℝ)..requestedTime,
            test t •
              ((ν * integerWaveViscousMultiplier wave) •
                trajectory t wave)) =
          (∫ t in (0 : ℝ)..requestedTime,
              testDerivative t • trajectory t wave) +
            ((∫ t in (0 : ℝ)..requestedTime,
                test t •
                  wholeStateVorticityNonlinearCoefficientAt
                    (trajectory t) wave) -
              ∫ t in (0 : ℝ)..requestedTime,
                test t •
                  ((ν * integerWaveViscousMultiplier wave) •
                    trajectory t wave)) := by
            abel
      _ =
          (∫ t in (0 : ℝ)..requestedTime,
              testDerivative t • trajectory t wave) +
            -(∫ t in (0 : ℝ)..requestedTime,
              testDerivative t • trajectory t wave) := by
            rw [integrationByParts]
      _ = 0 := by simp
  change
    fixedWaveWeakAction requestedTime ν wave
        (restrictedScalarL2 requestedTime test testContinuous)
        (restrictedScalarL2 requestedTime testDerivative
          testDerivativeContinuous)
        (restrictedScalarLInf requestedTime test testContinuous)
        (wholeTrajectorySpaceTimePath requestedTime trajectory
          trajectoryContinuous)
        (wholeNonlinearRowSpaceTimePath requestedTime trajectory
          trajectoryContinuous transverse wave) =
      0
  unfold fixedWaveWeakAction
  rw [
    fixedL2ScalarL2IntegralCLM_wholeTrajectory_eq_intervalIntegral
      requestedTime requestedTimePos
      testDerivative testDerivativeContinuous
      trajectory trajectoryContinuous wave,
    fixedLInfScalarL1IntegralCLM_wholeNonlinear_eq_intervalIntegral
      requestedTime requestedTimePos test testContinuous
      trajectory trajectoryContinuous transverse wave,
    fixedL2ScalarL2IntegralCLM_viscousWholeTrajectory_eq_intervalIntegral
      requestedTime requestedTimePos test testContinuous
      trajectory trajectoryContinuous wave
      (ν * integerWaveViscousMultiplier wave)]
  exact weakInterval

end

end ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
end NavierStokes
end SaturationMonoid
