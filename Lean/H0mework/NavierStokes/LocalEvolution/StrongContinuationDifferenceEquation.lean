import H0mework.NavierStokes.ShellSources.StrongContinuation
import H0mework.NavierStokes.Energy.WholeTangentEnergyTransport

/-!
# Actual difference equation for two coefficient strong continuations

Two strong-continuation receipts carried by the same generated lineage have
the same source-generated initial datum.  Their continuous path difference
therefore starts at zero, represents the difference of the two whole
space-time states, and has the difference of the two complete
`L²_t H⁻¹_x` tangents.

The final theorem below identifies that tangent, almost everywhere at every
nonzero Fourier wave, with the polarized Navier--Stokes nonlinearity minus
the exact viscous multiplier.  This is the actual nonlinear difference
equation needed by a same-horizon uniqueness argument; no equality,
compatibility, target path, or uniqueness certificate is accepted as input.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceEquation

open scoped ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedPathReceiptSquareUniformBound
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellCriticalSerrinWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellNonlinearNegativeOneForcing
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuation
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow

noncomputable section

section SameHorizon

variable
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}

/--
The path difference of two actual strong continuations on the same
generated lineage and horizon.
-/
def StrongContinuationReceipt.wholePathDifference
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) requestedTime)
      ComplexVorticityHilbertState :=
  left.wholePath - right.wholePath

/--
The complete negative-one tangent difference on the same whole carrier.
-/
def StrongContinuationReceipt.wholeNegativeOneTangentDifference
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    SpaceTimeState requestedTime :=
  NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
      left.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt -
    NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
      right.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt

/--
The two receipts have the same actual initial datum because both are limits
of the same source-owned punctured canonical initial sequence.
-/
theorem StrongContinuationReceipt.initialState_eq
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    left.initialState = right.initialState :=
  tendsto_nhds_unique left.initial_tendsto right.initial_tendsto

/-- The actual continuous difference path starts at zero. -/
theorem StrongContinuationReceipt.wholePathDifference_initial
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    StrongContinuationReceipt.wholePathDifference left right
        ⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩ =
      0 := by
  change
    left.wholePath
          ⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩ -
        right.wholePath
          ⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩ =
      0
  rw [left.wholePath_initial, right.wholePath_initial,
    StrongContinuationReceipt.initialState_eq left right, sub_self]

/--
The continuous difference path represents exactly the difference of the two
pre-existing whole space-time states.
-/
theorem StrongContinuationReceipt.wholePathDifference_toLp
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ
        (StrongContinuationReceipt.wholePathDifference left right) =
      left.stateLimit - right.stateLimit := by
  rw [StrongContinuationReceipt.wholePathDifference, map_sub,
    left.wholePath_toLp_eq_stateLimit,
    right.wholePath_toLp_eq_stateLimit]

/--
Fixed-wave observation commutes with formation of the whole tangent
difference.
-/
theorem
    StrongContinuationReceipt.fixedWave_wholeNegativeOneTangentDifference
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) :
    (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
        fixedWaveSpaceTimeRestriction requestedTime wave
          (StrongContinuationReceipt.wholeNegativeOneTangentDifference
            left right) =
      NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
          left.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
          wave -
        NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
          right.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
          wave := by
  rw [StrongContinuationReceipt.wholeNegativeOneTangentDifference,
    map_sub, smul_sub]
  rfl

/--
Subtracting the two actual weak update laws gives the weak equation for the
continuous path difference and the whole tangent difference.  No equality
between the two paths is assumed.
-/
theorem StrongContinuationReceipt.weak_difference_action
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (test testDerivative : ℝ → ℂ)
    (testHasDeriv :
      ∀ time ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt test (testDerivative time) time)
    (testDerivativeContinuous :
      ContinuousOn testDerivative
        (Icc (0 : ℝ) requestedTime))
    (testZero : test 0 = 0)
    (testRequestedTimeZero : test requestedTime = 0) :
    fixedL2ScalarL2IntegralCLM requestedTime
          (restrictedScalarL2 requestedTime testDerivative
            testDerivativeContinuous)
          (fixedWaveSpaceTimeRestriction requestedTime wave
            (BoundedContinuousFunction.toLp 2
              (commonTimeMeasure requestedTime) ℂ
              (StrongContinuationReceipt.wholePathDifference
                left right))) +
        fixedL2ScalarL2IntegralCLM requestedTime
          (restrictedScalarL2 requestedTime test
            (fun time timeMem =>
              (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
          ((Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
            fixedWaveSpaceTimeRestriction requestedTime wave
              (StrongContinuationReceipt.wholeNegativeOneTangentDifference
                left right)) =
      0 := by
  let testContinuous :
      ContinuousOn test (Icc (0 : ℝ) requestedTime) :=
    fun time timeMem =>
      (testHasDeriv time timeMem).continuousAt.continuousWithinAt
  have leftWeak :=
    left.weak_action_via_wholePath_tangent
      wave waveNe test testDerivative testHasDeriv
      testDerivativeContinuous testZero testRequestedTimeZero
  have rightWeak :=
    right.weak_action_via_wholePath_tangent
      wave waveNe test testDerivative testHasDeriv
      testDerivativeContinuous testZero testRequestedTimeZero
  rw [left.wholePath_toLp_eq_stateLimit] at leftWeak
  rw [right.wholePath_toLp_eq_stateLimit] at rightWeak
  rw [StrongContinuationReceipt.wholePathDifference_toLp left right,
    StrongContinuationReceipt.fixedWave_wholeNegativeOneTangentDifference
      left right wave]
  simp only [map_sub]
  calc
    _ =
        (fixedL2ScalarL2IntegralCLM requestedTime
              (restrictedScalarL2 requestedTime testDerivative
                testDerivativeContinuous)
              (fixedWaveSpaceTimeRestriction requestedTime wave
                left.stateLimit) +
            fixedL2ScalarL2IntegralCLM requestedTime
              (restrictedScalarL2 requestedTime test testContinuous)
              (NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
                left.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
                wave)) -
          (fixedL2ScalarL2IntegralCLM requestedTime
              (restrictedScalarL2 requestedTime testDerivative
                testDerivativeContinuous)
              (fixedWaveSpaceTimeRestriction requestedTime wave
                right.stateLimit) +
            fixedL2ScalarL2IntegralCLM requestedTime
              (restrictedScalarL2 requestedTime test testContinuous)
              (NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
                right.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
                wave)) := by
          abel
    _ = 0 := by rw [leftWeak, rightWeak, sub_self]

/--
Almost everywhere, the complete tangent difference is the polarized
Navier--Stokes nonlinearity in the actual two states minus the exact viscous
multiplier applied to their difference.

This is the coefficient-level nonlinear difference equation required by
the energy/Gronwall uniqueness gate.
-/
theorem
    StrongContinuationReceipt.wholeNegativeOneTangentDifference_unweighted_row_ae
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      Real.sqrt (integerWaveViscousMultiplier wave) •
          (StrongContinuationReceipt.wholeNegativeOneTangentDifference
            left right time) wave =
        wholeStateVorticityBilinearCoefficientAt
            ((left.transverseLimit time).val -
              (right.transverseLimit time).val)
            (left.transverseLimit time).val wave +
          wholeStateVorticityBilinearCoefficientAt
            (right.transverseLimit time).val
            ((left.transverseLimit time).val -
              (right.transverseLimit time).val) wave -
          (ν.coeff * integerWaveViscousMultiplier wave) •
            ((left.transverseLimit time).val wave -
              (right.transverseLimit time).val wave) := by
  have leftStateAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        left.stateLimit time =
          (left.transverseLimit time).val := by
    simpa only [left.inclusion_eq] using
      transverseSpaceTimeInclusion_coeFn
        requestedTime left.transverseLimit
  have rightStateAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        right.stateLimit time =
          (right.transverseLimit time).val := by
    simpa only [right.inclusion_eq] using
      transverseSpaceTimeInclusion_coeFn
        requestedTime right.transverseLimit
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
        left.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt)
      (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
        right.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt),
    NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent_unweighted_row_ae
      left.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
      wave waveNe,
    NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent_unweighted_row_ae
      right.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
      wave waveNe,
    transverseSpaceTimeNonlinearRow_coeFn
      left.transverseLimit wave,
    transverseSpaceTimeNonlinearRow_coeFn
      right.transverseLimit wave,
    leftStateAE, rightStateAE] with
      time tangentDifferenceEq leftTangentEq rightTangentEq
      leftNonlinearEq rightNonlinearEq leftStateEq rightStateEq
  change
    Real.sqrt (integerWaveViscousMultiplier wave) •
        (((NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
              left.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt -
            NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
              right.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt)
            time) wave) =
      _
  rw [tangentDifferenceEq]
  change
    Real.sqrt (integerWaveViscousMultiplier wave) •
        ((NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
            left.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
            time) wave -
          (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
            right.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
            time) wave) =
      _
  rw [smul_sub, leftTangentEq, rightTangentEq,
    leftStateEq, rightStateEq,
    leftNonlinearEq, rightNonlinearEq]
  change
    (wholeStateVorticityNonlinearCoefficientAt
          (left.transverseLimit time).val wave -
        (ν.coeff * integerWaveViscousMultiplier wave) •
          (left.transverseLimit time).val wave) -
      (wholeStateVorticityNonlinearCoefficientAt
          (right.transverseLimit time).val wave -
        (ν.coeff * integerWaveViscousMultiplier wave) •
          (right.transverseLimit time).val wave) =
      _
  calc
    _ =
        (wholeStateVorticityNonlinearCoefficientAt
              (left.transverseLimit time).val wave -
            wholeStateVorticityNonlinearCoefficientAt
              (right.transverseLimit time).val wave) -
          (ν.coeff * integerWaveViscousMultiplier wave) •
            ((left.transverseLimit time).val wave -
              (right.transverseLimit time).val wave) := by
      rw [smul_sub]
      abel
    _ = _ := by
      rw [wholeStateVorticityNonlinearCoefficientAt_sub
        (left.transverseLimit time).val
        (right.transverseLimit time).val
        (left.transverseLimit time).2
        (right.transverseLimit time).2 wave]

end SameHorizon

end

end ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceEquation
end NavierStokes
end SaturationMonoid
