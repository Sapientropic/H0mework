import H0mework.NavierStokes.WholeReceipt.PrefixState
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeNonlinearNegativeOne
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeViscousNegativeOne

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.WholePrefixTangent

open scoped ENNReal
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open WholePrefixState

noncomputable section

variable {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) (length : Nat)

theorem pointwiseGradient :
    ∀ᵐ time ∂(commonTimeMeasure (duration initial length)),
      Summable fun wave : IntegerWavevector => integerWaveNormSq wave *
        complexCoordinateAmplitudeSq (stateLimit initial length time wave) :=
  wholePointwiseGradientDensity_ae_summable
    (duration initial length) (stateLimit initial length) (gradient_summable initial length)

def nonlinear : SpaceTimeState (duration initial length) :=
  wholeSpaceTimeNonlinearNegativeOneState (transverseLimit initial length)
    (transverse_gradient_summable initial length) (enstrophyCeiling_nonneg initial length)
    (transverse_massBound initial length)

def viscous : SpaceTimeState (duration initial length) :=
  wholeSpaceTimeViscousNegativeOneState nu.coeff (stateLimit initial length)
    (gradient_summable initial length) (pointwiseGradient initial length)

def tangent : SpaceTimeState (duration initial length) :=
  nonlinear initial length - viscous initial length

def rowTangent (wave : IntegerWavevector)
    (time : Icc (0 : Real) (duration initial length)) : ComplexCoordinateVector :=
  wholeStateVorticityNonlinearCoefficientAt (wholePath initial length time) wave -
    (nu.coeff * integerWaveViscousMultiplier wave) • wholePath initial length time wave

theorem tangent_eq_unforced_ae :
    ∀ᵐ time ∂(commonTimeMeasure (duration initial length)),
      tangent initial length time =
        wholeSpaceTimeNonlinearNegativeOneFunction (transverseLimit initial length) time -
          wholeSpaceTimeViscousNegativeOneFunction nu.coeff (stateLimit initial length) time := by
  filter_upwards [Lp.coeFn_sub (nonlinear initial length) (viscous initial length),
    wholeSpaceTimeNonlinearNegativeOneState_coeFn (transverseLimit initial length)
      (transverse_gradient_summable initial length) (enstrophyCeiling_nonneg initial length)
      (transverse_massBound initial length),
    wholeSpaceTimeViscousNegativeOneState_coeFn nu.coeff (stateLimit initial length)
      (gradient_summable initial length) (pointwiseGradient initial length)] with
    time subtract nonlinearEq viscousEq
  change (nonlinear initial length - viscous initial length) time = _
  rw [subtract]
  exact congrArg₂ (· - ·) nonlinearEq viscousEq

theorem rowTangent_eq_unforced_ae (wave : IntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure (duration initial length)),
      rowTangent initial length wave time =
        wholeStateVorticityBilinearCoefficientAt (transverseLimit initial length time).1
          (transverseLimit initial length time).1 wave -
          (nu.coeff * integerWaveViscousMultiplier wave) • wholePath initial length time wave := by
  filter_upwards [transverse_eq_wholePath_ae initial length] with time same
  rw [same, wholeStateVorticityBilinearCoefficientAt_self]
  rfl

private theorem realAction (scalar : Real) (value : ComplexCoordinateVector) :
    (scalar : Complex) • value = scalar • value := by
  ext coordinate
  simp [Complex.real_smul]

theorem unweighted_row_ae (wave : IntegerWavevector) (waveNe : wave ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure (duration initial length)),
      (Real.sqrt (integerWaveViscousMultiplier wave) : Complex) •
        (tangent initial length time) wave = rowTangent initial length wave time := by
  filter_upwards [Lp.coeFn_sub (nonlinear initial length) (viscous initial length),
    wholeSpaceTimeNonlinearNegativeOneState_unweighted_row_ae (transverseLimit initial length)
      (transverse_gradient_summable initial length) (enstrophyCeiling_nonneg initial length)
      (transverse_massBound initial length) wave waveNe,
    wholeSpaceTimeViscousNegativeOneState_unweighted_row_ae nu.coeff (stateLimit initial length)
      (gradient_summable initial length) (pointwiseGradient initial length) wave,
    transverseSpaceTimeNonlinearRow_coeFn (transverseLimit initial length) wave,
    transverse_eq_wholePath_ae initial length, state_eq_wholePath_ae initial length] with
    time subtract nonlinearEq viscousEq rowEq transverseEq pathEq
  change (Real.sqrt (integerWaveViscousMultiplier wave) : Complex) •
    ((nonlinear initial length - viscous initial length) time) wave = _
  rw [subtract]
  change (Real.sqrt (integerWaveViscousMultiplier wave) : Complex) •
    ((nonlinear initial length time) wave - (viscous initial length time) wave) = _
  have nonlinearRow : (Real.sqrt (integerWaveViscousMultiplier wave) : Real) •
      (nonlinear initial length time) wave =
        transverseSpaceTimeNonlinearRow (transverseLimit initial length) wave time := nonlinearEq
  have viscousRow : (Real.sqrt (integerWaveViscousMultiplier wave) : Real) •
      (viscous initial length time) wave =
        (nu.coeff * integerWaveViscousMultiplier wave) • stateLimit initial length time wave := viscousEq
  rw [smul_sub, realAction, realAction, nonlinearRow, viscousRow, rowEq]
  change wholeStateVorticityNonlinearCoefficientAt (transverseLimit initial length time).1 wave -
    (nu.coeff * integerWaveViscousMultiplier wave) • stateLimit initial length time wave = _
  rw [transverseEq, pathEq]
  rfl

end
end SaturationMonoid.NavierStokes.WholePrefixTangent
