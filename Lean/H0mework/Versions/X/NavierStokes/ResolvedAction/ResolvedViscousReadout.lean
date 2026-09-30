import H0mework.NavierStokes.SourceAction.SpatialOperators
import H0mework.Versions.X.NavierStokes.ResolvedAction.ResolvedAction

set_option autoImplicit false
open scoped BigOperators ContDiff

namespace SaturationMonoid.NavierStokes.NativeResolvedViscousReadout

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open NativeFluidSpatialOperators NativeStressSource

noncomputable section

def frequency (wave : IntegerWavevector) (direction : Coordinate) : ℝ := 2 * Real.pi * (wave direction : ℝ)

theorem phase_single (wave : IntegerWavevector) (direction : Coordinate) :
    integerWavePhaseLinear wave (EuclideanSpace.single direction 1) = frequency wave direction := by
  simp [integerWavePhaseLinear, frequency]

theorem derivative_mode (wave : IntegerWavevector) (coefficient : ComplexCoordinateVector) (direction : Coordinate) :
    spatialDerivative (realComplexFourierMode wave coefficient) direction =
      realComplexFourierMode wave ((Complex.I * (frequency wave direction : ℂ)) • coefficient) := by
  funext space
  unfold spatialDerivative
  rw [realComplexFourierMode_fderiv]
  ext output
  simp [realComplexFourierMode, integerCosine_fderiv, integerSine_fderiv, phase_single,
    integerCosine, integerSine, coefficientReal, coefficientImag, Complex.mul_re, Complex.mul_im]
  ring

theorem derivative_mode_twice (wave : IntegerWavevector) (coefficient : ComplexCoordinateVector) (direction : Coordinate) :
    spatialDerivative (spatialDerivative (realComplexFourierMode wave coefficient) direction) direction =
      fun space => -(frequency wave direction) ^ 2 • realComplexFourierMode wave coefficient space := by
  rw [derivative_mode, derivative_mode]
  funext space
  change realModeCLM wave space _ = _
  have same : (Complex.I * (frequency wave direction : ℂ)) •
      ((Complex.I * (frequency wave direction : ℂ)) • coefficient) =
        (-(frequency wave direction) ^ 2 : ℝ) • coefficient := by
    ext output
    simp [Complex.ext_iff, Complex.real_smul, pow_two, Complex.mul_re, Complex.mul_im]
    constructor <;> ring
  rw [same, map_smul]
  rfl

theorem sum_frequency (wave : IntegerWavevector) :
    ∑ direction : Coordinate, (frequency wave direction) ^ 2 = integerWaveViscousMultiplier wave := by
  simp only [frequency, mul_pow, integerWaveViscousMultiplier, integerWaveNormSq, Finset.mul_sum]

theorem laplacian_mode (wave : IntegerWavevector) (coefficient : ComplexCoordinateVector) :
    spatialLaplacian (realComplexFourierMode wave coefficient) =
      fun space => -integerWaveViscousMultiplier wave • realComplexFourierMode wave coefficient space := by
  funext space
  unfold spatialLaplacian
  simp_rw [derivative_mode_twice]
  rw [← Finset.sum_smul, Finset.sum_neg_distrib, sum_frequency]

theorem derivative_finite (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) (direction : Coordinate) :
    spatialDerivative (finiteRealComplexFourierField modes coefficient) direction =
      finiteRealComplexFourierField modes (fun wave => (Complex.I * (frequency wave direction : ℂ)) • coefficient wave) := by
  funext space
  unfold spatialDerivative
  rw [finiteRealComplexFourierField_fderiv]
  simp only [_root_.sum_apply, finiteRealComplexFourierField]
  apply Finset.sum_congr rfl
  intro wave _
  exact congrFun (derivative_mode wave (coefficient wave) direction) space

theorem laplacian_finite (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    spatialLaplacian (finiteRealComplexFourierField modes coefficient) =
      fun space => ∑ wave ∈ modes, -integerWaveViscousMultiplier wave • realComplexFourierMode wave (coefficient wave) space := by
  funext space
  unfold spatialLaplacian
  simp_rw [derivative_finite]
  simp only [finiteRealComplexFourierField]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro wave _
  rw [← congrFun (laplacian_mode wave (coefficient wave)) space]
  simp only [spatialLaplacian, derivative_mode]

theorem resolved_viscous_read (modes : Finset IntegerWavevector) (viscosity : ℝ)
    (state : ComplexVorticityHilbertState) :
    resolvedViscousField modes viscosity state =
      fun space => -viscosity • spatialLaplacian (finiteRealComplexFourierField modes state) space := by
  funext space
  rw [laplacian_finite]
  change (∑ wave ∈ modes, realModeCLM wave space
    ((viscosity * integerWaveViscousMultiplier wave) • complexSharpSupportProjection modes state wave)) = _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro wave member
  rw [complexSharpSupportProjection_apply, if_pos member, map_smul, smul_smul, neg_mul_neg]
  rfl

end
end SaturationMonoid.NavierStokes.NativeResolvedViscousReadout
