import H0mework.NavierStokes.Fourier.FullVorticityStretching
import H0mework.NavierStokes.Fourier.IntegerCharacterUnitCellMean
import H0mework.NavierStokes.InitialData.RawSourceCore

/-!
# Physical compiler for finite three-dimensional vorticity coefficients

A complex coordinate coefficient is realized on the physical three-torus by
the real character

```text
cos(2π k·x) re(a) - sin(2π k·x) im(a).
```

The compiler sums this expression over an arbitrary finite signed support.
There is no planar representative choice and no half weight: the source
already owns its complete signed support and its conjugate-reality law.

At the generic coefficient level, physical divergence and right-handed curl
are proved to agree with multiplication by their Fourier symbols.  The raw
source then supplies transversality and the exact Biot--Savart coefficient
identity on site, yielding a divergence-free physical velocity whose curl is
the source-generated physical vorticity.  No reality, divergence, support,
nonvanishing, or membership certificate is accepted by this module.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientPhysicalCompiler

open scoped BigOperators Matrix

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicCoarseVectorCalculus
open ThreeDimensionalPeriodicFullVorticityStretching
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalVorticityCoefficientRawSourceCore

noncomputable section

/-! ## Real realization of complex coefficients -/

/-- Coordinatewise real part on the physical Euclidean carrier. -/
def coefficientReal
    (coefficient : ComplexCoordinateVector) : PhysicalSpace :=
  WithLp.toLp 2 fun coordinate => (coefficient coordinate).re

/-- Coordinatewise imaginary part on the physical Euclidean carrier. -/
def coefficientImag
    (coefficient : ComplexCoordinateVector) : PhysicalSpace :=
  WithLp.toLp 2 fun coordinate => (coefficient coordinate).im

@[simp] theorem coefficientReal_apply
    (coefficient : ComplexCoordinateVector)
    (coordinate : Coordinate) :
    coefficientReal coefficient coordinate =
      (coefficient coordinate).re :=
  rfl

@[simp] theorem coefficientImag_apply
    (coefficient : ComplexCoordinateVector)
    (coordinate : Coordinate) :
    coefficientImag coefficient coordinate =
      (coefficient coordinate).im :=
  rfl

@[simp] theorem coefficientReal_zero :
    coefficientReal (0 : ComplexCoordinateVector) = 0 := by
  ext coordinate
  simp

@[simp] theorem coefficientImag_zero :
    coefficientImag (0 : ComplexCoordinateVector) = 0 := by
  ext coordinate
  simp

/-- Scalar real part of one complex Fourier character. -/
def realComplexScalarFourierMode
    (wave : IntegerWavevector) (coefficient : ℂ) :
    PhysicalSpace → ℝ :=
  fun x =>
    integerCosine wave x * coefficient.re -
      integerSine wave x * coefficient.im

/-- Real physical vector field represented by one complex Fourier row. -/
def realComplexFourierMode
    (wave : IntegerWavevector)
    (coefficient : ComplexCoordinateVector) :
    PhysicalSpace → PhysicalSpace :=
  fun x =>
    integerCosine wave x • coefficientReal coefficient -
      integerSine wave x • coefficientImag coefficient

theorem realComplexFourierMode_contDiff
    (wave : IntegerWavevector)
    (coefficient : ComplexCoordinateVector) :
    ContDiff ℝ (⊤ : ℕ∞)
      (realComplexFourierMode wave coefficient) := by
  unfold realComplexFourierMode
  have hCosine := integerCosine_contDiff wave
  have hSine := integerSine_contDiff wave
  fun_prop

theorem realComplexFourierMode_latticePeriodic
    (wave : IntegerWavevector)
    (coefficient : ComplexCoordinateVector) :
    LatticePeriodic
      (realComplexFourierMode wave coefficient) := by
  intro shift x
  unfold realComplexFourierMode
  rw [integerCosine_latticePeriodic wave shift x,
    integerSine_latticePeriodic wave shift x]

/-- Fréchet derivative of one real complex-character mode. -/
theorem realComplexFourierMode_fderiv
    (wave : IntegerWavevector)
    (coefficient : ComplexCoordinateVector) :
    fderiv ℝ (realComplexFourierMode wave coefficient) =
      fun x =>
        (fderiv ℝ (integerCosine wave) x).smulRight
            (coefficientReal coefficient) -
          (fderiv ℝ (integerSine wave) x).smulRight
            (coefficientImag coefficient) := by
  have hCosine : Differentiable ℝ (integerCosine wave) :=
    (integerCosine_contDiff wave).differentiable (by simp)
  have hSine : Differentiable ℝ (integerSine wave) :=
    (integerSine_contDiff wave).differentiable (by simp)
  funext x
  unfold realComplexFourierMode
  change
    fderiv ℝ
        ((fun y => integerCosine wave y • coefficientReal coefficient) -
          fun y => integerSine wave y • coefficientImag coefficient) x = _
  rw [fderiv_sub]
  · rw [fderiv_smul_const (hCosine x),
      fderiv_smul_const (hSine x)]
  · fun_prop
  · fun_prop

/-! ## Generic finite physical field -/

/-- Full-signed realization of an arbitrary finite complex coefficient table. -/
def finiteRealComplexFourierField
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    PhysicalSpace → PhysicalSpace :=
  fun x =>
    ∑ wave ∈ modes,
      realComplexFourierMode wave (coefficient wave) x

theorem finiteRealComplexFourierField_contDiff
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    ContDiff ℝ (⊤ : ℕ∞)
      (finiteRealComplexFourierField modes coefficient) := by
  unfold finiteRealComplexFourierField
  exact ContDiff.sum fun wave _ =>
    realComplexFourierMode_contDiff wave (coefficient wave)

theorem finiteRealComplexFourierField_latticePeriodic
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    LatticePeriodic
      (finiteRealComplexFourierField modes coefficient) := by
  intro shift x
  unfold finiteRealComplexFourierField
  apply Finset.sum_congr rfl
  intro wave _
  exact
    realComplexFourierMode_latticePeriodic
      wave (coefficient wave) shift x

/-- Fréchet differentiation commutes with the actual finite field sum. -/
theorem finiteRealComplexFourierField_fderiv
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    fderiv ℝ (finiteRealComplexFourierField modes coefficient) =
      fun x =>
        ∑ wave ∈ modes,
          fderiv ℝ
            (realComplexFourierMode wave (coefficient wave)) x := by
  funext x
  unfold finiteRealComplexFourierField
  rw [fderiv_fun_sum]
  intro wave _
  exact
    (realComplexFourierMode_contDiff wave (coefficient wave))
      |>.differentiable (by simp) x

/-! ## Fourier symbols for divergence and curl -/

/-- Complex scalar coefficient of physical divergence at one frequency. -/
def fourierDivergenceCoefficient
    (wave : IntegerWavevector)
    (coefficient : ComplexCoordinateVector) : ℂ :=
  (Complex.I * (((2 * Real.pi : ℝ) : ℂ))) *
    (complexWavevector wave ⬝ᵥ coefficient)

/-- Physical divergence agrees with its complex Fourier multiplier. -/
theorem velocityDivergence_realComplexFourierMode
    (wave : IntegerWavevector)
    (coefficient : ComplexCoordinateVector) :
    velocityDivergence
        (realComplexFourierMode wave coefficient) =
      realComplexScalarFourierMode wave
        (fourierDivergenceCoefficient wave coefficient) := by
  funext x
  unfold velocityDivergence velocityDivergenceReadout
    velocityDivergenceReadoutLinear
  rw [realComplexFourierMode_fderiv,
    integerCosine_fderiv, integerSine_fderiv]
  simp [Fin.sum_univ_succ, realComplexScalarFourierMode,
    fourierDivergenceCoefficient, dotProduct,
    complexWavevector, coefficientReal, coefficientImag,
    integerWavePhaseLinear_single, integerAngularCoefficient,
    integerCosine, integerSine]
  ring

/-- Right-handed physical curl agrees with its complex Fourier multiplier. -/
theorem vorticityField_realComplexFourierMode
    (wave : IntegerWavevector)
    (coefficient : ComplexCoordinateVector) :
    vorticityField
        (realComplexFourierMode wave coefficient) =
      realComplexFourierMode wave
        (fourierCurlCoefficient wave coefficient) := by
  funext x
  unfold vorticityField
  rw [realComplexFourierMode_fderiv,
    integerCosine_fderiv, integerSine_fderiv]
  rw [vorticityReadout_apply]
  ext coordinate
  fin_cases coordinate <;>
    simp [realComplexFourierMode, coefficientReal, coefficientImag,
      fourierCurlCoefficient, complexWavevector, cross_apply,
      integerWavePhaseLinear_single, integerAngularCoefficient,
      integerCosine, integerSine] <;>
    ring

/-- Curl commutes with the complete finite Fourier realization. -/
theorem vorticityField_finiteRealComplexFourierField
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    vorticityField
        (finiteRealComplexFourierField modes coefficient) =
      finiteRealComplexFourierField modes
        (fun wave => fourierCurlCoefficient wave (coefficient wave)) := by
  funext x
  unfold vorticityField finiteRealComplexFourierField
  rw [fderiv_fun_sum]
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro wave _
    exact congrFun
      (vorticityField_realComplexFourierMode
        wave (coefficient wave)) x
  · intro wave _
    exact
      (realComplexFourierMode_contDiff wave (coefficient wave))
        |>.differentiable (by simp) x

/-- Divergence commutes with the complete finite Fourier realization. -/
theorem velocityDivergence_finiteRealComplexFourierField
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    velocityDivergence
        (finiteRealComplexFourierField modes coefficient) =
      fun x =>
        ∑ wave ∈ modes,
          realComplexScalarFourierMode wave
            (fourierDivergenceCoefficient wave (coefficient wave)) x := by
  funext x
  unfold velocityDivergence finiteRealComplexFourierField
  rw [fderiv_fun_sum]
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro wave _
    exact congrFun
      (velocityDivergence_realComplexFourierMode
        wave (coefficient wave)) x
  · intro wave _
    exact
      (realComplexFourierMode_contDiff wave (coefficient wave))
        |>.differentiable (by simp) x

/-! ## Raw-source specialization -/

/-- Full-signed physical velocity generated by the raw source. -/
def physicalVelocity
    (source : RawVorticityFourierSource) :
    PhysicalSpace → PhysicalSpace :=
  finiteRealComplexFourierField
    (generatedSupport source)
    (generatedVelocityCoefficient source)

/-- Full-signed physical vorticity generated by the raw source. -/
def physicalVorticity
    (source : RawVorticityFourierSource) :
    PhysicalSpace → PhysicalSpace :=
  finiteRealComplexFourierField
    (generatedSupport source)
    (generatedVorticityCoefficient source)

theorem physicalVelocity_contDiff
    (source : RawVorticityFourierSource) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalVelocity source) :=
  finiteRealComplexFourierField_contDiff _ _

theorem physicalVorticity_contDiff
    (source : RawVorticityFourierSource) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalVorticity source) :=
  finiteRealComplexFourierField_contDiff _ _

theorem physicalVelocity_latticePeriodic
    (source : RawVorticityFourierSource) :
    LatticePeriodic (physicalVelocity source) :=
  finiteRealComplexFourierField_latticePeriodic _ _

theorem physicalVorticity_latticePeriodic
    (source : RawVorticityFourierSource) :
    LatticePeriodic (physicalVorticity source) :=
  finiteRealComplexFourierField_latticePeriodic _ _

/-- The source-generated transverse law forces physical incompressibility. -/
theorem velocityDivergence_physicalVelocity_eq_zero
    (source : RawVorticityFourierSource) :
    velocityDivergence (physicalVelocity source) = 0 := by
  rw [physicalVelocity,
    velocityDivergence_finiteRealComplexFourierField]
  funext x
  apply Finset.sum_eq_zero
  intro wave _
  have transverse := generatedVelocityCoefficient_transverse source wave
  simp [fourierDivergenceCoefficient, transverse,
    realComplexScalarFourierMode]

/-- The source Biot--Savart coefficient identity survives physical curl. -/
theorem vorticityField_physicalVelocity
    (source : RawVorticityFourierSource) :
    vorticityField (physicalVelocity source) =
      physicalVorticity source := by
  rw [physicalVelocity,
    vorticityField_finiteRealComplexFourierField]
  unfold physicalVorticity finiteRealComplexFourierField
  funext x
  apply Finset.sum_congr rfl
  intro wave _
  change
    realComplexFourierMode wave
        (fourierCurlCoefficient wave
          (generatedVelocityCoefficient source wave)) x =
      realComplexFourierMode wave
        (generatedVorticityCoefficient source wave) x
  rw [fourierCurlCoefficient_generatedVelocityCoefficient]

end

end ThreeDimensionalVorticityCoefficientPhysicalCompiler
end NavierStokes
end SaturationMonoid
