import H0mework.NavierStokes.Fourier.NonlinearPairGenerator

/-!
# Physical bridge for the generated vorticity nonlinear pair table

The coefficient source already generates every ordered nonlinear pair row

```text
(omega_p dot nabla) u_q - (u_p dot nabla) omega_q.
```

This module proves that full-signed physical realization commutes with that
generation.  The existing stretching bridge supplies the first term.  For
vorticity advection, the real-character product first produces sum- and
difference-frequency halves; source-generated negation of the advecting slot
reindexes the difference half on the same complete pair table.  The final
coefficient is therefore one.

The resulting field is exactly
`-vorticityAdvection (physicalVelocity source) +
vortexStretching (physicalVelocity source)`.  Every public theorem mouth
contains only the raw source.  This module introduces no update, filter,
trajectory, successor, or PDE solution.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientNonlinearPhysicalBridge

open scoped BigOperators Matrix

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFullVorticityStretching
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicIntegerCharacterOrthogonality
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientStretchingPhysicalBridge

noncomputable section

/-! ## One vorticity-advection row -/

private theorem integerWavePhase_waveNeg
    (wave : IntegerWavevector) (x : PhysicalSpace) :
    integerWavePhase (waveNeg wave) x = -integerWavePhase wave x := by
  simp [integerWavePhase, waveNeg]

private theorem realComplexScalarFourierMode_smul_realComplexFourierMode
    (first second : IntegerWavevector)
    (scalar : ℂ) (vector : ComplexCoordinateVector)
    (x : PhysicalSpace) :
    (realComplexScalarFourierMode first scalar x) •
        realComplexFourierMode second vector x =
      (1 / 2 : ℝ) •
        (realComplexFourierMode (first + second)
            (scalar • vector) x +
          realComplexFourierMode (waveNeg first + second)
            (star scalar • vector) x) := by
  ext coordinate
  simp [realComplexScalarFourierMode, realComplexFourierMode,
    coefficientReal, coefficientImag,
    integerCosine, integerSine,
    integerWavePhase_wavevector_add,
    integerWavePhase_waveNeg,
    Real.cos_add, Real.sin_add,
    Real.cos_neg, Real.sin_neg]
  ring

private theorem integerWavePhaseLinear_realComplexFourierMode
    (direction wave : IntegerWavevector)
    (coefficient : ComplexCoordinateVector)
    (x : PhysicalSpace) :
    integerWavePhaseLinear direction
        (realComplexFourierMode wave coefficient x) =
      (2 * Real.pi) *
        realComplexScalarFourierMode wave
          (complexWavevector direction ⬝ᵥ coefficient) x := by
  rw [integerWavePhaseLinear_apply]
  simp [integerWavePhase, realComplexFourierMode,
    realComplexScalarFourierMode, coefficientReal, coefficientImag,
    dotProduct, complexWavevector, Fin.sum_univ_three]
  ring

private theorem fderiv_realComplexFourierMode_along_realComplexFourierMode
    (directionWave differentiatedWave : IntegerWavevector)
    (directionCoefficient differentiatedCoefficient : ComplexCoordinateVector)
    (x : PhysicalSpace) :
    fderiv ℝ
        (realComplexFourierMode differentiatedWave
          differentiatedCoefficient) x
        (realComplexFourierMode directionWave directionCoefficient x) =
      (realComplexScalarFourierMode directionWave
          (complexWavevector differentiatedWave ⬝ᵥ
            directionCoefficient) x) •
        realComplexFourierMode differentiatedWave
          ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) •
            differentiatedCoefficient) x := by
  rw [congrFun
    (realComplexFourierMode_fderiv
      differentiatedWave differentiatedCoefficient) x]
  rw [integerCosine_fderiv, integerSine_fderiv]
  simp only [_root_.sub_apply,
    ContinuousLinearMap.smulRight_apply, _root_.smul_apply]
  rw [integerWavePhaseLinear_realComplexFourierMode]
  ext coordinate
  simp [realComplexFourierMode, realComplexScalarFourierMode,
    coefficientReal, coefficientImag, integerCosine, integerSine]
  ring

private theorem complexWavevector_dot_vectorConj
    (wave : IntegerWavevector)
    (vector : ComplexCoordinateVector) :
    complexWavevector wave ⬝ᵥ vectorConj vector =
      star (complexWavevector wave ⬝ᵥ vector) := by
  simp [dotProduct, complexWavevector, vectorConj]

private theorem advectionSymbol_smul_eq_pairContribution
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) :
    (complexWavevector pair.2 ⬝ᵥ
        generatedVelocityCoefficient source pair.1) •
        ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) •
          generatedVorticityCoefficient source pair.2) =
      generatedVorticityAdvectionPairContribution source pair := by
  funext coordinate
  simp [generatedVorticityAdvectionPairContribution]
  ring

private theorem advectionSymbol_star_smul_eq_firstNegContribution
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) :
    star (complexWavevector pair.2 ⬝ᵥ
        generatedVelocityCoefficient source pair.1) •
        ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) •
          generatedVorticityCoefficient source pair.2) =
      generatedVorticityAdvectionPairContribution source
        (stretchingPairFirstNeg pair) := by
  rw [generatedVorticityAdvectionPairContribution,
    stretchingPairFirstNeg,
    generatedVelocityCoefficient_waveNeg,
    complexWavevector_dot_vectorConj]
  funext coordinate
  simp
  ring

/-- One physical vorticity-advection derivative row is the exact average of
its sum-frequency row and source-generated first-slot-negated row. -/
theorem fderiv_generatedVorticityRow_along_generatedVelocityRow
    (source : RawVorticityFourierSource)
    (pair : StretchingPair)
    (x : PhysicalSpace) :
    fderiv ℝ
        (realComplexFourierMode pair.2
          (generatedVorticityCoefficient source pair.2)) x
        (realComplexFourierMode pair.1
          (generatedVelocityCoefficient source pair.1) x) =
      (1 / 2 : ℝ) •
        (realComplexFourierMode (stretchingPairOutput pair)
            (generatedVorticityAdvectionPairContribution source pair) x +
          realComplexFourierMode
            (stretchingPairOutput (stretchingPairFirstNeg pair))
            (generatedVorticityAdvectionPairContribution source
              (stretchingPairFirstNeg pair)) x) := by
  rw [fderiv_realComplexFourierMode_along_realComplexFourierMode]
  rw [realComplexScalarFourierMode_smul_realComplexFourierMode]
  rw [advectionSymbol_smul_eq_pairContribution,
    advectionSymbol_star_smul_eq_firstNegContribution]
  rfl

/-! ## Complete advection table -/

/-- Full-signed physical realization of the complete vorticity-advection
pair table. -/
def generatedVorticityAdvectionPairField
    (source : RawVorticityFourierSource) :
    PhysicalSpace → PhysicalSpace :=
  fun x =>
    ∑ pair ∈ generatedStretchingPairTable source,
      realComplexFourierMode (stretchingPairOutput pair)
        (generatedVorticityAdvectionPairContribution source pair) x

private theorem generatedVorticityAdvectionPairField_firstNeg
    (source : RawVorticityFourierSource) :
    (fun x =>
      ∑ pair ∈ generatedStretchingPairTable source,
        realComplexFourierMode
          (stretchingPairOutput (stretchingPairFirstNeg pair))
          (generatedVorticityAdvectionPairContribution source
            (stretchingPairFirstNeg pair)) x) =
      generatedVorticityAdvectionPairField source := by
  funext x
  unfold generatedVorticityAdvectionPairField
  refine Finset.sum_equiv stretchingPairFirstNegEquiv ?_ ?_
  · intro pair
    exact
      (mem_generatedStretchingPairTable_firstNeg_iff
        source pair).symm
  · intro pair membership
    rfl

private theorem vorticityAdvection_physicalVelocity_apply_eq_pairDerivativeSum
    (source : RawVorticityFourierSource)
    (x : PhysicalSpace) :
    vorticityAdvection (physicalVelocity source) x =
      ∑ pair ∈ generatedStretchingPairTable source,
        fderiv ℝ
          (realComplexFourierMode pair.2
            (generatedVorticityCoefficient source pair.2)) x
          (realComplexFourierMode pair.1
            (generatedVelocityCoefficient source pair.1) x) := by
  unfold vorticityAdvection
  rw [vorticityField_physicalVelocity]
  rw [physicalVelocity, physicalVorticity,
    finiteRealComplexFourierField_fderiv]
  change
    (∑ differentiatedWave ∈ generatedSupport source,
        fderiv ℝ
          (realComplexFourierMode differentiatedWave
            (generatedVorticityCoefficient source differentiatedWave)) x)
        (∑ directionWave ∈ generatedSupport source,
          realComplexFourierMode directionWave
            (generatedVelocityCoefficient source directionWave) x) =
      ∑ pair ∈
          generatedSupport source ×ˢ generatedSupport source,
        fderiv ℝ
          (realComplexFourierMode pair.2
            (generatedVorticityCoefficient source pair.2)) x
          (realComplexFourierMode pair.1
            (generatedVelocityCoefficient source pair.1) x)
  rw [map_sum]
  simp only [_root_.sum_apply]
  exact
    (Finset.sum_product
      (generatedSupport source) (generatedSupport source)
      (fun pair =>
        fderiv ℝ
          (realComplexFourierMode pair.2
            (generatedVorticityCoefficient source pair.2)) x
          (realComplexFourierMode pair.1
            (generatedVelocityCoefficient source pair.1) x))).symm

/-- The complete source-generated advection table compiles to the actual
physical vorticity-advection field. -/
theorem vorticityAdvection_physicalVelocity_eq_generatedAdvectionPairField
    (source : RawVorticityFourierSource) :
    vorticityAdvection (physicalVelocity source) =
      generatedVorticityAdvectionPairField source := by
  funext x
  rw [vorticityAdvection_physicalVelocity_apply_eq_pairDerivativeSum]
  simp_rw [fderiv_generatedVorticityRow_along_generatedVelocityRow]
  unfold generatedVorticityAdvectionPairField
  rw [← Finset.smul_sum]
  simp only [Finset.sum_add_distrib]
  rw [show
    (∑ pair ∈ generatedStretchingPairTable source,
      realComplexFourierMode
        (stretchingPairOutput (stretchingPairFirstNeg pair))
        (generatedVorticityAdvectionPairContribution source
          (stretchingPairFirstNeg pair)) x) =
      ∑ pair ∈ generatedStretchingPairTable source,
        realComplexFourierMode (stretchingPairOutput pair)
          (generatedVorticityAdvectionPairContribution source pair) x by
      exact congrFun
        (generatedVorticityAdvectionPairField_firstNeg source) x]
  module

/-! ## Full nonlinear commuting square -/

/-- Full-signed physical realization of the generated nonlinear pair table. -/
def generatedVorticityNonlinearPairField
    (source : RawVorticityFourierSource) :
    PhysicalSpace → PhysicalSpace :=
  fun x =>
    ∑ pair ∈ generatedStretchingPairTable source,
      realComplexFourierMode (stretchingPairOutput pair)
        (generatedVorticityNonlinearPairContribution source pair) x

private theorem realComplexFourierMode_sub
    (wave : IntegerWavevector)
    (left right : ComplexCoordinateVector) :
    realComplexFourierMode wave (left - right) =
      realComplexFourierMode wave left -
        realComplexFourierMode wave right := by
  funext x
  ext coordinate
  simp [realComplexFourierMode, coefficientReal, coefficientImag]
  ring

theorem generatedVorticityNonlinearPairField_eq_stretching_sub_advection
    (source : RawVorticityFourierSource) :
    generatedVorticityNonlinearPairField source =
      generatedStretchingPairField source -
        generatedVorticityAdvectionPairField source := by
  funext x
  unfold generatedVorticityNonlinearPairField
    generatedStretchingPairField
    generatedVorticityAdvectionPairField
  simp_rw [generatedVorticityNonlinearPairContribution,
    realComplexFourierMode_sub]
  simp only [Pi.sub_apply]
  rw [Finset.sum_sub_distrib]

/-- Physical realization commutes with the complete source-generated
vorticity nonlinearity, with the repository PDE sign convention. -/
theorem generatedVorticityNonlinearPairField_eq_physicalNonlinearity
    (source : RawVorticityFourierSource) :
    generatedVorticityNonlinearPairField source =
      -vorticityAdvection (physicalVelocity source) +
        vortexStretching (physicalVelocity source) := by
  rw [generatedVorticityNonlinearPairField_eq_stretching_sub_advection,
    ← vortexStretching_physicalVelocity_eq_generatedPairField,
    ← vorticityAdvection_physicalVelocity_eq_generatedAdvectionPairField]
  abel

/-! ## Empty-source negative controls -/

@[simp] theorem zeroRawVorticitySource_generatedVorticityAdvectionPairField :
    generatedVorticityAdvectionPairField zeroRawVorticitySource = 0 := by
  funext x
  simp [generatedVorticityAdvectionPairField]

@[simp] theorem zeroRawVorticitySource_generatedVorticityNonlinearPairField :
    generatedVorticityNonlinearPairField zeroRawVorticitySource = 0 := by
  funext x
  simp [generatedVorticityNonlinearPairField]

end

end ThreeDimensionalVorticityCoefficientNonlinearPhysicalBridge
end NavierStokes
end SaturationMonoid
