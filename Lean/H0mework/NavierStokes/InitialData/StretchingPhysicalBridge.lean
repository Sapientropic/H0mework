import H0mework.NavierStokes.Fourier.IntegerCharacterOrthogonality
import H0mework.NavierStokes.InitialData.PhysicalCompiler
import H0mework.NavierStokes.Fourier.StretchingPairTable

/-!
# Physical realization of the generated three-dimensional stretching table

The raw vorticity source already generates a complete signed Fourier support,
its physical velocity and vorticity fields, and the complete ordered table of
vorticity--velocity interactions.  This module proves that those two routes
commute: compiling the whole pair table is exactly the physical vortex-
stretching field of the compiled velocity.

The proof retains both character channels of each real-mode product.  The
difference-frequency channel is not discarded; negation in the first pair
slot reindexes it into the sum-frequency channel on the same source-owned
table.  Thus the final coefficient is one, with no selected pair, target
frequency, reality, transversality, or nonvanishing premise.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientStretchingPhysicalBridge

open scoped BigOperators

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFullVorticityStretching
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicIntegerCharacterOrthogonality
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable

noncomputable section

/-! ## Character product and one-row derivative -/

private theorem integerWavePhase_waveNeg
    (wave : IntegerWavevector) (x : PhysicalSpace) :
    integerWavePhase (waveNeg wave) x = -integerWavePhase wave x := by
  simp [integerWavePhase, waveNeg]

/-- A real scalar character times a real vector character has its exact
sum- and difference-frequency decomposition. -/
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

/-- Applying the phase covector to one real vector character produces the
real scalar character of the complex dot product, including the angular
factor `2π`. -/
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

/-- The actual derivative of one velocity row along one vorticity row is a
scalar character times the velocity character carrying the Fourier
derivative symbol. -/
private theorem fderiv_realComplexFourierMode_along_realComplexFourierMode
    (vorticityWave velocityWave : IntegerWavevector)
    (vorticityCoefficient velocityCoefficient : ComplexCoordinateVector)
    (x : PhysicalSpace) :
    fderiv ℝ
        (realComplexFourierMode velocityWave velocityCoefficient) x
        (realComplexFourierMode vorticityWave vorticityCoefficient x) =
      (realComplexScalarFourierMode vorticityWave
          (complexWavevector velocityWave ⬝ᵥ vorticityCoefficient) x) •
        realComplexFourierMode velocityWave
          ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) •
            velocityCoefficient) x := by
  rw [congrFun
    (realComplexFourierMode_fderiv
      velocityWave velocityCoefficient) x]
  rw [integerCosine_fderiv, integerSine_fderiv]
  simp only [sub_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply]
  rw [integerWavePhaseLinear_realComplexFourierMode]
  ext coordinate
  simp [realComplexFourierMode, realComplexScalarFourierMode,
    coefficientReal, coefficientImag, integerCosine, integerSine]
  ring

/-! ## First-slot negation and the exact source row -/

/-- Negate only the vorticity slot of an ordered stretching pair. -/
def stretchingPairFirstNeg (pair : StretchingPair) : StretchingPair :=
  (waveNeg pair.1, pair.2)

@[simp] theorem stretchingPairFirstNeg_involutive
    (pair : StretchingPair) :
    stretchingPairFirstNeg (stretchingPairFirstNeg pair) = pair := by
  rcases pair with ⟨first, second⟩
  simp [stretchingPairFirstNeg]

/-- First-slot negation as an involution of the ambient pair carrier. -/
def stretchingPairFirstNegEquiv : StretchingPair ≃ StretchingPair where
  toFun := stretchingPairFirstNeg
  invFun := stretchingPairFirstNeg
  left_inv := stretchingPairFirstNeg_involutive
  right_inv := stretchingPairFirstNeg_involutive

@[simp] theorem mem_generatedStretchingPairTable_firstNeg_iff
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) :
    stretchingPairFirstNeg pair ∈ generatedStretchingPairTable source ↔
      pair ∈ generatedStretchingPairTable source := by
  simp [stretchingPairFirstNeg]

private theorem complexWavevector_dot_vectorConj
    (wave : IntegerWavevector)
    (vector : ComplexCoordinateVector) :
    complexWavevector wave ⬝ᵥ vectorConj vector =
      star (complexWavevector wave ⬝ᵥ vector) := by
  simp [dotProduct, complexWavevector, vectorConj]

private theorem stretchingSymbol_smul_eq_pairContribution
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) :
    (complexWavevector pair.2 ⬝ᵥ
        generatedVorticityCoefficient source pair.1) •
        ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) •
          generatedVelocityCoefficient source pair.2) =
      generatedStretchingPairContribution source pair := by
  funext coordinate
  simp [generatedStretchingPairContribution]
  ring

private theorem stretchingSymbol_star_smul_eq_firstNegContribution
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) :
    star (complexWavevector pair.2 ⬝ᵥ
        generatedVorticityCoefficient source pair.1) •
        ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) •
          generatedVelocityCoefficient source pair.2) =
      generatedStretchingPairContribution source
        (stretchingPairFirstNeg pair) := by
  rw [generatedStretchingPairContribution,
    stretchingPairFirstNeg,
    generatedVorticityCoefficient_waveNeg,
    complexWavevector_dot_vectorConj]
  funext coordinate
  simp
  ring

/-- One physical derivative row is the average of its sum-frequency row and
the source-generated first-slot-negated row. -/
theorem fderiv_generatedVelocityRow_along_generatedVorticityRow
    (source : RawVorticityFourierSource)
    (pair : StretchingPair)
    (x : PhysicalSpace) :
    fderiv ℝ
        (realComplexFourierMode pair.2
          (generatedVelocityCoefficient source pair.2)) x
        (realComplexFourierMode pair.1
          (generatedVorticityCoefficient source pair.1) x) =
      (1 / 2 : ℝ) •
        (realComplexFourierMode (stretchingPairOutput pair)
            (generatedStretchingPairContribution source pair) x +
          realComplexFourierMode
            (stretchingPairOutput (stretchingPairFirstNeg pair))
            (generatedStretchingPairContribution source
              (stretchingPairFirstNeg pair)) x) := by
  rw [fderiv_realComplexFourierMode_along_realComplexFourierMode]
  rw [realComplexScalarFourierMode_smul_realComplexFourierMode]
  rw [stretchingSymbol_smul_eq_pairContribution,
    stretchingSymbol_star_smul_eq_firstNegContribution]
  rfl

/-! ## Complete pair-table physical field -/

/-- Full-signed physical realization of the one complete stretching table. -/
def generatedStretchingPairField
    (source : RawVorticityFourierSource) :
    PhysicalSpace → PhysicalSpace :=
  fun x =>
    ∑ pair ∈ generatedStretchingPairTable source,
      realComplexFourierMode (stretchingPairOutput pair)
        (generatedStretchingPairContribution source pair) x

/-- First-slot negation reindexes the complete source table without changing
its full physical sum. -/
theorem generatedStretchingPairField_firstNeg
    (source : RawVorticityFourierSource) :
    (fun x =>
      ∑ pair ∈ generatedStretchingPairTable source,
        realComplexFourierMode
          (stretchingPairOutput (stretchingPairFirstNeg pair))
          (generatedStretchingPairContribution source
            (stretchingPairFirstNeg pair)) x) =
      generatedStretchingPairField source := by
  funext x
  unfold generatedStretchingPairField
  refine Finset.sum_equiv stretchingPairFirstNegEquiv ?_ ?_
  · intro pair
    exact
      (mem_generatedStretchingPairTable_firstNeg_iff
        source pair).symm
  · intro pair membership
    rfl

private theorem vortexStretching_physicalVelocity_apply_eq_pairDerivativeSum
    (source : RawVorticityFourierSource)
    (x : PhysicalSpace) :
    vortexStretching (physicalVelocity source) x =
      ∑ pair ∈ generatedStretchingPairTable source,
        fderiv ℝ
          (realComplexFourierMode pair.2
            (generatedVelocityCoefficient source pair.2)) x
          (realComplexFourierMode pair.1
            (generatedVorticityCoefficient source pair.1) x) := by
  unfold vortexStretching
  rw [vorticityField_physicalVelocity]
  rw [physicalVelocity, physicalVorticity,
    finiteRealComplexFourierField_fderiv]
  change
    (∑ velocityWave ∈ generatedSupport source,
        fderiv ℝ
          (realComplexFourierMode velocityWave
            (generatedVelocityCoefficient source velocityWave)) x)
        (∑ vorticityWave ∈ generatedSupport source,
          realComplexFourierMode vorticityWave
            (generatedVorticityCoefficient source vorticityWave) x) =
      ∑ pair ∈
          generatedSupport source ×ˢ generatedSupport source,
        fderiv ℝ
          (realComplexFourierMode pair.2
            (generatedVelocityCoefficient source pair.2)) x
          (realComplexFourierMode pair.1
            (generatedVorticityCoefficient source pair.1) x)
  rw [map_sum]
  simp only [sum_apply]
  exact
    (Finset.sum_product
      (generatedSupport source) (generatedSupport source)
      (fun pair =>
        fderiv ℝ
          (realComplexFourierMode pair.2
            (generatedVelocityCoefficient source pair.2)) x
          (realComplexFourierMode pair.1
            (generatedVorticityCoefficient source pair.1) x))).symm

/-!
The complete square is the commuting statement.  The source first forms its
physical velocity and takes the PDE stretching update on the left; on the
right it first forms every coefficient pair and then compiles their outputs.
-/

/-- The source-generated complete pair table compiles to the actual physical
vortex-stretching field. -/
theorem vortexStretching_physicalVelocity_eq_generatedPairField
    (source : RawVorticityFourierSource) :
    vortexStretching (physicalVelocity source) =
      generatedStretchingPairField source := by
  funext x
  rw [vortexStretching_physicalVelocity_apply_eq_pairDerivativeSum]
  simp_rw [fderiv_generatedVelocityRow_along_generatedVorticityRow]
  unfold generatedStretchingPairField
  rw [← Finset.smul_sum]
  simp only [Finset.sum_add_distrib]
  rw [show
    (∑ pair ∈ generatedStretchingPairTable source,
      realComplexFourierMode
        (stretchingPairOutput (stretchingPairFirstNeg pair))
        (generatedStretchingPairContribution source
          (stretchingPairFirstNeg pair)) x) =
      ∑ pair ∈ generatedStretchingPairTable source,
        realComplexFourierMode (stretchingPairOutput pair)
          (generatedStretchingPairContribution source pair) x by
      exact congrFun
        (generatedStretchingPairField_firstNeg source) x]
  module

end

end ThreeDimensionalVorticityCoefficientStretchingPhysicalBridge
end NavierStokes
end SaturationMonoid
