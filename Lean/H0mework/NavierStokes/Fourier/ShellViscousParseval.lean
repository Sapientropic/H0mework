import H0mework.NavierStokes.Fourier.LocalEnergyLedger
import H0mework.NavierStokes.ShellSources.TraceCumulative
import H0mework.NavierStokes.InitialData.PhysicalFourierCoordinateObserver

/-!
# Generated-shell Biot--Savart and physical Parseval identities

This module connects the source-generated finite vorticity carrier to the
actual unit-volume physical torus.  It first proves the one-frequency
Biot--Savart norm identity with the repository character normalization
`exp (i 2π k · x)`.  Source transversality then removes the only geometric
side condition, and an actual integer-shell receipt supplies the nonzero
frequency and exact shell label on site.

The second layer proves finite physical Parseval by pairing each real Fourier
row against the already verified unit-cell complex-coordinate observer.
Consequently both the source-generated velocity and vorticity fields have
premise-free physical `L²` readouts.

The normalization deliberately distinguishes the two viscous quantities:

* energy dissipation has Fourier density `ν |ω̂(k)|²`;
* enstrophy dissipation has Fourier density
  `ν (2π)² |k|² |ω̂(k)|²`.

No divergence-free, signed-coverage, nonzero-amplitude, time, or continuation
certificate is accepted by the public source theorems.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval

open MeasureTheory

open scoped BigOperators Matrix

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalPeriodicUnitCellDivergence
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicLocalEnergyAlgebra
open ThreeDimensionalPeriodicLocalEnergyLedger
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientPhysicalFourierCoordinateObserver

noncomputable section

/-! ## Exact one-frequency Biot--Savart norm -/

/-- The Hermitian self-pairing is the finite coordinate norm squared. -/
theorem vectorConj_dot_self_eq_complexCoordinateVectorNormSq
    (vector : ComplexCoordinateVector) :
    vectorConj vector ⬝ᵥ vector =
      (complexCoordinateVectorNormSq vector : ℂ) := by
  unfold dotProduct complexCoordinateVectorNormSq
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/-- A real wavevector pairs with a conjugate row by complex conjugation. -/
theorem complexWavevector_dot_vectorConj
    (wave : IntegerWavevector)
    (vector : ComplexCoordinateVector) :
    complexWavevector wave ⬝ᵥ vectorConj vector =
      star (complexWavevector wave ⬝ᵥ vector) := by
  simp [dotProduct, vectorConj, complexWavevector]

/--
Exact complex Lagrange identity.  The final nonnegative term is precisely the
longitudinal component lost by the cross product.
-/
theorem complexWavevector_cross_normSq
    (wave : IntegerWavevector)
    (vector : ComplexCoordinateVector) :
    complexCoordinateVectorNormSq
        (complexWavevector wave ⨯₃ vector) =
      integerWaveNormSq wave *
          complexCoordinateVectorNormSq vector -
        Complex.normSq
          (complexWavevector wave ⬝ᵥ vector) := by
  apply Complex.ofReal_injective
  rw [← vectorConj_dot_self_eq_complexCoordinateVectorNormSq,
    vectorConj_crossProduct,
    vectorConj_complexWavevector,
    cross_dot_cross,
    complexWavevector_dot_self,
    vectorConj_dot_self_eq_complexCoordinateVectorNormSq,
    dotProduct_comm
      (vectorConj vector) (complexWavevector wave),
    complexWavevector_dot_vectorConj]
  rw [mul_comm
    (complexWavevector wave ⬝ᵥ vector)
    (star (complexWavevector wave ⬝ᵥ vector))]
  change
    (integerWaveNormSq wave : ℂ) *
          (complexCoordinateVectorNormSq vector : ℂ) -
        (starRingEnd ℂ)
            (complexWavevector wave ⬝ᵥ vector) *
          (complexWavevector wave ⬝ᵥ vector) =
      _
  rw [← Complex.normSq_eq_conj_mul_self]
  push_cast
  rfl

/-- The cross-product row obeys the sharp finite-dimensional norm bound. -/
theorem complexWavevector_cross_normSq_le
    (wave : IntegerWavevector)
    (vector : ComplexCoordinateVector) :
    complexCoordinateVectorNormSq
        (complexWavevector wave ⨯₃ vector) ≤
      integerWaveNormSq wave *
        complexCoordinateVectorNormSq vector := by
  rw [complexWavevector_cross_normSq]
  exact
    sub_le_self _
      (Complex.normSq_nonneg
        (complexWavevector wave ⬝ᵥ vector))

/--
For a transverse row, crossing with the real integer wavevector multiplies
the coordinate norm squared by the exact real shell norm.
-/
theorem complexWavevector_cross_normSq_of_transverse
    (wave : IntegerWavevector)
    (vector : ComplexCoordinateVector)
    (transverse :
      complexWavevector wave ⬝ᵥ vector = 0) :
    complexCoordinateVectorNormSq
        (complexWavevector wave ⨯₃ vector) =
      integerWaveNormSq wave *
        complexCoordinateVectorNormSq vector := by
  apply Complex.ofReal_injective
  rw [← vectorConj_dot_self_eq_complexCoordinateVectorNormSq,
    vectorConj_crossProduct,
    vectorConj_complexWavevector,
    cross_dot_cross,
    complexWavevector_dot_self,
    vectorConj_dot_self_eq_complexCoordinateVectorNormSq,
    transverse]
  simp

/-- Complex scalar multiplication scales the coordinate norm by `normSq`. -/
theorem complexCoordinateVectorNormSq_smul
    (scalar : ℂ)
    (vector : ComplexCoordinateVector) :
    complexCoordinateVectorNormSq (scalar • vector) =
      Complex.normSq scalar *
        complexCoordinateVectorNormSq vector := by
  unfold complexCoordinateVectorNormSq
  simp_rw [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  rw [Finset.mul_sum]

/--
General Biot--Savart norm bound at one nonzero frequency.  Unlike the exact
transverse theorem below, this statement applies to an arbitrary complex
coordinate row.
-/
theorem biotSavartVelocityCoefficient_normSq_le
    (wave : IntegerWavevector)
    (vorticity : ComplexCoordinateVector)
    (waveNe : wave ≠ 0) :
    complexCoordinateVectorNormSq
        (biotSavartVelocityCoefficient wave vorticity) ≤
      complexCoordinateVectorNormSq vorticity /
        ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) := by
  rw [biotSavartVelocityCoefficient, if_neg waveNe,
    complexCoordinateVectorNormSq_smul,
    Complex.normSq_div,
    Complex.normSq_I,
    Complex.normSq_ofReal]
  have waveNormPos : 0 < integerWaveNormSq wave :=
    integerWaveNormSq_pos waveNe
  have crossBound :=
    complexWavevector_cross_normSq_le wave vorticity
  have scalarNonneg :
      0 ≤
        1 /
          ((2 * Real.pi * integerWaveNormSq wave) *
            (2 * Real.pi * integerWaveNormSq wave)) := by
    positivity
  calc
    1 /
          ((2 * Real.pi * integerWaveNormSq wave) *
            (2 * Real.pi * integerWaveNormSq wave)) *
        complexCoordinateVectorNormSq
          (complexWavevector wave ⨯₃ vorticity) ≤
      1 /
          ((2 * Real.pi * integerWaveNormSq wave) *
            (2 * Real.pi * integerWaveNormSq wave)) *
        (integerWaveNormSq wave *
          complexCoordinateVectorNormSq vorticity) :=
      mul_le_mul_of_nonneg_left crossBound scalarNonneg
    _ =
      complexCoordinateVectorNormSq vorticity /
        ((2 * Real.pi) ^ 2 *
          integerWaveNormSq wave) := by
      field_simp

/--
Exact one-frequency Biot--Savart norm with the repository's `2π`
character normalization.
-/
theorem biotSavartVelocityCoefficient_normSq_of_transverse
    (wave : IntegerWavevector)
    (vorticity : ComplexCoordinateVector)
    (waveNe : wave ≠ 0)
    (transverse :
      complexWavevector wave ⬝ᵥ vorticity = 0) :
    complexCoordinateVectorNormSq
        (biotSavartVelocityCoefficient wave vorticity) =
      complexCoordinateVectorNormSq vorticity /
        ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) := by
  rw [biotSavartVelocityCoefficient, if_neg waveNe,
    complexCoordinateVectorNormSq_smul,
    Complex.normSq_div,
    Complex.normSq_I,
    Complex.normSq_ofReal,
    complexWavevector_cross_normSq_of_transverse
      wave vorticity transverse]
  have waveNormNe : integerWaveNormSq wave ≠ 0 :=
    integerWaveNormSq_ne_zero waveNe
  have piNe : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/--
The raw source internally generates the transverse row, so its velocity
coefficient satisfies the exact Biot--Savart norm identity without a caller
hypothesis.  The zero row is handled by source zero extension.
-/
theorem generatedVelocityCoefficient_normSq
    (source : RawVorticityFourierSource)
    (wave : IntegerWavevector) :
    complexCoordinateVectorNormSq
        (generatedVelocityCoefficient source wave) =
      complexCoordinateVectorNormSq
          (generatedVorticityCoefficient source wave) /
        ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) := by
  by_cases waveZero : wave = 0
  · subst wave
    simp [complexCoordinateVectorNormSq]
  · exact
      biotSavartVelocityCoefficient_normSq_of_transverse
        wave
        (generatedVorticityCoefficient source wave)
        waveZero
        (generatedVorticityCoefficient_transverse source wave)

/--
An actual successful whole-shell receipt supplies both the nonzero frequency
and its exact source-selected shell.  Nonlinear transversality is generated
by the pair-swap cancellation theorem, not accepted as a premise here.
-/
theorem generatedIntegerShellReceipt_biotSavartNormSq
    (receipt : GeneratedIntegerShellReceipt)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ receipt.wholeShellModes) :
    complexCoordinateVectorNormSq
        (biotSavartVelocityCoefficient wave
          (generatedVorticityNonlinearCoefficientAt
            receipt.current wave)) =
      complexCoordinateVectorNormSq
          (generatedVorticityNonlinearCoefficientAt
            receipt.current wave) /
        ((2 * Real.pi) ^ 2 *
          (receipt.selectedShellSq : ℝ)) := by
  have waveNe : wave ≠ 0 := by
    intro waveZero
    subst wave
    exact
      zero_not_mem_generatedOuterNonlinearShellModes
        receipt.current receipt.selectedShellSq waveMem
  rw [biotSavartVelocityCoefficient_normSq_of_transverse
    wave
    (generatedVorticityNonlinearCoefficientAt
      receipt.current wave)
    waveNe
    (generatedVorticityNonlinearCoefficientAt_transverse
      receipt.current wave),
    integerWaveNormSq_eq_integerWaveShellSq]
  rw [((mem_generatedOuterNonlinearShellModes_iff
    receipt.current receipt.selectedShellSq wave).mp waveMem).2]

/-! ## Actual physical Fourier-coordinate readout for vorticity -/

/--
The unit-cell observer recovers every generated vorticity coefficient.
Signed closure, conjugate reality, and zero extension all come from the raw
source.
-/
theorem physicalUnitCellComplexFourierCoordinate_physicalVorticity
    (source : RawVorticityFourierSource)
    (testing : IntegerWavevector) :
    physicalUnitCellComplexFourierCoordinate testing
        (physicalVorticity source) =
      generatedVorticityCoefficient source testing := by
  rw [physicalVorticity,
    physicalUnitCellComplexFourierCoordinate_finiteRealComplexFourierField]
  funext coordinate
  by_cases membership : testing ∈ generatedSupport source
  · have negMembership :
        waveNeg testing ∈ generatedSupport source :=
      generatedSupport_waveNeg_mem source membership
    rw [if_pos membership, if_pos negMembership,
      generatedVorticityCoefficient_waveNeg]
    simp
  · have negNotMembership :
        waveNeg testing ∉ generatedSupport source := by
      simpa using membership
    rw [if_neg membership, if_neg negNotMembership,
      generatedVorticityCoefficient_eq_zero_of_not_mem
        source membership]
    simp

/-! ## Finite unit-cell Parseval -/

/-- Real Euclidean pairing of two finite complex coordinate rows. -/
def complexCoordinateRealInner
    (left right : ComplexCoordinateVector) : ℝ :=
  Finset.univ.sum fun coordinate =>
    (left coordinate).re * (right coordinate).re +
      (left coordinate).im * (right coordinate).im

@[simp] theorem complexCoordinateRealInner_self
    (vector : ComplexCoordinateVector) :
    complexCoordinateRealInner vector vector =
      complexCoordinateVectorNormSq vector := by
  unfold complexCoordinateRealInner complexCoordinateVectorNormSq
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [Complex.normSq_apply]

private theorem
    physicalUnitCell_velocityDot_realComplexFourierMode_field_integral
    (wave : IntegerWavevector)
    (coefficient : ComplexCoordinateVector)
    (field : PhysicalSpace → PhysicalSpace)
    (fieldContinuous : Continuous field) :
    (∫ x in physicalUnitCell,
      velocityDot
        (realComplexFourierMode wave coefficient)
        field x) =
      complexCoordinateRealInner coefficient
        (physicalUnitCellComplexFourierCoordinate wave field) := by
  have coordinateContinuous : ∀ (coordinate : Coordinate),
      Continuous (fun x => field x coordinate) := by
    intro coordinate
    fun_prop
  have cosineFieldIntegrable : ∀ (coordinate : Coordinate),
      IntegrableOn
        (fun x =>
          integerCosine wave x * field x coordinate)
        physicalUnitCell := by
    intro coordinate
    exact
      ((integerCosine_continuous wave).mul
        (coordinateContinuous coordinate))
        |>.continuousOn.integrableOn_compact
          physicalUnitCell_isCompact
  have sineFieldIntegrable : ∀ (coordinate : Coordinate),
      IntegrableOn
        (fun x =>
          integerSine wave x * field x coordinate)
        physicalUnitCell := by
    intro coordinate
    exact
      ((integerSine_continuous wave).mul
        (coordinateContinuous coordinate))
        |>.continuousOn.integrableOn_compact
          physicalUnitCell_isCompact
  unfold velocityDot
  rw [integral_finsetSum]
  · unfold complexCoordinateRealInner
      physicalUnitCellComplexFourierCoordinate
    apply Finset.sum_congr rfl
    intro coordinate _
    calc
      (∫ x in physicalUnitCell,
          realComplexFourierMode wave coefficient x coordinate *
            field x coordinate) =
          ∫ x in physicalUnitCell,
            (coefficient coordinate).re *
                (integerCosine wave x * field x coordinate) -
              (coefficient coordinate).im *
                (integerSine wave x * field x coordinate) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [realComplexFourierMode,
          PiLp.sub_apply, PiLp.smul_apply,
          coefficientReal_apply, coefficientImag_apply]
        ring
      _ =
          (coefficient coordinate).re *
              (∫ x in physicalUnitCell,
                integerCosine wave x * field x coordinate) -
            (coefficient coordinate).im *
              (∫ x in physicalUnitCell,
                integerSine wave x * field x coordinate) := by
        rw [integral_sub
          ((cosineFieldIntegrable coordinate).const_mul _)
          ((sineFieldIntegrable coordinate).const_mul _),
          integral_const_mul, integral_const_mul]
      _ =
          (coefficient coordinate).re *
              (((((∫ x in physicalUnitCell,
                  integerCosine wave x *
                    field x coordinate) : ℝ) : ℂ) -
                Complex.I *
                  (((∫ x in physicalUnitCell,
                    integerSine wave x *
                      field x coordinate) : ℝ) : ℂ)).re) +
            (coefficient coordinate).im *
              (((((∫ x in physicalUnitCell,
                  integerCosine wave x *
                    field x coordinate) : ℝ) : ℂ) -
                Complex.I *
                  (((∫ x in physicalUnitCell,
                    integerSine wave x *
                      field x coordinate) : ℝ) : ℂ)).im) := by
        simp
        ring
  · intro coordinate _
    have modeCoordinateContinuous :
        Continuous
          (fun x =>
            realComplexFourierMode
              wave coefficient x coordinate) := by
      unfold realComplexFourierMode
      change Continuous (fun x =>
        integerCosine wave x * (coefficient coordinate).re -
          integerSine wave x * (coefficient coordinate).im)
      exact
        ((integerCosine_continuous wave).mul continuous_const).sub
          ((integerSine_continuous wave).mul continuous_const)
    exact
      (modeCoordinateContinuous.mul
        (coordinateContinuous coordinate))
        |>.continuousOn.integrableOn_compact
          physicalUnitCell_isCompact

/--
Exact unit-cell pairing of a finite trigonometric field with an arbitrary
continuous physical field.  This is the physical/coefficient commuting seam
used by finite-test weak formulations.
-/
theorem physicalUnitCell_finiteRealComplexFourierField_pairing
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector)
    (field : PhysicalSpace → PhysicalSpace)
    (fieldContinuous : Continuous field) :
    (∫ x in physicalUnitCell,
      velocityDot
        (finiteRealComplexFourierField modes coefficient)
        field x) =
      ∑ wave ∈ modes,
        complexCoordinateRealInner (coefficient wave)
          (physicalUnitCellComplexFourierCoordinate wave field) := by
  have rowPairingIntegrable : ∀ wave ∈ modes,
      IntegrableOn
        (fun x =>
          velocityDot
            (realComplexFourierMode wave (coefficient wave))
            field x)
        physicalUnitCell := by
    intro wave _
    have dotContinuous : Continuous (fun x =>
        velocityDot
          (realComplexFourierMode wave (coefficient wave))
          field x) := by
      unfold velocityDot
      apply continuous_finsetSum
      intro coordinate _
      have modeCoordinateContinuous :
          Continuous (fun x =>
            realComplexFourierMode
              wave (coefficient wave) x coordinate) := by
        unfold realComplexFourierMode
        change Continuous (fun x =>
          integerCosine wave x *
              (coefficient wave coordinate).re -
            integerSine wave x *
              (coefficient wave coordinate).im)
        exact
          ((integerCosine_continuous wave).mul continuous_const).sub
            ((integerSine_continuous wave).mul continuous_const)
      have fieldCoordinateContinuous :
          Continuous (fun x => field x coordinate) := by
        fun_prop
      exact modeCoordinateContinuous.mul fieldCoordinateContinuous
    exact
      dotContinuous.continuousOn.integrableOn_compact
        physicalUnitCell_isCompact
  calc
    (∫ x in physicalUnitCell,
      velocityDot
        (finiteRealComplexFourierField modes coefficient)
        field x) =
      ∫ x in physicalUnitCell,
        ∑ wave ∈ modes,
          velocityDot
            (realComplexFourierMode wave (coefficient wave))
            field x := by
      apply integral_congr_ae
      filter_upwards with x
      unfold finiteRealComplexFourierField velocityDot
      simp only [WithLp.ofLp_sum, Finset.sum_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [Finset.sum_mul]
    _ =
      ∑ wave ∈ modes,
        ∫ x in physicalUnitCell,
          velocityDot
            (realComplexFourierMode wave (coefficient wave))
            field x := by
      rw [integral_finsetSum modes rowPairingIntegrable]
    _ =
      ∑ wave ∈ modes,
        complexCoordinateRealInner (coefficient wave)
          (physicalUnitCellComplexFourierCoordinate wave field) := by
      apply Finset.sum_congr rfl
      intro wave _
      rw [
        physicalUnitCell_velocityDot_realComplexFourierMode_field_integral
          wave (coefficient wave) field fieldContinuous]

/--
Finite Parseval from an exact unit-cell observer on the supplied inventory.
This is a readout theorem; the two source specializations below discharge the
observer law from generated signed reality.
-/
theorem
    physicalUnitCell_finiteRealComplexFourierField_parseval_of_observer
    (modes : Finset IntegerWavevector)
    (coefficient :
      IntegerWavevector → ComplexCoordinateVector)
    (observerExact : ∀ wave ∈ modes,
      physicalUnitCellComplexFourierCoordinate wave
          (finiteRealComplexFourierField modes coefficient) =
        coefficient wave) :
    (∫ x in physicalUnitCell,
      velocityDot
        (finiteRealComplexFourierField modes coefficient)
        (finiteRealComplexFourierField modes coefficient) x) =
      ∑ wave ∈ modes,
        complexCoordinateVectorNormSq (coefficient wave) := by
  have fieldContinuous : Continuous
      (finiteRealComplexFourierField modes coefficient) :=
    (finiteRealComplexFourierField_contDiff modes coefficient).continuous
  rw [physicalUnitCell_finiteRealComplexFourierField_pairing
    modes coefficient
    (finiteRealComplexFourierField modes coefficient)
    fieldContinuous]
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [observerExact wave waveMem, complexCoordinateRealInner_self]

/-!
The actual physical velocity has the exact finite Parseval ledger.  The
observer premise of the generic internal lemma is discharged by the
source-generated signed coefficient theorem.
-/
theorem physicalUnitCell_physicalVelocity_parseval
    (source : RawVorticityFourierSource) :
    (∫ x in physicalUnitCell,
      velocityDot
        (physicalVelocity source)
        (physicalVelocity source) x) =
      ∑ wave ∈ generatedSupport source,
        complexCoordinateVectorNormSq
          (generatedVelocityCoefficient source wave) := by
  exact
    physicalUnitCell_finiteRealComplexFourierField_parseval_of_observer
      (generatedSupport source)
      (generatedVelocityCoefficient source)
      fun wave _ =>
        physicalUnitCellComplexFourierCoordinate_physicalVelocity
          source wave

/--
The actual physical vorticity has the exact finite Parseval ledger.
-/
theorem physicalUnitCell_physicalVorticity_parseval
    (source : RawVorticityFourierSource) :
    (∫ x in physicalUnitCell,
      velocityDot
        (physicalVorticity source)
        (physicalVorticity source) x) =
      ∑ wave ∈ generatedSupport source,
        complexCoordinateVectorNormSq
          (generatedVorticityCoefficient source wave) := by
  exact
    physicalUnitCell_finiteRealComplexFourierField_parseval_of_observer
      (generatedSupport source)
      (generatedVorticityCoefficient source)
      fun wave _ =>
        physicalUnitCellComplexFourierCoordinate_physicalVorticity
          source wave

/-! ## Exact physical derivatives of finite coefficient fields -/

/-- Fourier coefficient of one physical coordinate derivative. -/
def angularDerivativeCoefficient
    (coefficient :
      IntegerWavevector → ComplexCoordinateVector)
    (direction : Coordinate)
    (wave : IntegerWavevector) :
    ComplexCoordinateVector :=
  (Complex.I *
      (integerAngularCoefficient wave direction : ℂ)) •
    coefficient wave

@[simp] theorem integerAngularCoefficient_waveNeg
    (wave : IntegerWavevector)
    (direction : Coordinate) :
    integerAngularCoefficient (waveNeg wave) direction =
      -integerAngularCoefficient wave direction := by
  simp [integerAngularCoefficient, waveNeg]

/-- Angular differentiation preserves a supplied signed reality law. -/
theorem angularDerivativeCoefficient_waveNeg
    (coefficient :
      IntegerWavevector → ComplexCoordinateVector)
    (reality :
      ∀ wave,
        coefficient (waveNeg wave) =
          vectorConj (coefficient wave))
    (direction : Coordinate)
    (wave : IntegerWavevector) :
    angularDerivativeCoefficient
        coefficient direction (waveNeg wave) =
      vectorConj
        (angularDerivativeCoefficient
          coefficient direction wave) := by
  rw [angularDerivativeCoefficient,
    angularDerivativeCoefficient,
    integerAngularCoefficient_waveNeg,
    reality,
    vectorConj_smul]
  funext coordinate
  simp [vectorConj]

private theorem angularDerivativeCoefficient_eq_zero
    (coefficient :
      IntegerWavevector → ComplexCoordinateVector)
    (direction : Coordinate)
    {wave : IntegerWavevector}
    (coefficientZero : coefficient wave = 0) :
    angularDerivativeCoefficient
        coefficient direction wave = 0 := by
  rw [angularDerivativeCoefficient, coefficientZero]
  simp

/--
The actual Fréchet derivative of one real complex-character row is the row
with coefficient multiplied by `i 2π kⱼ`.
-/
theorem realComplexFourierMode_coordinateDerivative
    (wave : IntegerWavevector)
    (coefficient : ComplexCoordinateVector)
    (direction : Coordinate)
    (x : PhysicalSpace) :
    fderiv ℝ
        (realComplexFourierMode wave coefficient) x
        (EuclideanSpace.single direction 1) =
      realComplexFourierMode wave
        (angularDerivativeCoefficient
          (fun _ => coefficient) direction wave) x := by
  rw [congrFun
    (realComplexFourierMode_fderiv wave coefficient) x,
    integerCosine_fderiv, integerSine_fderiv]
  simp only [_root_.sub_apply,
    ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,
    integerWavePhaseLinear_single]
  ext coordinate
  simp [angularDerivativeCoefficient,
    realComplexFourierMode, coefficientReal, coefficientImag,
    integerCosine, integerSine]
  ring

/-- Physical differentiation commutes with the complete finite inventory. -/
theorem finiteRealComplexFourierField_coordinateDerivative
    (modes : Finset IntegerWavevector)
    (coefficient :
      IntegerWavevector → ComplexCoordinateVector)
    (direction : Coordinate)
    (x : PhysicalSpace) :
    fderiv ℝ
        (finiteRealComplexFourierField modes coefficient) x
        (EuclideanSpace.single direction 1) =
      finiteRealComplexFourierField modes
        (angularDerivativeCoefficient
          coefficient direction) x := by
  rw [congrFun
    (finiteRealComplexFourierField_fderiv
      modes coefficient) x]
  unfold finiteRealComplexFourierField
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro wave _
  exact
    realComplexFourierMode_coordinateDerivative
      wave (coefficient wave) direction x

/--
Pointwise gradient square of a finite field as the sum of the three
directional derivative-field squares.
-/
theorem gradientDissipation_finiteRealComplexFourierField
    (modes : Finset IntegerWavevector)
    (coefficient :
      IntegerWavevector → ComplexCoordinateVector)
    (x : PhysicalSpace) :
    gradientDissipation
        (finiteRealComplexFourierField modes coefficient) x =
      ∑ direction : Coordinate,
        velocityDot
          (finiteRealComplexFourierField modes
            (angularDerivativeCoefficient
              coefficient direction))
          (finiteRealComplexFourierField modes
            (angularDerivativeCoefficient
              coefficient direction)) x := by
  unfold gradientDissipation velocityDot
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro direction _
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [finiteRealComplexFourierField_coordinateDerivative
    modes coefficient direction x]
  change
    (finiteRealComplexFourierField modes
      (angularDerivativeCoefficient
        coefficient direction) x coordinate) ^ 2 =
    finiteRealComplexFourierField modes
        (angularDerivativeCoefficient
          coefficient direction) x coordinate *
      finiteRealComplexFourierField modes
        (angularDerivativeCoefficient
          coefficient direction) x coordinate
  rw [pow_two]

/-- Sum of the three exact derivative-row norms at one frequency. -/
theorem angularDerivativeCoefficient_normSq_sum
    (coefficient :
      IntegerWavevector → ComplexCoordinateVector)
    (wave : IntegerWavevector) :
    (∑ direction : Coordinate,
      complexCoordinateVectorNormSq
        (angularDerivativeCoefficient
          coefficient direction wave)) =
      (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
        complexCoordinateVectorNormSq
          (coefficient wave) := by
  unfold angularDerivativeCoefficient
  simp_rw [complexCoordinateVectorNormSq_smul,
    Complex.normSq_mul, Complex.normSq_I, one_mul,
    Complex.normSq_ofReal, integerAngularCoefficient]
  rw [← Finset.sum_mul]
  congr 1
  unfold integerWaveNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro direction _
  ring

private theorem velocityDot_self_integrableOn_of_continuous
    (field : PhysicalSpace → PhysicalSpace)
    (fieldContinuous : Continuous field) :
    IntegrableOn
      (fun x => velocityDot field field x)
      physicalUnitCell := by
  have dotContinuous :
      Continuous (fun x => velocityDot field field x) := by
    unfold velocityDot
    apply continuous_finsetSum
    intro coordinate _
    have coordinateContinuous :
        Continuous (fun x => field x coordinate) := by
      fun_prop
    exact coordinateContinuous.mul coordinateContinuous
  exact
    dotContinuous.continuousOn.integrableOn_compact
      physicalUnitCell_isCompact

/--
Gradient Parseval from exact observers on the three derivative inventories.
This is a finite readout theorem; source specializations below generate the
observer laws internally.
-/
theorem
    physicalUnitCell_gradientDissipation_parseval_of_derivativeObserver
    (modes : Finset IntegerWavevector)
    (coefficient :
      IntegerWavevector → ComplexCoordinateVector)
    (derivativeObserverExact :
      ∀ direction, ∀ wave ∈ modes,
        physicalUnitCellComplexFourierCoordinate wave
            (finiteRealComplexFourierField modes
              (angularDerivativeCoefficient
                coefficient direction)) =
          angularDerivativeCoefficient
            coefficient direction wave) :
    (∫ x in physicalUnitCell,
      gradientDissipation
        (finiteRealComplexFourierField modes coefficient) x) =
      ∑ wave ∈ modes,
        (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
          complexCoordinateVectorNormSq
            (coefficient wave) := by
  have directionalIntegrable :
      ∀ direction : Coordinate,
        IntegrableOn
          (fun x =>
            velocityDot
              (finiteRealComplexFourierField modes
                (angularDerivativeCoefficient
                  coefficient direction))
              (finiteRealComplexFourierField modes
                (angularDerivativeCoefficient
                  coefficient direction)) x)
          physicalUnitCell := by
    intro direction
    exact
      velocityDot_self_integrableOn_of_continuous _
        (finiteRealComplexFourierField_contDiff
          modes
          (angularDerivativeCoefficient
            coefficient direction)).continuous
  calc
    (∫ x in physicalUnitCell,
      gradientDissipation
        (finiteRealComplexFourierField modes coefficient) x) =
      ∫ x in physicalUnitCell,
        ∑ direction : Coordinate,
          velocityDot
            (finiteRealComplexFourierField modes
              (angularDerivativeCoefficient
                coefficient direction))
            (finiteRealComplexFourierField modes
              (angularDerivativeCoefficient
                coefficient direction)) x := by
      apply integral_congr_ae
      filter_upwards with x
      exact
        gradientDissipation_finiteRealComplexFourierField
          modes coefficient x
    _ =
      ∑ direction : Coordinate,
        ∫ x in physicalUnitCell,
          velocityDot
            (finiteRealComplexFourierField modes
              (angularDerivativeCoefficient
                coefficient direction))
            (finiteRealComplexFourierField modes
              (angularDerivativeCoefficient
                coefficient direction)) x := by
      rw [integral_finsetSum]
      intro direction _
      exact directionalIntegrable direction
    _ =
      ∑ direction : Coordinate,
        ∑ wave ∈ modes,
          complexCoordinateVectorNormSq
            (angularDerivativeCoefficient
              coefficient direction wave) := by
      apply Finset.sum_congr rfl
      intro direction _
      exact
        physicalUnitCell_finiteRealComplexFourierField_parseval_of_observer
          modes
          (angularDerivativeCoefficient
            coefficient direction)
          fun wave waveMem =>
            derivativeObserverExact
              direction wave waveMem
    _ =
      ∑ wave ∈ modes,
        ∑ direction : Coordinate,
          complexCoordinateVectorNormSq
            (angularDerivativeCoefficient
              coefficient direction wave) := by
      rw [Finset.sum_comm]
    _ =
      ∑ wave ∈ modes,
        (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
          complexCoordinateVectorNormSq
            (coefficient wave) := by
      apply Finset.sum_congr rfl
      intro wave _
      exact
        angularDerivativeCoefficient_normSq_sum
          coefficient wave

/-! ## Source-generated derivative observers -/

private theorem generatedVelocityCoefficient_eq_zero_of_not_mem
    (source : RawVorticityFourierSource)
    {wave : IntegerWavevector}
    (notMem : wave ∉ generatedSupport source) :
    generatedVelocityCoefficient source wave = 0 := by
  rw [generatedVelocityCoefficient,
    generatedVorticityCoefficient_eq_zero_of_not_mem
      source notMem,
    biotSavartVelocityCoefficient_zero_vorticity]

private theorem
    physicalUnitCellComplexFourierCoordinate_generatedDerivative
    (source : RawVorticityFourierSource)
    (coefficient :
      IntegerWavevector → ComplexCoordinateVector)
    (reality :
      ∀ wave,
        coefficient (waveNeg wave) =
          vectorConj (coefficient wave))
    (zeroOutside :
      ∀ {wave}, wave ∉ generatedSupport source →
        coefficient wave = 0)
    (direction : Coordinate)
    (testing : IntegerWavevector) :
    physicalUnitCellComplexFourierCoordinate testing
        (finiteRealComplexFourierField
          (generatedSupport source)
          (angularDerivativeCoefficient
            coefficient direction)) =
      angularDerivativeCoefficient
        coefficient direction testing := by
  rw [
    physicalUnitCellComplexFourierCoordinate_finiteRealComplexFourierField]
  funext coordinate
  by_cases membership : testing ∈ generatedSupport source
  · have negMembership :
        waveNeg testing ∈ generatedSupport source :=
      generatedSupport_waveNeg_mem source membership
    rw [if_pos membership, if_pos negMembership,
      angularDerivativeCoefficient_waveNeg
        coefficient reality]
    simp
  · have negNotMembership :
        waveNeg testing ∉ generatedSupport source := by
      simpa using membership
    rw [if_neg membership, if_neg negNotMembership,
      angularDerivativeCoefficient_eq_zero
        coefficient direction (zeroOutside membership)]
    simp

/-- Exact derivative observer for the source-generated velocity field. -/
theorem
    physicalUnitCellComplexFourierCoordinate_generatedVelocityDerivative
    (source : RawVorticityFourierSource)
    (direction : Coordinate)
    (testing : IntegerWavevector) :
    physicalUnitCellComplexFourierCoordinate testing
        (finiteRealComplexFourierField
          (generatedSupport source)
          (angularDerivativeCoefficient
            (generatedVelocityCoefficient source)
            direction)) =
      angularDerivativeCoefficient
        (generatedVelocityCoefficient source)
        direction testing :=
  physicalUnitCellComplexFourierCoordinate_generatedDerivative
    source
    (generatedVelocityCoefficient source)
    (generatedVelocityCoefficient_waveNeg source)
    (generatedVelocityCoefficient_eq_zero_of_not_mem source)
    direction testing

/-- Exact derivative observer for the source-generated vorticity field. -/
theorem
    physicalUnitCellComplexFourierCoordinate_generatedVorticityDerivative
    (source : RawVorticityFourierSource)
    (direction : Coordinate)
    (testing : IntegerWavevector) :
    physicalUnitCellComplexFourierCoordinate testing
        (finiteRealComplexFourierField
          (generatedSupport source)
          (angularDerivativeCoefficient
            (generatedVorticityCoefficient source)
            direction)) =
      angularDerivativeCoefficient
        (generatedVorticityCoefficient source)
        direction testing :=
  physicalUnitCellComplexFourierCoordinate_generatedDerivative
    source
    (generatedVorticityCoefficient source)
    (generatedVorticityCoefficient_waveNeg source)
    (generatedVorticityCoefficient_eq_zero_of_not_mem source)
    direction testing

/-! ## Energy and enstrophy dissipation are different readouts -/

/-- Spectral gradient ledger of the actual source-generated velocity. -/
theorem physicalUnitCell_physicalVelocity_gradient_parseval
    (source : RawVorticityFourierSource) :
    (∫ x in physicalUnitCell,
      gradientDissipation (physicalVelocity source) x) =
      ∑ wave ∈ generatedSupport source,
        (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
          complexCoordinateVectorNormSq
            (generatedVelocityCoefficient source wave) := by
  exact
    physicalUnitCell_gradientDissipation_parseval_of_derivativeObserver
      (generatedSupport source)
      (generatedVelocityCoefficient source)
      fun direction wave _ =>
        physicalUnitCellComplexFourierCoordinate_generatedVelocityDerivative
          source direction wave

/-- Spectral gradient ledger of the actual source-generated vorticity. -/
theorem physicalUnitCell_physicalVorticity_gradient_parseval
    (source : RawVorticityFourierSource) :
    (∫ x in physicalUnitCell,
      gradientDissipation (physicalVorticity source) x) =
      ∑ wave ∈ generatedSupport source,
        (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
          complexCoordinateVectorNormSq
            (generatedVorticityCoefficient source wave) := by
  exact
    physicalUnitCell_gradientDissipation_parseval_of_derivativeObserver
      (generatedSupport source)
      (generatedVorticityCoefficient source)
      fun direction wave _ =>
        physicalUnitCellComplexFourierCoordinate_generatedVorticityDerivative
          source direction wave

/--
Energy dissipation identity:
`∫ |∇u|² = ∑ |ω̂(k)|²`.

The source supplies nonzero support, transversality, and Biot--Savart
inversion; none is accepted from the caller.
-/
theorem
    physicalUnitCell_physicalVelocity_gradient_eq_vorticityNormSq
    (source : RawVorticityFourierSource) :
    (∫ x in physicalUnitCell,
      gradientDissipation (physicalVelocity source) x) =
      ∑ wave ∈ generatedSupport source,
        complexCoordinateVectorNormSq
          (generatedVorticityCoefficient source wave) := by
  rw [physicalUnitCell_physicalVelocity_gradient_parseval]
  apply Finset.sum_congr rfl
  intro wave waveMem
  have waveNe : wave ≠ 0 := by
    intro waveZero
    subst wave
    exact zero_not_mem_generatedSupport source waveMem
  rw [generatedVelocityCoefficient_normSq]
  have waveNormNe : integerWaveNormSq wave ≠ 0 :=
    integerWaveNormSq_ne_zero waveNe
  have piNe : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/--
Equivalent physical form of the divergence-free periodic identity
`∫ |∇u|² = ∫ |curl u|²`.
-/
theorem
    physicalUnitCell_physicalVelocity_gradient_eq_vorticityL2
    (source : RawVorticityFourierSource) :
    (∫ x in physicalUnitCell,
      gradientDissipation (physicalVelocity source) x) =
      ∫ x in physicalUnitCell,
        velocityDot
          (physicalVorticity source)
          (physicalVorticity source) x := by
  rw [
    physicalUnitCell_physicalVelocity_gradient_eq_vorticityNormSq,
    physicalUnitCell_physicalVorticity_parseval]

/--
Viscous energy dissipation.  Its spectral density is `ν |ω̂(k)|²`;
there is no additional shell factor.
-/
theorem physicalUnitCell_viscousEnergyDissipation_parseval
    (ν : Viscosity)
    (source : RawVorticityFourierSource) :
    (∫ x in physicalUnitCell,
      viscousDissipation ν (physicalVelocity source) x) =
      ν.coeff *
        ∑ wave ∈ generatedSupport source,
          complexCoordinateVectorNormSq
            (generatedVorticityCoefficient source wave) := by
  unfold viscousDissipation
  rw [integral_const_mul,
    physicalUnitCell_physicalVelocity_gradient_eq_vorticityNormSq]

/--
Viscous enstrophy dissipation.  In contrast with energy dissipation, its
spectral density is `ν (2π)² |k|² |ω̂(k)|²`.
-/
theorem physicalUnitCell_viscousEnstrophyDissipation_parseval
    (ν : Viscosity)
    (source : RawVorticityFourierSource) :
    (∫ x in physicalUnitCell,
      viscousDissipation ν (physicalVorticity source) x) =
      ν.coeff *
        ∑ wave ∈ generatedSupport source,
          (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
            complexCoordinateVectorNormSq
              (generatedVorticityCoefficient source wave) := by
  unfold viscousDissipation
  rw [integral_const_mul,
    physicalUnitCell_physicalVorticity_gradient_parseval]

end

end ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
end NavierStokes
end SaturationMonoid
