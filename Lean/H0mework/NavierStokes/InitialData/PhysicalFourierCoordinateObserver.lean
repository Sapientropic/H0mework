import H0mework.NavierStokes.Fourier.IntegerCharacterOrthogonality
import H0mework.NavierStokes.InitialData.PhysicalCompiler

/-!
# Physical unit-cell Fourier-coordinate observer

For a real physical vector field `u`, the actual complex coordinate at an
integer frequency `k` is defined coordinatewise by

```text
integral_cell cos(k*x) u(x) - I integral_cell sin(k*x) u(x).
```

Applied to one real complex row at frequency `l`, the observer reads

```text
((if k=l then a_l else 0) +
  (if k=-l then conjugate(a_l) else 0)) / 2.
```

This formula includes the zero mode, equal frequencies, opposite frequencies,
and absent frequencies without side hypotheses.  Thus one isolated nonzero
row has normalization `1/2`; a complete signed reality pair contributes both
halves.

The finite-inventory theorem keeps both membership tests explicit.  For the
raw source's generated signed support, negative-frequency closure and the
generated reality law then prove, without a frequency or membership premise,
that the physical observer recovers the exact generated velocity coefficient.

This is a coefficient readout theorem.  It does not assert a PDE consequence,
observer injectivity on arbitrary fields, or a higher transport level.
-/

open MeasureTheory

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientPhysicalFourierCoordinateObserver

open scoped BigOperators Matrix

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicIntegerCharacterOrthogonality
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalPeriodicUnitCellDivergence
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientPhysicalCompiler

noncomputable section

/-! ## Actual unit-cell observer -/

/--
Complex Fourier coordinate of a real physical vector field, with the
repository's unit-volume cell normalization.
-/
def physicalUnitCellComplexFourierCoordinate
    (wave : IntegerWavevector)
    (field : PhysicalSpace → PhysicalSpace) : ComplexCoordinateVector :=
  fun coordinate =>
    ((∫ x in physicalUnitCell,
      integerCosine wave x * field x coordinate : ℝ) : ℂ) -
    Complex.I *
      ((∫ x in physicalUnitCell,
        integerSine wave x * field x coordinate : ℝ) : ℂ)

private theorem cosine_realComplexFourierMode_coordinate_integrableOn
    (testing mode : IntegerWavevector)
    (coefficient : ComplexCoordinateVector)
    (coordinate : Coordinate) :
    IntegrableOn
      (fun x => integerCosine testing x *
        realComplexFourierMode mode coefficient x coordinate)
      physicalUnitCell := by
  have continuousIntegrand :
      Continuous
        (fun x => integerCosine testing x *
          realComplexFourierMode mode coefficient x coordinate) := by
    unfold realComplexFourierMode
    change Continuous
      (fun x => integerCosine testing x *
        (integerCosine mode x * (coefficient coordinate).re -
          integerSine mode x * (coefficient coordinate).im))
    exact
      (integerCosine_continuous testing).mul
        (((integerCosine_continuous mode).mul continuous_const).sub
          ((integerSine_continuous mode).mul continuous_const))
  exact continuousIntegrand.continuousOn.integrableOn_compact
    physicalUnitCell_isCompact

private theorem sine_realComplexFourierMode_coordinate_integrableOn
    (testing mode : IntegerWavevector)
    (coefficient : ComplexCoordinateVector)
    (coordinate : Coordinate) :
    IntegrableOn
      (fun x => integerSine testing x *
        realComplexFourierMode mode coefficient x coordinate)
      physicalUnitCell := by
  have continuousIntegrand :
      Continuous
        (fun x => integerSine testing x *
          realComplexFourierMode mode coefficient x coordinate) := by
    unfold realComplexFourierMode
    change Continuous
      (fun x => integerSine testing x *
        (integerCosine mode x * (coefficient coordinate).re -
          integerSine mode x * (coefficient coordinate).im))
    exact
      (integerSine_continuous testing).mul
        (((integerCosine_continuous mode).mul continuous_const).sub
          ((integerSine_continuous mode).mul continuous_const))
  exact continuousIntegrand.continuousOn.integrableOn_compact
    physicalUnitCell_isCompact

/-! ## One-row cosine and sine readings -/

private theorem physicalUnitCell_cosine_realComplexFourierMode_integral
    (testing mode : IntegerWavevector)
    (coefficient : ComplexCoordinateVector)
    (coordinate : Coordinate) :
    (∫ x in physicalUnitCell,
      integerCosine testing x *
        realComplexFourierMode mode coefficient x coordinate) =
      (((if testing = mode then 1 else 0) +
          (if testing = -mode then 1 else 0)) / 2) *
        (coefficient coordinate).re := by
  have cosineCosineIntegrable :
      IntegrableOn
        (fun x =>
          (integerCosine testing x * integerCosine mode x) *
            (coefficient coordinate).re)
        physicalUnitCell :=
    (((integerCosine_continuous testing).mul
      (integerCosine_continuous mode)).mul continuous_const)
      |>.continuousOn.integrableOn_compact physicalUnitCell_isCompact
  have cosineSineIntegrable :
      IntegrableOn
        (fun x =>
          (integerCosine testing x * integerSine mode x) *
            (coefficient coordinate).im)
        physicalUnitCell :=
    (((integerCosine_continuous testing).mul
      (integerSine_continuous mode)).mul continuous_const)
      |>.continuousOn.integrableOn_compact physicalUnitCell_isCompact
  calc
    (∫ x in physicalUnitCell,
        integerCosine testing x *
          realComplexFourierMode mode coefficient x coordinate) =
        ∫ x in physicalUnitCell,
          (integerCosine testing x * integerCosine mode x) *
              (coefficient coordinate).re -
            (integerCosine testing x * integerSine mode x) *
              (coefficient coordinate).im := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [realComplexFourierMode, PiLp.sub_apply,
        PiLp.smul_apply, coefficientReal_apply, coefficientImag_apply]
      ring
    _ =
        (∫ x in physicalUnitCell,
          integerCosine testing x * integerCosine mode x) *
            (coefficient coordinate).re -
        (∫ x in physicalUnitCell,
          integerCosine testing x * integerSine mode x) *
            (coefficient coordinate).im := by
      rw [integral_sub cosineCosineIntegrable cosineSineIntegrable,
        integral_mul_const, integral_mul_const]
    _ =
        (((if testing = mode then 1 else 0) +
            (if testing = -mode then 1 else 0)) / 2) *
          (coefficient coordinate).re := by
      rw [physicalUnitCell_integerCosine_mul_integerCosine_integral,
        physicalUnitCell_integerCosine_mul_integerSine_integral_eq_zero]
      ring

private theorem physicalUnitCell_sine_realComplexFourierMode_integral
    (testing mode : IntegerWavevector)
    (coefficient : ComplexCoordinateVector)
    (coordinate : Coordinate) :
    (∫ x in physicalUnitCell,
      integerSine testing x *
        realComplexFourierMode mode coefficient x coordinate) =
      -(((if testing = mode then 1 else 0) -
          (if testing = -mode then 1 else 0)) / 2) *
        (coefficient coordinate).im := by
  have sineCosineIntegrable :
      IntegrableOn
        (fun x =>
          (integerSine testing x * integerCosine mode x) *
            (coefficient coordinate).re)
        physicalUnitCell :=
    (((integerSine_continuous testing).mul
      (integerCosine_continuous mode)).mul continuous_const)
      |>.continuousOn.integrableOn_compact physicalUnitCell_isCompact
  have sineSineIntegrable :
      IntegrableOn
        (fun x =>
          (integerSine testing x * integerSine mode x) *
            (coefficient coordinate).im)
        physicalUnitCell :=
    (((integerSine_continuous testing).mul
      (integerSine_continuous mode)).mul continuous_const)
      |>.continuousOn.integrableOn_compact physicalUnitCell_isCompact
  calc
    (∫ x in physicalUnitCell,
        integerSine testing x *
          realComplexFourierMode mode coefficient x coordinate) =
        ∫ x in physicalUnitCell,
          (integerSine testing x * integerCosine mode x) *
              (coefficient coordinate).re -
            (integerSine testing x * integerSine mode x) *
              (coefficient coordinate).im := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [realComplexFourierMode, PiLp.sub_apply,
        PiLp.smul_apply, coefficientReal_apply, coefficientImag_apply]
      ring
    _ =
        (∫ x in physicalUnitCell,
          integerSine testing x * integerCosine mode x) *
            (coefficient coordinate).re -
        (∫ x in physicalUnitCell,
          integerSine testing x * integerSine mode x) *
            (coefficient coordinate).im := by
      rw [integral_sub sineCosineIntegrable sineSineIntegrable,
        integral_mul_const, integral_mul_const]
    _ =
        -(((if testing = mode then 1 else 0) -
            (if testing = -mode then 1 else 0)) / 2) *
          (coefficient coordinate).im := by
      rw [physicalUnitCell_integerSine_mul_integerCosine_integral_eq_zero,
        physicalUnitCell_integerSine_mul_integerSine_integral]
      ring

/--
Exact readout of one row.  The two Kronecker terms expose the true `1/2`
normalization and also handle the zero row without a side hypothesis.
-/
theorem physicalUnitCellComplexFourierCoordinate_realComplexFourierMode
    (testing mode : IntegerWavevector)
    (coefficient : ComplexCoordinateVector) :
    physicalUnitCellComplexFourierCoordinate testing
        (realComplexFourierMode mode coefficient) =
      fun coordinate =>
        ((if testing = mode then coefficient coordinate else 0) +
          (if testing = -mode then
            star (coefficient coordinate) else 0)) / 2 := by
  funext coordinate
  rw [physicalUnitCellComplexFourierCoordinate,
    physicalUnitCell_cosine_realComplexFourierMode_integral,
    physicalUnitCell_sine_realComplexFourierMode_integral]
  by_cases equalFrequency : testing = mode
  · subst testing
    by_cases selfOpposite : mode = -mode
    · simp only [if_pos selfOpposite]
      apply Complex.ext <;>
        simp
    · simp only [if_neg selfOpposite]
      apply Complex.ext <;>
        simp <;>
        ring
  · by_cases oppositeFrequency : testing = -mode
    · subst testing
      simp only [if_neg equalFrequency]
      apply Complex.ext <;>
        simp <;>
        ring
    · simp only [if_neg equalFrequency, if_neg oppositeFrequency]
      apply Complex.ext <;>
        simp

/-! ## Arbitrary finite signed inventories -/

private theorem physicalUnitCellComplexFourierCoordinate_finite_sum
    (testing : IntegerWavevector)
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    physicalUnitCellComplexFourierCoordinate testing
        (finiteRealComplexFourierField modes coefficient) =
      ∑ mode ∈ modes,
        physicalUnitCellComplexFourierCoordinate testing
          (realComplexFourierMode mode (coefficient mode)) := by
  classical
  funext coordinate
  unfold physicalUnitCellComplexFourierCoordinate
    finiteRealComplexFourierField
  simp only [WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum]
  rw [integral_finsetSum modes
      (fun mode _ =>
        cosine_realComplexFourierMode_coordinate_integrableOn
          testing mode (coefficient mode) coordinate),
    integral_finsetSum modes
      (fun mode _ =>
        sine_realComplexFourierMode_coordinate_integrableOn
          testing mode (coefficient mode) coordinate)]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]

/--
Exact unit-cell readout on an arbitrary finite inventory.  Every equality,
opposite-frequency match, zero row, and absent row remains internal to the
finite sum.
-/
theorem physicalUnitCellComplexFourierCoordinate_finiteRealComplexFourierField_sum
    (testing : IntegerWavevector)
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    physicalUnitCellComplexFourierCoordinate testing
        (finiteRealComplexFourierField modes coefficient) =
      ∑ mode ∈ modes,
        fun coordinate =>
          ((if testing = mode then coefficient mode coordinate else 0) +
            (if testing = -mode then
              star (coefficient mode coordinate) else 0)) / 2 := by
  rw [physicalUnitCellComplexFourierCoordinate_finite_sum]
  apply Finset.sum_congr rfl
  intro mode modeMembership
  exact
    physicalUnitCellComplexFourierCoordinate_realComplexFourierMode
      testing mode (coefficient mode)

private theorem testing_eq_neg_iff_waveNeg_testing_eq
    (testing mode : IntegerWavevector) :
    testing = -mode ↔ waveNeg testing = mode := by
  constructor
  · intro equality
    simpa [waveNeg] using congrArg Neg.neg equality
  · intro equality
    change -testing = mode at equality
    simpa using congrArg Neg.neg equality

/--
The same formula collapsed to the two possible inventory rows.  It visibly
records whether `k` and `-k` are each present, so no hidden signed-coverage
assumption enters the readout.
-/
theorem physicalUnitCellComplexFourierCoordinate_finiteRealComplexFourierField
    (testing : IntegerWavevector)
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    physicalUnitCellComplexFourierCoordinate testing
        (finiteRealComplexFourierField modes coefficient) =
      fun coordinate =>
        ((if testing ∈ modes then coefficient testing coordinate else 0) +
          (if waveNeg testing ∈ modes then
            star (coefficient (waveNeg testing) coordinate) else 0)) / 2 := by
  rw [physicalUnitCellComplexFourierCoordinate_finiteRealComplexFourierField_sum]
  funext coordinate
  simp only [Finset.sum_apply]
  simp_rw [testing_eq_neg_iff_waveNeg_testing_eq]
  calc
    (∑ mode ∈ modes,
        ((if testing = mode then coefficient mode coordinate else 0) +
          (if waveNeg testing = mode then
            star (coefficient mode coordinate) else 0)) / 2) =
        (∑ mode ∈ modes,
          ((if testing = mode then coefficient mode coordinate else 0) +
            (if waveNeg testing = mode then
              star (coefficient mode coordinate) else 0))) / 2 := by
      symm
      exact Finset.sum_div modes _ 2
    _ =
        ((if testing ∈ modes then coefficient testing coordinate else 0) +
          (if waveNeg testing ∈ modes then
            star (coefficient (waveNeg testing) coordinate) else 0)) / 2 := by
      rw [Finset.sum_add_distrib,
        Finset.sum_ite_eq modes testing,
        Finset.sum_ite_eq modes (waveNeg testing)]

/-! ## Source-generated signed specialization -/

private theorem generatedVelocityCoefficient_eq_zero_of_not_mem
    (source : RawVorticityFourierSource)
    {wave : IntegerWavevector}
    (notMem : wave ∉ generatedSupport source) :
    generatedVelocityCoefficient source wave = 0 := by
  rw [generatedVelocityCoefficient,
    generatedVorticityCoefficient_eq_zero_of_not_mem source notMem,
    biotSavartVelocityCoefficient_zero_vorticity]

/--
The actual physical velocity recovers every generated velocity coefficient.
This is premise-free even at zero and outside the support: the source itself
generates signed closure, conjugate reality, and zero extension.
-/
theorem physicalUnitCellComplexFourierCoordinate_physicalVelocity
    (source : RawVorticityFourierSource)
    (testing : IntegerWavevector) :
    physicalUnitCellComplexFourierCoordinate testing
        (physicalVelocity source) =
      generatedVelocityCoefficient source testing := by
  rw [physicalVelocity,
    physicalUnitCellComplexFourierCoordinate_finiteRealComplexFourierField]
  funext coordinate
  by_cases membership : testing ∈ generatedSupport source
  · have negMembership :
        waveNeg testing ∈ generatedSupport source :=
      generatedSupport_waveNeg_mem source membership
    rw [if_pos membership, if_pos negMembership,
      generatedVelocityCoefficient_waveNeg]
    simp
  · have negNotMembership :
        waveNeg testing ∉ generatedSupport source := by
      simpa using membership
    rw [if_neg membership, if_neg negNotMembership,
      generatedVelocityCoefficient_eq_zero_of_not_mem source membership]
    simp

end

end ThreeDimensionalVorticityCoefficientPhysicalFourierCoordinateObserver
end NavierStokes
end SaturationMonoid
