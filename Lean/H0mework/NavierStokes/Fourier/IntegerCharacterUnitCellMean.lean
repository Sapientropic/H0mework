import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp
import H0mework.NavierStokes.Fourier.IntegerCharacterCoarseFilter
import H0mework.NavierStokes.Fourier.UnitCellDivergence

/-!
# Unit-cell means of nonzero integer characters

The existing integer sine and cosine characters are realized through an
actual continuous-linear phase.  A nonzero coordinate of the wavevector
then generates a periodic single-coordinate vector primitive whose
divergence is exactly the corresponding character.  The existing periodic
unit-cell divergence theorem therefore forces both character means to
vanish.

The hypothesis that the integer wavevector is nonzero is only the
structural frequency condition needed to choose a differentiating
coordinate.  No coarse multiplier, nonvanishing multiplier, faithfulness,
flux sign, or observer conclusion appears here.  Opposite-face
cancellation is consumed from the existing unit-cell theorem rather than
reproved.
-/

open MeasureTheory

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalPeriodicIntegerCharacterUnitCellMean

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicCoarseVectorCalculus
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicUnitCellDivergence

noncomputable section

/-- The continuous-linear realization of the existing integer phase. -/
def integerWavePhaseLinear
    (k : IntegerWavevector) : PhysicalSpace →L[ℝ] ℝ :=
  (2 * Real.pi) •
    ∑ i : Coordinate,
      (k i : ℝ) • EuclideanSpace.proj i

theorem integerWavePhaseLinear_apply
    (k : IntegerWavevector) (x : PhysicalSpace) :
    integerWavePhaseLinear k x = integerWavePhase k x := by
  classical
  simp only [integerWavePhaseLinear, integerWavePhase,
    smul_apply, _root_.sum_apply, EuclideanSpace.coe_proj,
    smul_eq_mul]

theorem integerWavePhase_eq_linear
    (k : IntegerWavevector) :
    integerWavePhase k = integerWavePhaseLinear k := by
  funext x
  exact (integerWavePhaseLinear_apply k x).symm

theorem integerWavePhase_contDiff
    (k : IntegerWavevector) :
    ContDiff ℝ (⊤ : ℕ∞) (integerWavePhase k) := by
  rw [integerWavePhase_eq_linear]
  exact (integerWavePhaseLinear k).contDiff

theorem integerWavePhase_fderiv
    (k : IntegerWavevector) :
    fderiv ℝ (integerWavePhase k) =
      fun _ => integerWavePhaseLinear k := by
  rw [integerWavePhase_eq_linear]
  funext x
  rw [ContinuousLinearMap.fderiv]

theorem integerCosine_contDiff
    (k : IntegerWavevector) :
    ContDiff ℝ (⊤ : ℕ∞) (integerCosine k) := by
  unfold integerCosine
  exact Real.contDiff_cos.comp (integerWavePhase_contDiff k)

theorem integerSine_contDiff
    (k : IntegerWavevector) :
    ContDiff ℝ (⊤ : ℕ∞) (integerSine k) := by
  unfold integerSine
  exact Real.contDiff_sin.comp (integerWavePhase_contDiff k)

theorem integerCosine_fderiv
    (k : IntegerWavevector) :
    fderiv ℝ (integerCosine k) =
      fun x =>
        (-Real.sin (integerWavePhase k x)) •
          integerWavePhaseLinear k := by
  have hPhase :
      Differentiable ℝ (integerWavePhase k) :=
    (integerWavePhase_contDiff k).differentiable (by simp)
  funext x
  unfold integerCosine
  rw [fderiv_cos (hPhase x), integerWavePhase_fderiv]

theorem integerSine_fderiv
    (k : IntegerWavevector) :
    fderiv ℝ (integerSine k) =
      fun x =>
        Real.cos (integerWavePhase k x) •
          integerWavePhaseLinear k := by
  have hPhase :
      Differentiable ℝ (integerWavePhase k) :=
    (integerWavePhase_contDiff k).differentiable (by simp)
  funext x
  unfold integerSine
  rw [fderiv_sin (hPhase x), integerWavePhase_fderiv]

/-- The integer phase accumulated along an integer lattice shift. -/
def integerWavePairing
    (k : IntegerWavevector) (z : IntegerShift) : ℤ :=
  ∑ i : Coordinate, k i * z i

theorem integerWavePhase_latticeShift
    (k : IntegerWavevector) (z : IntegerShift) :
    integerWavePhase k (latticeShift z) =
      (integerWavePairing k z : ℝ) * (2 * Real.pi) := by
  simp only [integerWavePhase, integerWavePairing, latticeShift,
    Int.cast_sum, Int.cast_mul, PiLp.toLp_apply]
  ring

theorem integerWavePhase_add_latticeShift
    (k : IntegerWavevector) (z : IntegerShift)
    (x : PhysicalSpace) :
    integerWavePhase k (x + latticeShift z) =
      integerWavePhase k x +
        (integerWavePairing k z : ℝ) * (2 * Real.pi) := by
  rw [integerWavePhase_add, integerWavePhase_latticeShift]

theorem integerCosine_latticePeriodic
    (k : IntegerWavevector) :
    LatticePeriodic (integerCosine k) := by
  intro z x
  unfold integerCosine
  rw [integerWavePhase_add_latticeShift]
  exact Real.cos_add_int_mul_two_pi _ (integerWavePairing k z)

theorem integerSine_latticePeriodic
    (k : IntegerWavevector) :
    LatticePeriodic (integerSine k) := by
  intro z x
  unfold integerSine
  rw [integerWavePhase_add_latticeShift]
  exact Real.sin_add_int_mul_two_pi _ (integerWavePairing k z)

/-- Angular derivative of character `k` in coordinate `i`. -/
def integerAngularCoefficient
    (k : IntegerWavevector) (i : Coordinate) : ℝ :=
  (2 * Real.pi) * (k i : ℝ)

theorem integerAngularCoefficient_ne_zero
    (k : IntegerWavevector) (i : Coordinate)
    (hki : k i ≠ 0) :
    integerAngularCoefficient k i ≠ 0 := by
  unfold integerAngularCoefficient
  apply mul_ne_zero
  · positivity
  · exact_mod_cast hki

theorem integerWavePhaseLinear_single
    (k : IntegerWavevector) (i : Coordinate) :
    integerWavePhaseLinear k
        (EuclideanSpace.single i (1 : ℝ)) =
      integerAngularCoefficient k i := by
  classical
  simp only [integerWavePhaseLinear,
    integerAngularCoefficient,
    smul_apply, _root_.sum_apply, EuclideanSpace.coe_proj,
    smul_eq_mul]
  simp

/--
A single-coordinate periodic primitive whose divergence is the cosine
character whenever the selected frequency coordinate is nonzero.
-/
def integerCosineDivergencePrimitive
    (k : IntegerWavevector) (i : Coordinate) :
    PhysicalSpace → PhysicalSpace :=
  fun x =>
    ((integerAngularCoefficient k i)⁻¹ *
        integerSine k x) •
      (EuclideanSpace.single i (1 : ℝ) : PhysicalSpace)

/--
A single-coordinate periodic primitive whose divergence is the sine
character whenever the selected frequency coordinate is nonzero.
-/
def integerSineDivergencePrimitive
    (k : IntegerWavevector) (i : Coordinate) :
    PhysicalSpace → PhysicalSpace :=
  fun x =>
    (-(integerAngularCoefficient k i)⁻¹ *
        integerCosine k x) •
      (EuclideanSpace.single i (1 : ℝ) : PhysicalSpace)

theorem integerCosineDivergencePrimitive_contDiff
    (k : IntegerWavevector) (i : Coordinate) :
    ContDiff ℝ 1 (integerCosineDivergencePrimitive k i) := by
  have hSine :
      ContDiff ℝ 1 (integerSine k) :=
    (integerSine_contDiff k).of_le (by simp)
  change
    ContDiff ℝ 1
      (fun x =>
        ((integerAngularCoefficient k i)⁻¹ *
          integerSine k x) •
            (EuclideanSpace.single i (1 : ℝ) : PhysicalSpace))
  exact
    (ContDiff.const_smul
      (integerAngularCoefficient k i)⁻¹ hSine).smul_const
        (EuclideanSpace.single i (1 : ℝ) : PhysicalSpace)

theorem integerSineDivergencePrimitive_contDiff
    (k : IntegerWavevector) (i : Coordinate) :
    ContDiff ℝ 1 (integerSineDivergencePrimitive k i) := by
  have hCosine :
      ContDiff ℝ 1 (integerCosine k) :=
    (integerCosine_contDiff k).of_le (by simp)
  change
    ContDiff ℝ 1
      (fun x =>
        (-(integerAngularCoefficient k i)⁻¹ *
          integerCosine k x) •
            (EuclideanSpace.single i (1 : ℝ) : PhysicalSpace))
  exact
    (ContDiff.const_smul
      (-(integerAngularCoefficient k i)⁻¹) hCosine).smul_const
        (EuclideanSpace.single i (1 : ℝ) : PhysicalSpace)

theorem integerCosineDivergencePrimitive_latticePeriodic
    (k : IntegerWavevector) (i : Coordinate) :
    LatticePeriodic (integerCosineDivergencePrimitive k i) := by
  intro z x
  unfold integerCosineDivergencePrimitive
  rw [integerSine_latticePeriodic k z x]

theorem integerSineDivergencePrimitive_latticePeriodic
    (k : IntegerWavevector) (i : Coordinate) :
    LatticePeriodic (integerSineDivergencePrimitive k i) := by
  intro z x
  unfold integerSineDivergencePrimitive
  rw [integerCosine_latticePeriodic k z x]

private theorem integerCosineDivergencePrimitive_fderiv
    (k : IntegerWavevector) (i : Coordinate) :
    fderiv ℝ (integerCosineDivergencePrimitive k i) =
      fun x =>
        (((integerAngularCoefficient k i)⁻¹ •
            fderiv ℝ (integerSine k) x).smulRight
          (EuclideanSpace.single i 1)) := by
  have hSine :
      Differentiable ℝ (integerSine k) :=
    (integerSine_contDiff k).differentiable (by simp)
  funext x
  unfold integerCosineDivergencePrimitive
  have hScalar :
      DifferentiableAt ℝ
        (fun y =>
          (integerAngularCoefficient k i)⁻¹ *
            integerSine k y) x := by
    fun_prop
  rw [fderiv_smul_const hScalar
    (EuclideanSpace.single i (1 : ℝ))]
  change
    (fderiv ℝ
      ((integerAngularCoefficient k i)⁻¹ •
        integerSine k) x).smulRight
        (EuclideanSpace.single i (1 : ℝ)) = _
  rw [fderiv_const_smul (hSine x)]

private theorem integerSineDivergencePrimitive_fderiv
    (k : IntegerWavevector) (i : Coordinate) :
    fderiv ℝ (integerSineDivergencePrimitive k i) =
      fun x =>
        ((-(integerAngularCoefficient k i)⁻¹ •
            fderiv ℝ (integerCosine k) x).smulRight
          (EuclideanSpace.single i 1)) := by
  have hCosine :
      Differentiable ℝ (integerCosine k) :=
    (integerCosine_contDiff k).differentiable (by simp)
  funext x
  unfold integerSineDivergencePrimitive
  have hScalar :
      DifferentiableAt ℝ
        (fun y =>
          -(integerAngularCoefficient k i)⁻¹ *
            integerCosine k y) x := by
    fun_prop
  rw [fderiv_smul_const hScalar
    (EuclideanSpace.single i (1 : ℝ))]
  change
    (fderiv ℝ
      (-(integerAngularCoefficient k i)⁻¹ •
        integerCosine k) x).smulRight
        (EuclideanSpace.single i (1 : ℝ)) = _
  rw [fderiv_const_smul (hCosine x)]

theorem velocityDivergence_integerCosineDivergencePrimitive
    (k : IntegerWavevector) (i : Coordinate)
    (hki : k i ≠ 0) :
    velocityDivergence
        (integerCosineDivergencePrimitive k i) =
      integerCosine k := by
  have hCoefficient :=
    integerAngularCoefficient_ne_zero k i hki
  funext x
  unfold velocityDivergence velocityDivergenceReadout
    velocityDivergenceReadoutLinear
  rw [integerCosineDivergencePrimitive_fderiv,
    integerSine_fderiv]
  fin_cases i <;>
    simp [Fin.sum_univ_succ, integerWavePhaseLinear_single,
      integerCosine] at hCoefficient ⊢ <;>
    field_simp [hCoefficient]

theorem velocityDivergence_integerSineDivergencePrimitive
    (k : IntegerWavevector) (i : Coordinate)
    (hki : k i ≠ 0) :
    velocityDivergence
        (integerSineDivergencePrimitive k i) =
      integerSine k := by
  have hCoefficient :=
    integerAngularCoefficient_ne_zero k i hki
  funext x
  unfold velocityDivergence velocityDivergenceReadout
    velocityDivergenceReadoutLinear
  rw [integerSineDivergencePrimitive_fderiv,
    integerCosine_fderiv]
  fin_cases i <;>
    simp [Fin.sum_univ_succ, integerWavePhaseLinear_single,
      integerSine] at hCoefficient ⊢ <;>
    field_simp [hCoefficient]

/--
A concrete nonzero coordinate makes the cosine character a periodic
divergence and hence forces its physical-unit-cell mean to vanish.
-/
theorem physicalUnitCell_integerCosine_integral_eq_zero_of_coordinate_ne
    (k : IntegerWavevector) (i : Coordinate)
    (hki : k i ≠ 0) :
    (∫ x in physicalUnitCell, integerCosine k x) = 0 := by
  rw [← velocityDivergence_integerCosineDivergencePrimitive
    k i hki]
  exact
    physicalUnitCell_velocityDivergence_integral_eq_zero
      (integerCosineDivergencePrimitive k i)
      (integerCosineDivergencePrimitive_contDiff k i)
      (integerCosineDivergencePrimitive_latticePeriodic k i)

/--
A concrete nonzero coordinate makes the sine character a periodic
divergence and hence forces its physical-unit-cell mean to vanish.
-/
theorem physicalUnitCell_integerSine_integral_eq_zero_of_coordinate_ne
    (k : IntegerWavevector) (i : Coordinate)
    (hki : k i ≠ 0) :
    (∫ x in physicalUnitCell, integerSine k x) = 0 := by
  rw [← velocityDivergence_integerSineDivergencePrimitive
    k i hki]
  exact
    physicalUnitCell_velocityDivergence_integral_eq_zero
      (integerSineDivergencePrimitive k i)
      (integerSineDivergencePrimitive_contDiff k i)
      (integerSineDivergencePrimitive_latticePeriodic k i)

private theorem exists_coordinate_ne_zero_of_wavevector_ne_zero
    (k : IntegerWavevector) (hk : k ≠ 0) :
    ∃ i : Coordinate, k i ≠ 0 := by
  by_contra h
  apply hk
  funext i
  exact not_ne_iff.mp (not_exists.mp h i)

/-- Every nonzero integer cosine character has zero physical-unit-cell mean. -/
theorem physicalUnitCell_integerCosine_integral_eq_zero
    (k : IntegerWavevector) (hk : k ≠ 0) :
    (∫ x in physicalUnitCell, integerCosine k x) = 0 := by
  obtain ⟨i, hi⟩ :=
    exists_coordinate_ne_zero_of_wavevector_ne_zero k hk
  exact
    physicalUnitCell_integerCosine_integral_eq_zero_of_coordinate_ne
      k i hi

/-- Every nonzero integer sine character has zero physical-unit-cell mean. -/
theorem physicalUnitCell_integerSine_integral_eq_zero
    (k : IntegerWavevector) (hk : k ≠ 0) :
    (∫ x in physicalUnitCell, integerSine k x) = 0 := by
  obtain ⟨i, hi⟩ :=
    exists_coordinate_ne_zero_of_wavevector_ne_zero k hk
  exact
    physicalUnitCell_integerSine_integral_eq_zero_of_coordinate_ne
      k i hi

end

end ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
end NavierStokes
end SaturationMonoid
