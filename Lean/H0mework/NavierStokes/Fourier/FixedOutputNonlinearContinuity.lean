import H0mework.NavierStokes.Galerkin.NonlinearNegativeSobolev
import H0mework.NavierStokes.Galerkin.KineticEnergyLedger
import H0mework.NavierStokes.ShellSources.Source

/-!
# Cutoff-independent continuity of one fixed nonlinear Fourier row

The complete finite vorticity nonlinearity is quadratic.  At one fixed
output frequency its difference factors through a bilinear row:

```text
N(left) - N(right)
  = B(left - right, left) + B(right, left - right).
```

This module bounds `B` by discrete Cauchy--Schwarz rather than by the number
of retained modes.  Integer frequencies give the uniform Biot--Savart row
bound `|u_k| ≤ (2π)⁻¹ |ω_k|`; transversality moves the derivative frequency
from an input to the fixed output.  The resulting continuity estimate has
no cutoff, maximal shell, or mode-cardinality constant.

It is the nonlinear consumer needed after strong `L²` convergence on a
common finite carrier.  The theorem does not assert that such convergence,
an infinite-dimensional limit, or a continuation conclusion has already
been generated.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity

open scoped BigOperators Matrix

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource

noncomputable section

/-! ## Exact bilinear polarization -/

/-- Bilinear vorticity row with the first state in the differentiated /
advecting slot and the second state in the transported / velocity slot. -/
def finiteStateVorticityBilinearPairContribution
    (left right : ComplexVorticityHilbertState)
    (pair : StretchingPair) : ComplexCoordinateVector :=
  (Complex.I * (((2 * Real.pi : ℝ) : ℂ)) *
      (complexWavevector pair.2 ⬝ᵥ left pair.1)) •
        finiteStateVelocityCoefficient right pair.2 -
    (Complex.I * (((2 * Real.pi : ℝ) : ℂ)) *
      (complexWavevector pair.2 ⬝ᵥ
        finiteStateVelocityCoefficient left pair.1)) •
          right pair.2

/-- Complete fixed-output aggregation of the bilinear rows. -/
def finiteStateVorticityBilinearCoefficientAt
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  ∑ first ∈ modes,
    ∑ second ∈ modes,
      if first + second = output then
        finiteStateVorticityBilinearPairContribution
          left right (first, second)
      else 0

theorem finiteStateVelocityCoefficient_sub
    (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    finiteStateVelocityCoefficient (left - right) wave =
      finiteStateVelocityCoefficient left wave -
        finiteStateVelocityCoefficient right wave := by
  simp [finiteStateVelocityCoefficient,
    biotSavartVelocityCoefficient_sub]

theorem finiteStateVorticityNonlinearPairContribution_sub
    (left right : ComplexVorticityHilbertState)
    (pair : StretchingPair) :
    finiteStateVorticityNonlinearPairContribution left pair -
        finiteStateVorticityNonlinearPairContribution right pair =
      finiteStateVorticityBilinearPairContribution
          (left - right) left pair +
        finiteStateVorticityBilinearPairContribution
          right (left - right) pair := by
  simp [finiteStateVorticityNonlinearPairContribution,
    finiteStateVorticityBilinearPairContribution,
    dotProduct_sub, finiteStateVelocityCoefficient_sub, smul_sub]
  module

/--
Exact polarization of the complete ordered-pair coefficient.  The equality
uses the same finite carrier on both sides, but no support size enters it.
-/
theorem finiteStateVorticityNonlinearCoefficientAt_sub
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    finiteStateVorticityNonlinearCoefficientAt modes left output -
        finiteStateVorticityNonlinearCoefficientAt modes right output =
      finiteStateVorticityBilinearCoefficientAt
          modes (left - right) left output +
        finiteStateVorticityBilinearCoefficientAt
          modes right (left - right) output := by
  unfold finiteStateVorticityNonlinearCoefficientAt
    finiteStateVorticityBilinearCoefficientAt
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro first firstMem
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro second secondMem
  by_cases incidence : first + second = output
  · simp [incidence,
      finiteStateVorticityNonlinearPairContribution_sub]
  · simp [incidence]

/-! ## Uniform integer-frequency Biot--Savart row bound -/

/-- Euclidean coefficient amplitude of one vorticity row. -/
def vorticityRowAmplitude
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ℝ :=
  Real.sqrt (complexCoordinateAmplitudeSq (state wave))

/-- Euclidean coefficient amplitude of its Biot--Savart velocity row. -/
def velocityRowAmplitude
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ℝ :=
  Real.sqrt
    (complexCoordinateAmplitudeSq
      (finiteStateVelocityCoefficient state wave))

theorem vorticityRowAmplitude_nonneg
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    0 ≤ vorticityRowAmplitude state wave :=
  Real.sqrt_nonneg _

theorem velocityRowAmplitude_nonneg
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    0 ≤ velocityRowAmplitude state wave :=
  Real.sqrt_nonneg _

theorem vorticityRowAmplitude_sq
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    vorticityRowAmplitude state wave ^ 2 =
      complexCoordinateVectorNormSq (state wave) := by
  rw [vorticityRowAmplitude,
    Real.sq_sqrt (complexCoordinateAmplitudeSq_nonneg _),
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]

theorem velocityRowAmplitude_sq
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    velocityRowAmplitude state wave ^ 2 =
      complexCoordinateAmplitudeSq
        (finiteStateVelocityCoefficient state wave) := by
  rw [velocityRowAmplitude, Real.sq_sqrt]
  exact complexCoordinateAmplitudeSq_nonneg _

theorem one_le_integerWaveNormSq
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    1 ≤ integerWaveNormSq wave := by
  rw [integerWaveNormSq_eq_integerWaveShellSq]
  exact_mod_cast integerWaveShellSq_pos waveNe

/--
Every integer Fourier velocity row is uniformly bounded by its vorticity
row, with no dependence on a cutoff.  The zero row is silent; every nonzero
integer row has squared norm at least one.
-/
theorem velocityRowAmplitude_le_vorticityRowAmplitude
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    velocityRowAmplitude state wave ≤
      (1 / (2 * Real.pi)) *
        vorticityRowAmplitude state wave := by
  by_cases waveZero : wave = 0
  · subst wave
    have rightNonneg :
        0 ≤
          (1 / (2 * Real.pi)) *
            vorticityRowAmplitude state 0 :=
      mul_nonneg (by positivity)
        (vorticityRowAmplitude_nonneg _ _)
    simpa [velocityRowAmplitude,
      finiteStateVelocityCoefficient,
      complexCoordinateAmplitudeSq] using rightNonneg
  · have sourceBound :=
      biotSavartVelocityCoefficient_normSq_le
        wave (state wave) waveZero
    have normOneLe :=
      one_le_integerWaveNormSq wave waveZero
    have piSqPos : 0 < (2 * Real.pi) ^ 2 :=
      sq_pos_of_pos (by positivity)
    have denominatorLe :
        (2 * Real.pi) ^ 2 ≤
          (2 * Real.pi) ^ 2 * integerWaveNormSq wave := by
      nlinarith
    have amplitudeDivLe :
        complexCoordinateAmplitudeSq (state wave) /
              ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) ≤
          complexCoordinateAmplitudeSq (state wave) /
            (2 * Real.pi) ^ 2 :=
      div_le_div_of_nonneg_left
        (complexCoordinateAmplitudeSq_nonneg _)
        piSqPos denominatorLe
    have squared :
        velocityRowAmplitude state wave ^ 2 ≤
          ((1 / (2 * Real.pi)) *
            vorticityRowAmplitude state wave) ^ 2 := by
      rw [velocityRowAmplitude_sq]
      change
        complexCoordinateVectorNormSq
            (biotSavartVelocityCoefficient wave (state wave)) ≤
          _
      calc
        _ ≤
            complexCoordinateVectorNormSq (state wave) /
              ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) :=
          sourceBound
        _ ≤
            complexCoordinateVectorNormSq (state wave) /
              (2 * Real.pi) ^ 2 := by
          simpa
              [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
            using amplitudeDivLe
        _ =
            (1 / (2 * Real.pi)) ^ 2 *
              complexCoordinateVectorNormSq (state wave) := by
          field_simp [Real.pi_ne_zero]
        _ =
            (1 / (2 * Real.pi)) ^ 2 *
              vorticityRowAmplitude state wave ^ 2 := by
          rw [vorticityRowAmplitude_sq]
        _ =
            ((1 / (2 * Real.pi)) *
              vorticityRowAmplitude state wave) ^ 2 := by
          ring
    have rightNonneg :
        0 ≤
          (1 / (2 * Real.pi)) *
            vorticityRowAmplitude state wave :=
      mul_nonneg (by positivity)
        (vorticityRowAmplitude_nonneg _ _)
    exact
      (sq_le_sq₀
        (velocityRowAmplitude_nonneg _ _) rightNonneg).mp
        squared

/-! ## One bilinear interaction at a fixed output -/

def finiteStateVorticityBilinearStretchingPairContribution
    (left right : ComplexVorticityHilbertState)
    (pair : StretchingPair) : ComplexCoordinateVector :=
  (Complex.I * (((2 * Real.pi : ℝ) : ℂ)) *
      (complexWavevector pair.2 ⬝ᵥ left pair.1)) •
    finiteStateVelocityCoefficient right pair.2

def finiteStateVorticityBilinearAdvectionPairContribution
    (left right : ComplexVorticityHilbertState)
    (pair : StretchingPair) : ComplexCoordinateVector :=
  (Complex.I * (((2 * Real.pi : ℝ) : ℂ)) *
      (complexWavevector pair.2 ⬝ᵥ
        finiteStateVelocityCoefficient left pair.1)) •
    right pair.2

theorem finiteStateVorticityBilinearPairContribution_eq
    (left right : ComplexVorticityHilbertState)
    (pair : StretchingPair) :
    finiteStateVorticityBilinearPairContribution left right pair =
      finiteStateVorticityBilinearStretchingPairContribution
          left right pair -
        finiteStateVorticityBilinearAdvectionPairContribution
          left right pair :=
  rfl

private theorem complexWavevector_add
    (first second : IntegerWavevector) :
    complexWavevector (first + second) =
      complexWavevector first + complexWavevector second := by
  funext coordinate
  simp [complexWavevector]

private theorem second_dot_left_eq_output_dot
    (left : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse :
      complexWavevector first ⬝ᵥ left first = 0) :
    complexWavevector second ⬝ᵥ left first =
      complexWavevector output ⬝ᵥ left first := by
  rw [← incidence, complexWavevector_add,
    add_dotProduct, transverse]
  simp

private theorem second_dot_leftVelocity_eq_output_dot
    (left : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output) :
    complexWavevector second ⬝ᵥ
        finiteStateVelocityCoefficient left first =
      complexWavevector output ⬝ᵥ
        finiteStateVelocityCoefficient left first := by
  have velocityTransverse :
      complexWavevector first ⬝ᵥ
          finiteStateVelocityCoefficient left first = 0 := by
    unfold finiteStateVelocityCoefficient
    exact
      complexWavevector_dot_biotSavartVelocityCoefficient
        first (left first)
  rw [← incidence, complexWavevector_add,
    add_dotProduct, velocityTransverse]
  simp

private theorem bilinearStretchingPairContribution_amplitudeSq_le
    (left right : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse :
      complexWavevector first ⬝ᵥ left first = 0) :
    complexCoordinateAmplitudeSq
        (finiteStateVorticityBilinearStretchingPairContribution
          left right (first, second)) ≤
      (2 * Real.pi) ^ 2 * integerWaveNormSq output *
        complexCoordinateAmplitudeSq (left first) *
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient right second) := by
  have dotBound :=
    complexWavevector_dot_normSq_le output (left first)
  rw [← second_dot_left_eq_output_dot
    left output first second incidence transverse] at dotBound
  simp only
    [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    at dotBound
  rw [finiteStateVorticityBilinearStretchingPairContribution,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    complexCoordinateVectorNormSq_smul]
  simp only [Complex.normSq_mul, Complex.normSq_I,
    Complex.normSq_ofReal, one_mul]
  simp only
    [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have angularNonneg : 0 ≤ (2 * Real.pi) ^ 2 :=
    sq_nonneg _
  have scaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left dotBound angularNonneg)
      (complexCoordinateVectorNormSq_nonneg
        (finiteStateVelocityCoefficient right second))
  simpa only [pow_two, mul_assoc] using scaled

private theorem bilinearAdvectionPairContribution_amplitudeSq_le
    (left right : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output) :
    complexCoordinateAmplitudeSq
        (finiteStateVorticityBilinearAdvectionPairContribution
          left right (first, second)) ≤
      (2 * Real.pi) ^ 2 * integerWaveNormSq output *
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient left first) *
        complexCoordinateAmplitudeSq (right second) := by
  have dotBound :=
    complexWavevector_dot_normSq_le output
      (finiteStateVelocityCoefficient left first)
  rw [← second_dot_leftVelocity_eq_output_dot
    left output first second incidence] at dotBound
  simp only
    [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    at dotBound
  rw [finiteStateVorticityBilinearAdvectionPairContribution,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    complexCoordinateVectorNormSq_smul]
  simp only [Complex.normSq_mul, Complex.normSq_I,
    Complex.normSq_ofReal, one_mul]
  simp only
    [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have angularNonneg : 0 ≤ (2 * Real.pi) ^ 2 :=
    sq_nonneg _
  have scaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left dotBound angularNonneg)
      (complexCoordinateVectorNormSq_nonneg (right second))
  simpa only [pow_two, mul_assoc] using scaled

private theorem bilinearStretchingPairContribution_norm_le
    (left right : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse :
      complexWavevector first ⬝ᵥ left first = 0) :
    ‖finiteStateVorticityBilinearStretchingPairContribution
        left right (first, second)‖ ≤
      (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        vorticityRowAmplitude left first *
        velocityRowAmplitude right second := by
  have normSqLe :
      ‖finiteStateVorticityBilinearStretchingPairContribution
          left right (first, second)‖ ^ 2 ≤
        complexCoordinateAmplitudeSq
          (finiteStateVorticityBilinearStretchingPairContribution
            left right (first, second)) :=
    complexCoordinateVector_norm_sq_le_amplitudeSq _
  have amplitudeLe :=
    bilinearStretchingPairContribution_amplitudeSq_le
      left right output first second incidence transverse
  have rhsNonneg :
      0 ≤
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          vorticityRowAmplitude left first *
          velocityRowAmplitude right second := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) Real.pi_pos.le)
            (Real.sqrt_nonneg _))
          (vorticityRowAmplitude_nonneg left first))
        (velocityRowAmplitude_nonneg right second)
  apply (sq_le_sq₀ (norm_nonneg _) rhsNonneg).mp
  calc
    ‖finiteStateVorticityBilinearStretchingPairContribution
        left right (first, second)‖ ^ 2 ≤
        complexCoordinateAmplitudeSq
          (finiteStateVorticityBilinearStretchingPairContribution
            left right (first, second)) :=
      normSqLe
    _ ≤
        (2 * Real.pi) ^ 2 * integerWaveNormSq output *
          complexCoordinateAmplitudeSq (left first) *
          complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient right second) :=
      amplitudeLe
    _ =
        ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          vorticityRowAmplitude left first *
          velocityRowAmplitude right second) ^ 2 := by
      symm
      calc
        ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            vorticityRowAmplitude left first *
            velocityRowAmplitude right second) ^ 2 =
            (2 * Real.pi) ^ 2 *
              Real.sqrt (integerWaveNormSq output) ^ 2 *
              vorticityRowAmplitude left first ^ 2 *
              velocityRowAmplitude right second ^ 2 := by
          ring
        _ =
            (2 * Real.pi) ^ 2 * integerWaveNormSq output *
              complexCoordinateAmplitudeSq (left first) *
              complexCoordinateAmplitudeSq
                (finiteStateVelocityCoefficient right second) := by
          rw [Real.sq_sqrt (integerWaveNormSq_nonneg output),
            vorticityRowAmplitude_sq,
            velocityRowAmplitude_sq]
          simp only
            [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]

private theorem bilinearAdvectionPairContribution_norm_le
    (left right : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output) :
    ‖finiteStateVorticityBilinearAdvectionPairContribution
        left right (first, second)‖ ≤
      (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        velocityRowAmplitude left first *
        vorticityRowAmplitude right second := by
  have normSqLe :
      ‖finiteStateVorticityBilinearAdvectionPairContribution
          left right (first, second)‖ ^ 2 ≤
        complexCoordinateAmplitudeSq
          (finiteStateVorticityBilinearAdvectionPairContribution
            left right (first, second)) :=
    complexCoordinateVector_norm_sq_le_amplitudeSq _
  have amplitudeLe :=
    bilinearAdvectionPairContribution_amplitudeSq_le
      left right output first second incidence
  have rhsNonneg :
      0 ≤
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          velocityRowAmplitude left first *
          vorticityRowAmplitude right second := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) Real.pi_pos.le)
            (Real.sqrt_nonneg _))
          (velocityRowAmplitude_nonneg left first))
        (vorticityRowAmplitude_nonneg right second)
  apply (sq_le_sq₀ (norm_nonneg _) rhsNonneg).mp
  calc
    ‖finiteStateVorticityBilinearAdvectionPairContribution
        left right (first, second)‖ ^ 2 ≤
        complexCoordinateAmplitudeSq
          (finiteStateVorticityBilinearAdvectionPairContribution
            left right (first, second)) :=
      normSqLe
    _ ≤
        (2 * Real.pi) ^ 2 * integerWaveNormSq output *
          complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient left first) *
          complexCoordinateAmplitudeSq (right second) :=
      amplitudeLe
    _ =
        ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          velocityRowAmplitude left first *
          vorticityRowAmplitude right second) ^ 2 := by
      symm
      calc
        ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            velocityRowAmplitude left first *
            vorticityRowAmplitude right second) ^ 2 =
            (2 * Real.pi) ^ 2 *
              Real.sqrt (integerWaveNormSq output) ^ 2 *
              velocityRowAmplitude left first ^ 2 *
              vorticityRowAmplitude right second ^ 2 := by
          ring
        _ =
            (2 * Real.pi) ^ 2 * integerWaveNormSq output *
              complexCoordinateAmplitudeSq
                (finiteStateVelocityCoefficient left first) *
              complexCoordinateAmplitudeSq (right second) := by
          rw [Real.sq_sqrt (integerWaveNormSq_nonneg output),
            velocityRowAmplitude_sq,
            vorticityRowAmplitude_sq]
          simp only
            [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]

/--
Before collapsing the Biot--Savart factor into a vorticity-only bound, one
bilinear interaction retains the two velocity--vorticity placements.  This
is the form required by whole-output Young convolution estimates.
-/
theorem finiteStateVorticityBilinearPairContribution_norm_le_preBiotSavart
    (left right : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse :
      complexWavevector first ⬝ᵥ left first = 0) :
    ‖finiteStateVorticityBilinearPairContribution
        left right (first, second)‖ ≤
      (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        (vorticityRowAmplitude left first *
            velocityRowAmplitude right second +
          velocityRowAmplitude left first *
            vorticityRowAmplitude right second) := by
  rw [finiteStateVorticityBilinearPairContribution_eq]
  calc
    ‖finiteStateVorticityBilinearStretchingPairContribution
          left right (first, second) -
        finiteStateVorticityBilinearAdvectionPairContribution
          left right (first, second)‖ ≤
        ‖finiteStateVorticityBilinearStretchingPairContribution
          left right (first, second)‖ +
          ‖finiteStateVorticityBilinearAdvectionPairContribution
            left right (first, second)‖ :=
      norm_sub_le _ _
    _ ≤
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            vorticityRowAmplitude left first *
            velocityRowAmplitude right second +
          (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            velocityRowAmplitude left first *
            vorticityRowAmplitude right second :=
      add_le_add
        (bilinearStretchingPairContribution_norm_le
          left right output first second incidence transverse)
        (bilinearAdvectionPairContribution_norm_le
          left right output first second incidence)
    _ =
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          (vorticityRowAmplitude left first *
              velocityRowAmplitude right second +
            velocityRowAmplitude left first *
              vorticityRowAmplitude right second) := by
      ring

/--
After the integer-frequency Biot--Savart bound, one interaction costs only
the fixed output frequency and the two vorticity row amplitudes.
-/
theorem finiteStateVorticityBilinearPairContribution_norm_le
    (left right : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse :
      complexWavevector first ⬝ᵥ left first = 0) :
    ‖finiteStateVorticityBilinearPairContribution
        left right (first, second)‖ ≤
      2 * Real.sqrt (integerWaveNormSq output) *
        vorticityRowAmplitude left first *
        vorticityRowAmplitude right second := by
  have angularNonneg :
      0 ≤
        (2 * Real.pi) *
          Real.sqrt (integerWaveNormSq output) := by
    positivity
  have innerBound :
      vorticityRowAmplitude left first *
            velocityRowAmplitude right second +
          velocityRowAmplitude left first *
            vorticityRowAmplitude right second ≤
        vorticityRowAmplitude left first *
              ((1 / (2 * Real.pi)) *
                vorticityRowAmplitude right second) +
          ((1 / (2 * Real.pi)) *
              vorticityRowAmplitude left first) *
            vorticityRowAmplitude right second :=
    add_le_add
      (mul_le_mul_of_nonneg_left
        (velocityRowAmplitude_le_vorticityRowAmplitude
          right second)
        (vorticityRowAmplitude_nonneg left first))
      (mul_le_mul_of_nonneg_right
        (velocityRowAmplitude_le_vorticityRowAmplitude
          left first)
        (vorticityRowAmplitude_nonneg right second))
  calc
    ‖finiteStateVorticityBilinearPairContribution
        left right (first, second)‖ ≤
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          (vorticityRowAmplitude left first *
              velocityRowAmplitude right second +
            velocityRowAmplitude left first *
              vorticityRowAmplitude right second) :=
      finiteStateVorticityBilinearPairContribution_norm_le_preBiotSavart
        left right output first second incidence transverse
    _ ≤
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          (vorticityRowAmplitude left first *
                ((1 / (2 * Real.pi)) *
                  vorticityRowAmplitude right second) +
            ((1 / (2 * Real.pi)) *
                vorticityRowAmplitude left first) *
              vorticityRowAmplitude right second) :=
      mul_le_mul_of_nonneg_left innerBound angularNonneg
    _ =
        2 * Real.sqrt (integerWaveNormSq output) *
          vorticityRowAmplitude left first *
          vorticityRowAmplitude right second := by
      field_simp [Real.pi_ne_zero]
      ring

/-! ## Fixed-output convolution without a mode-count loss -/

/--
Scalar coefficient convolution at one fixed output.  The incidence equation
determines the second frequency uniquely from the first.
-/
def fixedOutputVorticityConvolutionAmplitude
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : ℝ :=
  ∑ first ∈ modes,
    if output - first ∈ modes then
      vorticityRowAmplitude left first *
        vorticityRowAmplitude right (output - first)
    else 0

theorem fixedOutputVorticityConvolutionAmplitude_nonneg
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    0 ≤
      fixedOutputVorticityConvolutionAmplitude
        modes left right output := by
  unfold fixedOutputVorticityConvolutionAmplitude
  exact Finset.sum_nonneg fun first firstMem => by
    split_ifs
    · exact mul_nonneg
        (vorticityRowAmplitude_nonneg left first)
        (vorticityRowAmplitude_nonneg right (output - first))
    · exact le_rfl

private theorem doubleIncidenceAmplitude_eq_fixedOutput
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    (∑ first ∈ modes,
      ∑ second ∈ modes,
        if first + second = output then
          vorticityRowAmplitude left first *
            vorticityRowAmplitude right second
        else 0) =
      fixedOutputVorticityConvolutionAmplitude
        modes left right output := by
  unfold fixedOutputVorticityConvolutionAmplitude
  apply Finset.sum_congr rfl
  intro first firstMem
  have condition :
      ∀ second : IntegerWavevector,
        first + second = output ↔
          second = output - first := by
    intro second
    constructor <;> intro equality
    · rw [← equality]
      abel
    · rw [equality]
      abel
  simp_rw [condition]
  by_cases translatedMem : output - first ∈ modes
  · simp [translatedMem]
  · simp [translatedMem]

/--
The aggregate bilinear row costs the fixed output frequency times one
scalar convolution; the number of input pairs does not enter.
-/
theorem finiteStateVorticityBilinearCoefficientAt_norm_le_convolution
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left)
    (output : IntegerWavevector) :
    ‖finiteStateVorticityBilinearCoefficientAt
        modes left right output‖ ≤
      2 * Real.sqrt (integerWaveNormSq output) *
        fixedOutputVorticityConvolutionAmplitude
          modes left right output := by
  let angular : ℝ :=
    2 * Real.sqrt (integerWaveNormSq output)
  have aggregateNorm :
      ‖finiteStateVorticityBilinearCoefficientAt
          modes left right output‖ ≤
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            ‖if first + second = output then
                finiteStateVorticityBilinearPairContribution
                  left right (first, second)
              else 0‖ := by
    unfold finiteStateVorticityBilinearCoefficientAt
    exact
      (norm_sum_le modes fun first =>
        ∑ second ∈ modes,
          if first + second = output then
            finiteStateVorticityBilinearPairContribution
              left right (first, second)
          else 0).trans
        (Finset.sum_le_sum fun first firstMem =>
          norm_sum_le modes fun second =>
            if first + second = output then
              finiteStateVorticityBilinearPairContribution
                left right (first, second)
            else 0)
  have pairwiseNorm :
      (∑ first ∈ modes,
          ∑ second ∈ modes,
            ‖if first + second = output then
                finiteStateVorticityBilinearPairContribution
                  left right (first, second)
              else 0‖) ≤
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            if first + second = output then
              angular *
                (vorticityRowAmplitude left first *
                  vorticityRowAmplitude right second)
            else 0 := by
    apply Finset.sum_le_sum
    intro first firstMem
    apply Finset.sum_le_sum
    intro second secondMem
    by_cases incidence : first + second = output
    · simp only [if_pos incidence]
      simpa [angular, mul_assoc] using
        finiteStateVorticityBilinearPairContribution_norm_le
          left right output first second incidence
          (leftTransverse first firstMem)
    · simp [incidence]
  have factorAngular :
      (∑ first ∈ modes,
          ∑ second ∈ modes,
            if first + second = output then
              angular *
                (vorticityRowAmplitude left first *
                  vorticityRowAmplitude right second)
            else 0) =
        angular *
          fixedOutputVorticityConvolutionAmplitude
            modes left right output := by
    rw [← doubleIncidenceAmplitude_eq_fixedOutput]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first firstMem
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro second secondMem
    by_cases incidence : first + second = output <;>
      simp [incidence]
  exact aggregateNorm.trans (pairwiseNorm.trans_eq factorAngular)

private theorem translated_vorticityRowAmplitude_sq_sum_le
    (modes : Finset IntegerWavevector)
    (right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    (∑ first ∈ modes,
        if output - first ∈ modes then
          vorticityRowAmplitude right (output - first) ^ 2
        else 0) ≤
      ∑ second ∈ modes,
        vorticityRowAmplitude right second ^ 2 := by
  let translated : Finset IntegerWavevector :=
    modes.image fun second => output - second
  have filteredSubset :
      modes.filter (fun first => output - first ∈ modes) ⊆
        translated := by
    intro first firstMem
    have membership := Finset.mem_filter.mp firstMem
    apply Finset.mem_image.mpr
    refine ⟨output - first, membership.2, ?_⟩
    abel
  have translatedSum :
      (∑ first ∈ translated,
          vorticityRowAmplitude right (output - first) ^ 2) =
        ∑ second ∈ modes,
          vorticityRowAmplitude right second ^ 2 := by
    dsimp [translated]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro second secondMem
      congr 2
      abel
    · intro left leftMem rightWave rightMem equality
      exact sub_right_inj.mp equality
  rw [← Finset.sum_filter]
  exact
    (Finset.sum_le_sum_of_subset_of_nonneg
      filteredSubset
      (fun first firstMem firstNotMem =>
        sq_nonneg
          (vorticityRowAmplitude right (output - first)))).trans_eq
      translatedSum

private theorem vorticityRowAmplitude_sq_sum_eq_mass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    (∑ wave ∈ modes,
        vorticityRowAmplitude state wave ^ 2) =
      finiteStateVorticityMass modes state := by
  unfold finiteStateVorticityMass
  apply Finset.sum_congr rfl
  intro wave waveMem
  exact vorticityRowAmplitude_sq state wave

/--
Discrete fixed-output Cauchy--Schwarz.  Translation by the output frequency
is injective, so the estimate has no interaction-cardinality factor.
-/
theorem fixedOutputVorticityConvolutionAmplitude_le_mass
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    fixedOutputVorticityConvolutionAmplitude
        modes left right output ≤
      Real.sqrt (finiteStateVorticityMass modes left) *
        Real.sqrt (finiteStateVorticityMass modes right) := by
  let translatedAmplitude : IntegerWavevector → ℝ :=
    fun first =>
      if output - first ∈ modes then
        vorticityRowAmplitude right (output - first)
      else 0
  have cauchy :=
    Real.sum_mul_le_sqrt_mul_sqrt
      modes
      (vorticityRowAmplitude left)
      translatedAmplitude
  have translatedSqLe :
      (∑ first ∈ modes,
          translatedAmplitude first ^ 2) ≤
        ∑ second ∈ modes,
          vorticityRowAmplitude right second ^ 2 := by
    dsimp [translatedAmplitude]
    calc
      (∑ first ∈ modes,
          (if output - first ∈ modes then
              vorticityRowAmplitude right (output - first)
            else 0) ^ 2) =
          ∑ first ∈ modes,
            if output - first ∈ modes then
              vorticityRowAmplitude right (output - first) ^ 2
            else 0 := by
        apply Finset.sum_congr rfl
        intro first firstMem
        by_cases translatedMem : output - first ∈ modes <;>
          simp [translatedMem]
      _ ≤
          ∑ second ∈ modes,
            vorticityRowAmplitude right second ^ 2 :=
        translated_vorticityRowAmplitude_sq_sum_le
          modes right output
  have sqrtTranslatedLe :
      Real.sqrt
          (∑ first ∈ modes,
            translatedAmplitude first ^ 2) ≤
        Real.sqrt
          (∑ second ∈ modes,
            vorticityRowAmplitude right second ^ 2) :=
    Real.sqrt_le_sqrt translatedSqLe
  calc
    fixedOutputVorticityConvolutionAmplitude
        modes left right output =
        ∑ first ∈ modes,
          vorticityRowAmplitude left first *
            translatedAmplitude first := by
      unfold fixedOutputVorticityConvolutionAmplitude
      apply Finset.sum_congr rfl
      intro first firstMem
      by_cases translatedMem : output - first ∈ modes <;>
        simp [translatedAmplitude, translatedMem]
    _ ≤
        Real.sqrt
            (∑ first ∈ modes,
              vorticityRowAmplitude left first ^ 2) *
          Real.sqrt
            (∑ first ∈ modes,
              translatedAmplitude first ^ 2) :=
      cauchy
    _ ≤
        Real.sqrt
            (∑ first ∈ modes,
              vorticityRowAmplitude left first ^ 2) *
          Real.sqrt
            (∑ second ∈ modes,
              vorticityRowAmplitude right second ^ 2) :=
      mul_le_mul_of_nonneg_left sqrtTranslatedLe
        (Real.sqrt_nonneg _)
    _ =
        Real.sqrt (finiteStateVorticityMass modes left) *
          Real.sqrt (finiteStateVorticityMass modes right) := by
      rw [vorticityRowAmplitude_sq_sum_eq_mass,
        vorticityRowAmplitude_sq_sum_eq_mass]

/-! ## Cutoff-independent nonlinear continuity -/

/--
One fixed bilinear Fourier row is bounded only by the output frequency and
the two whole-carrier vorticity masses.  In particular, the constant does
not depend on the number of retained modes or on a maximal shell.
-/
theorem finiteStateVorticityBilinearCoefficientAt_norm_le_mass
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left)
    (output : IntegerWavevector) :
    ‖finiteStateVorticityBilinearCoefficientAt
        modes left right output‖ ≤
      2 * Real.sqrt (integerWaveNormSq output) *
        (Real.sqrt (finiteStateVorticityMass modes left) *
          Real.sqrt (finiteStateVorticityMass modes right)) := by
  calc
    ‖finiteStateVorticityBilinearCoefficientAt
        modes left right output‖ ≤
        2 * Real.sqrt (integerWaveNormSq output) *
          fixedOutputVorticityConvolutionAmplitude
            modes left right output :=
      finiteStateVorticityBilinearCoefficientAt_norm_le_convolution
        modes left right leftTransverse output
    _ ≤
        2 * Real.sqrt (integerWaveNormSq output) *
          (Real.sqrt (finiteStateVorticityMass modes left) *
            Real.sqrt (finiteStateVorticityMass modes right)) :=
      mul_le_mul_of_nonneg_left
        (fixedOutputVorticityConvolutionAmplitude_le_mass
          modes left right output)
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

/-- Transverse finite states are closed under subtraction on the same carrier. -/
theorem finiteStateTransverseOn_sub
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left)
    (rightTransverse : FiniteStateTransverseOn modes right) :
    FiniteStateTransverseOn modes (left - right) := by
  intro wave waveMem
  simp [dotProduct_sub, leftTransverse wave waveMem,
    rightTransverse wave waveMem]

/--
Cutoff-independent continuity of one complete nonlinear Fourier row.

The common carrier may be enlarged to the union of two finite supports.
Only transversality on that carrier is used.  The Lipschitz factor depends
on the fixed output wave and the two whole-carrier vorticity masses, never
on the carrier cardinality or its largest shell.
-/
theorem finiteStateVorticityNonlinearCoefficientAt_sub_norm_le_mass
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left)
    (rightTransverse : FiniteStateTransverseOn modes right)
    (output : IntegerWavevector) :
    ‖finiteStateVorticityNonlinearCoefficientAt modes left output -
        finiteStateVorticityNonlinearCoefficientAt modes right output‖ ≤
      2 * Real.sqrt (integerWaveNormSq output) *
        Real.sqrt (finiteStateVorticityMass modes (left - right)) *
        (Real.sqrt (finiteStateVorticityMass modes left) +
          Real.sqrt (finiteStateVorticityMass modes right)) := by
  rw [finiteStateVorticityNonlinearCoefficientAt_sub]
  calc
    ‖finiteStateVorticityBilinearCoefficientAt
          modes (left - right) left output +
        finiteStateVorticityBilinearCoefficientAt
          modes right (left - right) output‖ ≤
        ‖finiteStateVorticityBilinearCoefficientAt
          modes (left - right) left output‖ +
        ‖finiteStateVorticityBilinearCoefficientAt
          modes right (left - right) output‖ :=
      norm_add_le _ _
    _ ≤
        2 * Real.sqrt (integerWaveNormSq output) *
            (Real.sqrt (finiteStateVorticityMass modes (left - right)) *
              Real.sqrt (finiteStateVorticityMass modes left)) +
          2 * Real.sqrt (integerWaveNormSq output) *
            (Real.sqrt (finiteStateVorticityMass modes right) *
              Real.sqrt (finiteStateVorticityMass modes (left - right))) :=
      add_le_add
        (finiteStateVorticityBilinearCoefficientAt_norm_le_mass
          modes (left - right) left
          (finiteStateTransverseOn_sub
            modes left right leftTransverse rightTransverse)
          output)
        (finiteStateVorticityBilinearCoefficientAt_norm_le_mass
          modes right (left - right) rightTransverse output)
    _ =
        2 * Real.sqrt (integerWaveNormSq output) *
          Real.sqrt (finiteStateVorticityMass modes (left - right)) *
          (Real.sqrt (finiteStateVorticityMass modes left) +
            Real.sqrt (finiteStateVorticityMass modes right)) := by
      ring

end

end ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
end NavierStokes
end SaturationMonoid
