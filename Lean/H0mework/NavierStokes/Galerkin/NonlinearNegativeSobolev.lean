import H0mework.NavierStokes.Galerkin.AmbientNorm
import H0mework.NavierStokes.Galerkin.StretchingCriticalBound

/-!
# Cutoff-independent negative-Sobolev control of the nonlinear tangent

The finite vorticity nonlinearity is a first-order Fourier convolution.  On
transverse states its derivative frequency can be moved to the output row.
Dividing the squared output by the exact Laplacian multiplier therefore
leaves an ordinary scalar convolution of velocity and vorticity amplitudes.

This module keeps that calculation on the complete output carrier and proves
a discrete `ℓ¹ * ℓ² → ℓ²` Young bound.  The resulting estimate

```text
‖N(ω)‖_{H⁻¹}² ≤ 4 * M(u)² * Y(ω)
```

has no mode count or maximal frequency.  It is the spatial estimate needed
before testing whether heat smoothing has an integrable critical time
kernel.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev

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
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm

noncomputable section

private def vorticityAmplitude
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ℝ :=
  Real.sqrt (complexCoordinateAmplitudeSq (state wave))

private def velocityAmplitude
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ℝ :=
  Real.sqrt
    (complexCoordinateAmplitudeSq
      (finiteStateVelocityCoefficient state wave))

private theorem vorticityAmplitude_nonneg
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    0 ≤ vorticityAmplitude state wave :=
  Real.sqrt_nonneg _

private theorem velocityAmplitude_nonneg
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    0 ≤ velocityAmplitude state wave :=
  Real.sqrt_nonneg _

private theorem vorticityAmplitude_sq
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    vorticityAmplitude state wave ^ 2 =
      complexCoordinateAmplitudeSq (state wave) := by
  rw [vorticityAmplitude, Real.sq_sqrt]
  exact complexCoordinateAmplitudeSq_nonneg _

private theorem velocityAmplitude_sq
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    velocityAmplitude state wave ^ 2 =
      complexCoordinateAmplitudeSq
        (finiteStateVelocityCoefficient state wave) := by
  rw [velocityAmplitude, Real.sq_sqrt]
  exact complexCoordinateAmplitudeSq_nonneg _

private theorem complexWavevector_add
    (first second : IntegerWavevector) :
    complexWavevector (first + second) =
      complexWavevector first + complexWavevector second := by
  funext coordinate
  simp [complexWavevector]

/-- Cauchy--Schwarz for one complex Fourier dot product, in the coefficient
normalization used throughout the finite Galerkin development. -/
theorem complexWavevector_dot_normSq_le
    (wave : IntegerWavevector)
    (vector : ComplexCoordinateVector) :
    Complex.normSq (complexWavevector wave ⬝ᵥ vector) ≤
      integerWaveNormSq wave *
        complexCoordinateAmplitudeSq vector := by
  have lagrange :=
    complexWavevector_cross_normSq wave vector
  have crossNonneg :
      0 ≤
        complexCoordinateVectorNormSq
          (complexWavevector wave ⨯₃ vector) :=
    complexCoordinateVectorNormSq_nonneg _
  simp only [
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    at lagrange ⊢
  linarith

private theorem second_dot_state_eq_output_dot
    (state : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse :
      complexWavevector first ⬝ᵥ state first = 0) :
    complexWavevector second ⬝ᵥ state first =
      complexWavevector output ⬝ᵥ state first := by
  rw [← incidence, complexWavevector_add, add_dotProduct, transverse]
  simp

private theorem second_dot_velocity_eq_output_dot
    (state : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output) :
    complexWavevector second ⬝ᵥ
        finiteStateVelocityCoefficient state first =
      complexWavevector output ⬝ᵥ
        finiteStateVelocityCoefficient state first := by
  have velocityTransverse :
      complexWavevector first ⬝ᵥ
          finiteStateVelocityCoefficient state first = 0 := by
    unfold finiteStateVelocityCoefficient
    exact
      complexWavevector_dot_biotSavartVelocityCoefficient
        first (state first)
  rw [← incidence, complexWavevector_add, add_dotProduct,
    velocityTransverse]
  simp

private theorem stretchingPairContribution_amplitudeSq_le
    (state : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse :
      complexWavevector first ⬝ᵥ state first = 0) :
    complexCoordinateAmplitudeSq
        (finiteStateVorticityStretchingPairContribution
          state (first, second)) ≤
      (2 * Real.pi) ^ 2 * integerWaveNormSq output *
        complexCoordinateAmplitudeSq (state first) *
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state second) := by
  have dotBound :=
    complexWavevector_dot_normSq_le output (state first)
  rw [← second_dot_state_eq_output_dot
    state output first second incidence transverse] at dotBound
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    at dotBound
  rw [finiteStateVorticityStretchingPairContribution,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    complexCoordinateVectorNormSq_smul]
  simp only [Complex.normSq_mul, Complex.normSq_I,
    Complex.normSq_ofReal, one_mul]
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have angularNonneg : 0 ≤ (2 * Real.pi) ^ 2 :=
    sq_nonneg _
  have scaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left dotBound angularNonneg)
      (complexCoordinateVectorNormSq_nonneg
        (finiteStateVelocityCoefficient state second))
  simpa only [pow_two, mul_assoc] using scaled

private theorem advectionPairContribution_amplitudeSq_le
    (state : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output) :
    complexCoordinateAmplitudeSq
        (finiteStateVorticityAdvectionPairContribution
          state (first, second)) ≤
      (2 * Real.pi) ^ 2 * integerWaveNormSq output *
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state first) *
        complexCoordinateAmplitudeSq (state second) := by
  have dotBound :=
    complexWavevector_dot_normSq_le output
      (finiteStateVelocityCoefficient state first)
  rw [← second_dot_velocity_eq_output_dot
    state output first second incidence] at dotBound
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    at dotBound
  rw [finiteStateVorticityAdvectionPairContribution,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    complexCoordinateVectorNormSq_smul]
  simp only [Complex.normSq_mul, Complex.normSq_I,
    Complex.normSq_ofReal, one_mul]
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have angularNonneg : 0 ≤ (2 * Real.pi) ^ 2 :=
    sq_nonneg _
  have scaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left dotBound angularNonneg)
      (complexCoordinateVectorNormSq_nonneg (state second))
  simpa only [pow_two, mul_assoc] using scaled

private theorem stretchingPairContribution_norm_le
    (state : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse :
      complexWavevector first ⬝ᵥ state first = 0) :
    ‖finiteStateVorticityStretchingPairContribution
        state (first, second)‖ ≤
      (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        vorticityAmplitude state first *
        velocityAmplitude state second := by
  have normSqLe :
      ‖finiteStateVorticityStretchingPairContribution
          state (first, second)‖ ^ 2 ≤
        complexCoordinateAmplitudeSq
          (finiteStateVorticityStretchingPairContribution
            state (first, second)) :=
    complexCoordinateVector_norm_sq_le_amplitudeSq _
  have amplitudeLe :=
    stretchingPairContribution_amplitudeSq_le
      state output first second incidence transverse
  have rhsNonneg :
      0 ≤
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          vorticityAmplitude state first *
          velocityAmplitude state second := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) Real.pi_pos.le)
            (Real.sqrt_nonneg _))
          (vorticityAmplitude_nonneg state first))
        (velocityAmplitude_nonneg state second)
  apply (sq_le_sq₀ (norm_nonneg _) rhsNonneg).mp
  calc
    ‖finiteStateVorticityStretchingPairContribution
        state (first, second)‖ ^ 2 ≤
        complexCoordinateAmplitudeSq
          (finiteStateVorticityStretchingPairContribution
            state (first, second)) :=
      normSqLe
    _ ≤
        (2 * Real.pi) ^ 2 * integerWaveNormSq output *
          complexCoordinateAmplitudeSq (state first) *
          complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient state second) :=
      amplitudeLe
    _ =
        ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          vorticityAmplitude state first *
          velocityAmplitude state second) ^ 2 := by
      symm
      calc
        ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            vorticityAmplitude state first *
            velocityAmplitude state second) ^ 2 =
            (2 * Real.pi) ^ 2 *
              Real.sqrt (integerWaveNormSq output) ^ 2 *
              vorticityAmplitude state first ^ 2 *
              velocityAmplitude state second ^ 2 := by
          ring
        _ =
            (2 * Real.pi) ^ 2 * integerWaveNormSq output *
              complexCoordinateAmplitudeSq (state first) *
              complexCoordinateAmplitudeSq
                (finiteStateVelocityCoefficient state second) := by
          rw [Real.sq_sqrt (integerWaveNormSq_nonneg output),
            vorticityAmplitude_sq state first,
            velocityAmplitude_sq state second]

private theorem advectionPairContribution_norm_le
    (state : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output) :
    ‖finiteStateVorticityAdvectionPairContribution
        state (first, second)‖ ≤
      (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        velocityAmplitude state first *
        vorticityAmplitude state second := by
  have normSqLe :
      ‖finiteStateVorticityAdvectionPairContribution
          state (first, second)‖ ^ 2 ≤
        complexCoordinateAmplitudeSq
          (finiteStateVorticityAdvectionPairContribution
            state (first, second)) :=
    complexCoordinateVector_norm_sq_le_amplitudeSq _
  have amplitudeLe :=
    advectionPairContribution_amplitudeSq_le
      state output first second incidence
  have rhsNonneg :
      0 ≤
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          velocityAmplitude state first *
          vorticityAmplitude state second := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) Real.pi_pos.le)
            (Real.sqrt_nonneg _))
          (velocityAmplitude_nonneg state first))
        (vorticityAmplitude_nonneg state second)
  apply (sq_le_sq₀ (norm_nonneg _) rhsNonneg).mp
  calc
    ‖finiteStateVorticityAdvectionPairContribution
        state (first, second)‖ ^ 2 ≤
        complexCoordinateAmplitudeSq
          (finiteStateVorticityAdvectionPairContribution
            state (first, second)) :=
      normSqLe
    _ ≤
        (2 * Real.pi) ^ 2 * integerWaveNormSq output *
          complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient state first) *
          complexCoordinateAmplitudeSq (state second) :=
      amplitudeLe
    _ =
        ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          velocityAmplitude state first *
          vorticityAmplitude state second) ^ 2 := by
      symm
      calc
        ((2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            velocityAmplitude state first *
            vorticityAmplitude state second) ^ 2 =
            (2 * Real.pi) ^ 2 *
              Real.sqrt (integerWaveNormSq output) ^ 2 *
              velocityAmplitude state first ^ 2 *
              vorticityAmplitude state second ^ 2 := by
          ring
        _ =
            (2 * Real.pi) ^ 2 * integerWaveNormSq output *
              complexCoordinateAmplitudeSq
                (finiteStateVelocityCoefficient state first) *
              complexCoordinateAmplitudeSq (state second) := by
          rw [Real.sq_sqrt (integerWaveNormSq_nonneg output),
            velocityAmplitude_sq state first,
            vorticityAmplitude_sq state second]

private theorem nonlinearPairContribution_norm_le
    (state : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output)
    (transverse :
      complexWavevector first ⬝ᵥ state first = 0) :
    ‖finiteStateVorticityNonlinearPairContribution
        state (first, second)‖ ≤
      (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        (vorticityAmplitude state first *
            velocityAmplitude state second +
          velocityAmplitude state first *
            vorticityAmplitude state second) := by
  rw [finiteStateVorticityNonlinearPairContribution_eq]
  calc
    ‖finiteStateVorticityStretchingPairContribution
          state (first, second) -
        finiteStateVorticityAdvectionPairContribution
          state (first, second)‖ ≤
        ‖finiteStateVorticityStretchingPairContribution
          state (first, second)‖ +
          ‖finiteStateVorticityAdvectionPairContribution
            state (first, second)‖ :=
      norm_sub_le _ _
    _ ≤
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            vorticityAmplitude state first *
            velocityAmplitude state second +
          (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            velocityAmplitude state first *
            vorticityAmplitude state second :=
      add_le_add
        (stretchingPairContribution_norm_le
          state output first second incidence transverse)
        (advectionPairContribution_norm_le
          state output first second incidence)
    _ =
        (2 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          (vorticityAmplitude state first *
              velocityAmplitude state second +
            velocityAmplitude state first *
              vorticityAmplitude state second) := by
      ring

/-! ## Output convolution and complete nonlinear row -/

/-- Scalar velocity--vorticity convolution at one output frequency. -/
def finiteStateVorticityPairConvolutionAmplitude
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : ℝ :=
  ∑ first ∈ modes,
    ∑ second ∈ modes,
      if first + second = output then
        velocityAmplitude state first *
          vorticityAmplitude state second
      else 0

theorem finiteStateVorticityPairConvolutionAmplitude_nonneg
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    0 ≤
      finiteStateVorticityPairConvolutionAmplitude
        modes state output := by
  unfold finiteStateVorticityPairConvolutionAmplitude
  exact Finset.sum_nonneg fun first firstMem =>
    Finset.sum_nonneg fun second secondMem => by
      split_ifs
      · exact mul_nonneg
          (velocityAmplitude_nonneg state first)
          (vorticityAmplitude_nonneg state second)
      · exact le_rfl

/-- The complete ordered-pair aggregate retains the output derivative
factor.  The remaining scalar is exactly twice the velocity--vorticity
convolution, with no interaction-cardinality loss. -/
theorem finiteStateVorticityNonlinearCoefficientAt_norm_le_convolution
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state)
    (output : IntegerWavevector) :
    ‖finiteStateVorticityNonlinearCoefficientAt
        modes state output‖ ≤
      2 * (2 * Real.pi) *
        Real.sqrt (integerWaveNormSq output) *
        finiteStateVorticityPairConvolutionAmplitude
          modes state output := by
  let angular : ℝ :=
    (2 * Real.pi) * Real.sqrt (integerWaveNormSq output)
  let stretchingScalar : ℝ :=
    ∑ first ∈ modes,
      ∑ second ∈ modes,
        if first + second = output then
          vorticityAmplitude state first *
            velocityAmplitude state second
        else 0
  let advectionScalar : ℝ :=
    ∑ first ∈ modes,
      ∑ second ∈ modes,
        if first + second = output then
          velocityAmplitude state first *
            vorticityAmplitude state second
        else 0
  have aggregateNorm :
      ‖finiteStateVorticityNonlinearCoefficientAt
          modes state output‖ ≤
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            ‖if first + second = output then
                finiteStateVorticityNonlinearPairContribution
                  state (first, second)
              else 0‖ := by
    unfold finiteStateVorticityNonlinearCoefficientAt
    exact
      (norm_sum_le modes fun first =>
        ∑ second ∈ modes,
          if first + second = output then
            finiteStateVorticityNonlinearPairContribution
              state (first, second)
          else 0).trans
        (Finset.sum_le_sum fun first firstMem =>
          norm_sum_le modes fun second =>
            if first + second = output then
              finiteStateVorticityNonlinearPairContribution
                state (first, second)
            else 0)
  have pairwiseNorm :
      (∑ first ∈ modes,
          ∑ second ∈ modes,
            ‖if first + second = output then
                finiteStateVorticityNonlinearPairContribution
                  state (first, second)
              else 0‖) ≤
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            if first + second = output then
              angular *
                (vorticityAmplitude state first *
                    velocityAmplitude state second +
                  velocityAmplitude state first *
                    vorticityAmplitude state second)
            else 0 := by
    apply Finset.sum_le_sum
    intro first firstMem
    apply Finset.sum_le_sum
    intro second secondMem
    by_cases incidence : first + second = output
    · simp only [if_pos incidence]
      exact
        nonlinearPairContribution_norm_le
          state output first second incidence
            (stateTransverse first firstMem)
    · simp [incidence]
  have scalarSplit :
      (∑ first ∈ modes,
          ∑ second ∈ modes,
            if first + second = output then
              angular *
                (vorticityAmplitude state first *
                    velocityAmplitude state second +
                  velocityAmplitude state first *
                    vorticityAmplitude state second)
            else 0) =
        angular * stretchingScalar +
          angular * advectionScalar := by
    simp only [stretchingScalar, advectionScalar]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro first firstMem
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro second secondMem
    by_cases incidence : first + second = output <;>
      simp [incidence, mul_add]
  have stretchingEq :
      stretchingScalar =
        finiteStateVorticityPairConvolutionAmplitude
          modes state output := by
    dsimp [stretchingScalar,
      finiteStateVorticityPairConvolutionAmplitude]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro first firstMem
    apply Finset.sum_congr rfl
    intro second secondMem
    by_cases incidence : first + second = output
    · simp [incidence, add_comm, mul_comm]
    · have reverseIncidence : ¬ second + first = output := by
        simpa [add_comm] using incidence
      simp [incidence, reverseIncidence]
  have advectionEq :
      advectionScalar =
        finiteStateVorticityPairConvolutionAmplitude
          modes state output := by
    rfl
  calc
    ‖finiteStateVorticityNonlinearCoefficientAt
        modes state output‖ ≤
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            ‖if first + second = output then
                finiteStateVorticityNonlinearPairContribution
                  state (first, second)
              else 0‖ :=
      aggregateNorm
    _ ≤
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            if first + second = output then
              angular *
                (vorticityAmplitude state first *
                    velocityAmplitude state second +
                  velocityAmplitude state first *
                    vorticityAmplitude state second)
            else 0 :=
      pairwiseNorm
    _ = angular * stretchingScalar +
          angular * advectionScalar :=
      scalarSplit
    _ =
        2 * (2 * Real.pi) *
          Real.sqrt (integerWaveNormSq output) *
          finiteStateVorticityPairConvolutionAmplitude
            modes state output := by
      rw [stretchingEq, advectionEq]
      dsimp [angular]
      ring

/-! ## Discrete Young inequality -/

private theorem pairConvolutionAmplitude_eq_single_sum
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    finiteStateVorticityPairConvolutionAmplitude
        modes state output =
      ∑ first ∈ modes,
        if output - first ∈ modes then
          velocityAmplitude state first *
            vorticityAmplitude state (output - first)
        else 0 := by
  unfold finiteStateVorticityPairConvolutionAmplitude
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

private theorem translated_vorticityAmplitude_sq_sum_le
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (first : IntegerWavevector) :
    (∑ output ∈ modes,
        if output - first ∈ modes then
          vorticityAmplitude state (output - first) ^ 2
        else 0) ≤
      ∑ second ∈ modes,
        vorticityAmplitude state second ^ 2 := by
  let translated : Finset IntegerWavevector :=
    modes.image fun second => first + second
  have filteredSubset :
      modes.filter (fun output => output - first ∈ modes) ⊆
        translated := by
    intro output outputMem
    have membership :=
      Finset.mem_filter.mp outputMem
    apply Finset.mem_image.mpr
    refine ⟨output - first, membership.2, ?_⟩
    abel
  have translatedSum :
      (∑ output ∈ translated,
          vorticityAmplitude state (output - first) ^ 2) =
        ∑ second ∈ modes,
          vorticityAmplitude state second ^ 2 := by
    dsimp [translated]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro second secondMem
      congr 2
      abel
    · intro left leftMem right rightMem equality
      exact add_left_cancel equality
  rw [← Finset.sum_filter]
  exact
    (Finset.sum_le_sum_of_subset_of_nonneg
      filteredSubset
      (fun output outputMem outputNotMem =>
        sq_nonneg
          (vorticityAmplitude state (output - first)))).trans_eq
      translatedSum

/-- Discrete `ℓ¹ * ℓ² → ℓ²` Young inequality on the actual finite
velocity--vorticity convolution.  Translation of the output frequency is
injective, so no cardinality factor appears. -/
theorem sum_pairConvolutionAmplitude_sq_le
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    (∑ output ∈ modes,
        finiteStateVorticityPairConvolutionAmplitude
          modes state output ^ 2) ≤
      (∑ first ∈ modes,
          velocityAmplitude state first) ^ 2 *
        ∑ second ∈ modes,
          vorticityAmplitude state second ^ 2 := by
  let velocitySum : ℝ :=
    ∑ first ∈ modes, velocityAmplitude state first
  let vorticitySqSum : ℝ :=
    ∑ second ∈ modes, vorticityAmplitude state second ^ 2
  let weightedTranslate :
      IntegerWavevector → IntegerWavevector → ℝ :=
    fun output first =>
      if output - first ∈ modes then
        velocityAmplitude state first *
          vorticityAmplitude state (output - first) ^ 2
      else 0
  have velocitySumNonneg : 0 ≤ velocitySum := by
    exact Finset.sum_nonneg fun first firstMem =>
      velocityAmplitude_nonneg state first
  have pointwise :
      ∀ output ∈ modes,
        finiteStateVorticityPairConvolutionAmplitude
            modes state output ^ 2 ≤
          velocitySum *
            ∑ first ∈ modes,
              weightedTranslate output first := by
    intro output outputMem
    rw [pairConvolutionAmplitude_eq_single_sum]
    have cauchy :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
        modes
        (r := fun first =>
          if output - first ∈ modes then
            velocityAmplitude state first *
              vorticityAmplitude state (output - first)
          else 0)
        (f := fun first => velocityAmplitude state first)
        (g := fun first => weightedTranslate output first)
        (fun first firstMem =>
          velocityAmplitude_nonneg state first)
        (fun first firstMem => by
          dsimp [weightedTranslate]
          split_ifs
          · exact mul_nonneg
              (velocityAmplitude_nonneg state first)
              (sq_nonneg _)
          · exact le_rfl)
        (fun first firstMem => by
          dsimp [weightedTranslate]
          by_cases translatedMem : output - first ∈ modes
          · simp only [if_pos translatedMem]
            exact le_of_eq (by ring)
          · simp [translatedMem])
    simpa only [velocitySum] using cauchy
  have weightedTotalLe :
      (∑ output ∈ modes,
          ∑ first ∈ modes,
            weightedTranslate output first) ≤
        velocitySum * vorticitySqSum := by
    rw [Finset.sum_comm]
    calc
      (∑ first ∈ modes,
          ∑ output ∈ modes,
            weightedTranslate output first) ≤
          ∑ first ∈ modes,
            velocityAmplitude state first *
              vorticitySqSum := by
        apply Finset.sum_le_sum
        intro first firstMem
        dsimp [weightedTranslate]
        have factorEq :
            (∑ output ∈ modes,
                if output - first ∈ modes then
                  velocityAmplitude state first *
                    vorticityAmplitude state (output - first) ^ 2
                else 0) =
              velocityAmplitude state first *
                ∑ output ∈ modes,
                  if output - first ∈ modes then
                    vorticityAmplitude state (output - first) ^ 2
                  else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro output outputMem
          by_cases translatedMem : output - first ∈ modes <;>
            simp [translatedMem]
        rw [factorEq]
        exact
          mul_le_mul_of_nonneg_left
            (translated_vorticityAmplitude_sq_sum_le
              modes state first)
            (velocityAmplitude_nonneg state first)
      _ = velocitySum * vorticitySqSum := by
        rw [Finset.sum_mul]
  calc
    (∑ output ∈ modes,
        finiteStateVorticityPairConvolutionAmplitude
          modes state output ^ 2) ≤
        ∑ output ∈ modes,
          velocitySum *
            ∑ first ∈ modes,
              weightedTranslate output first :=
      Finset.sum_le_sum pointwise
    _ =
        velocitySum *
          (∑ output ∈ modes,
            ∑ first ∈ modes,
              weightedTranslate output first) := by
      rw [Finset.mul_sum]
    _ ≤ velocitySum * (velocitySum * vorticitySqSum) :=
      mul_le_mul_of_nonneg_left weightedTotalLe velocitySumNonneg
    _ =
        (∑ first ∈ modes,
            velocityAmplitude state first) ^ 2 *
          ∑ second ∈ modes,
            vorticityAmplitude state second ^ 2 := by
      dsimp [velocitySum, vorticitySqSum]
      ring

/-! ## Whole-tangent negative-one mass -/

/-- Discrete `H⁻¹` mass of the complete finite nonlinear tangent.

The row norm is the norm of the repository's actual
`ComplexCoordinateVector` carrier.  The denominator is the exact positive
Fourier multiplier of `-Δ`; the zero row is assigned zero rather than
dividing by the vanishing multiplier. -/
def finiteStateVorticityNonlinearNegativeOneMass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ output ∈ modes,
    if output = 0 then 0
    else
      ‖finiteStateVorticityNonlinearCoefficientAt
          modes state output‖ ^ 2 /
        integerWaveViscousMultiplier output

theorem finiteStateVorticityNonlinearNegativeOneMass_nonneg
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    0 ≤
      finiteStateVorticityNonlinearNegativeOneMass
        modes state := by
  unfold finiteStateVorticityNonlinearNegativeOneMass
  apply Finset.sum_nonneg
  intro output outputMem
  by_cases outputZero : output = 0
  · simp [outputZero]
  · rw [if_neg outputZero]
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _)
        (integerWaveNormSq_nonneg output))

private theorem nonlinearNegativeOneRow_le_convolution
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0) :
    ‖finiteStateVorticityNonlinearCoefficientAt
        modes state output‖ ^ 2 /
        integerWaveViscousMultiplier output ≤
      4 *
        finiteStateVorticityPairConvolutionAmplitude
          modes state output ^ 2 := by
  let convolution :=
    finiteStateVorticityPairConvolutionAmplitude
      modes state output
  have convolutionNonneg : 0 ≤ convolution :=
    finiteStateVorticityPairConvolutionAmplitude_nonneg
      modes state output
  have rhsNonneg :
      0 ≤
        2 * (2 * Real.pi) *
          Real.sqrt (integerWaveNormSq output) *
          convolution := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (mul_nonneg (by norm_num) Real.pi_pos.le))
          (Real.sqrt_nonneg _))
        convolutionNonneg
  have normLe :
      ‖finiteStateVorticityNonlinearCoefficientAt
          modes state output‖ ≤
        2 * (2 * Real.pi) *
          Real.sqrt (integerWaveNormSq output) *
          convolution := by
    simpa [convolution] using
      finiteStateVorticityNonlinearCoefficientAt_norm_le_convolution
        modes state stateTransverse output
  have normSqLe :
      ‖finiteStateVorticityNonlinearCoefficientAt
          modes state output‖ ^ 2 ≤
        (2 * (2 * Real.pi) *
          Real.sqrt (integerWaveNormSq output) *
          convolution) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) rhsNonneg).mpr normLe
  have multiplierPos :
      0 < integerWaveViscousMultiplier output := by
    unfold integerWaveViscousMultiplier
    exact mul_pos (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
      (integerWaveNormSq_pos outputNe)
  calc
    ‖finiteStateVorticityNonlinearCoefficientAt
        modes state output‖ ^ 2 /
        integerWaveViscousMultiplier output ≤
        (2 * (2 * Real.pi) *
          Real.sqrt (integerWaveNormSq output) *
          convolution) ^ 2 /
          integerWaveViscousMultiplier output :=
      div_le_div_of_nonneg_right normSqLe multiplierPos.le
    _ = 4 * convolution ^ 2 := by
      unfold integerWaveViscousMultiplier
      rw [show
        (2 * (2 * Real.pi) *
            Real.sqrt (integerWaveNormSq output) *
            convolution) ^ 2 =
          4 * (2 * Real.pi) ^ 2 *
            Real.sqrt (integerWaveNormSq output) ^ 2 *
            convolution ^ 2 by ring]
      rw [Real.sq_sqrt (integerWaveNormSq_nonneg output)]
      field_simp [Real.pi_ne_zero,
        integerWaveNormSq_ne_zero outputNe]

/-- The complete finite nonlinear tangent has a cutoff-independent
negative-Sobolev bound:

```text
‖N(ω)‖_{H⁻¹}² ≤ 4 * M(u)² * Y(ω).
```

Only transversality of the actual state is consumed.  The output derivative
is removed by the exact Laplacian multiplier, and discrete Young convolution
then removes every mode-count and maximal-frequency factor. -/
theorem finiteStateVorticityNonlinearNegativeOneMass_le
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state) :
    finiteStateVorticityNonlinearNegativeOneMass
        modes state ≤
      4 * finiteStateVelocityMajorant modes state ^ 2 *
        finiteStateVorticityCoefficientEnstrophy modes state := by
  have rowSumLe :
      finiteStateVorticityNonlinearNegativeOneMass
          modes state ≤
        4 *
          ∑ output ∈ modes,
            finiteStateVorticityPairConvolutionAmplitude
              modes state output ^ 2 := by
    unfold finiteStateVorticityNonlinearNegativeOneMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro output outputMem
    by_cases outputZero : output = 0
    · simp [outputZero,
        finiteStateVorticityPairConvolutionAmplitude_nonneg]
    · rw [if_neg outputZero]
      exact
        nonlinearNegativeOneRow_le_convolution
          modes state stateTransverse output outputZero
  have young :=
    sum_pairConvolutionAmplitude_sq_le modes state
  calc
    finiteStateVorticityNonlinearNegativeOneMass
        modes state ≤
        4 *
          ∑ output ∈ modes,
            finiteStateVorticityPairConvolutionAmplitude
              modes state output ^ 2 :=
      rowSumLe
    _ ≤
        4 *
          ((∑ first ∈ modes,
              velocityAmplitude state first) ^ 2 *
            ∑ second ∈ modes,
              vorticityAmplitude state second ^ 2) :=
      mul_le_mul_of_nonneg_left young (by norm_num)
    _ =
        4 * finiteStateVelocityMajorant modes state ^ 2 *
          finiteStateVorticityCoefficientEnstrophy modes state := by
      unfold finiteStateVelocityMajorant
        finiteVelocityFourierMajorant
        finiteStateVorticityCoefficientEnstrophy
      simp_rw [velocityAmplitude, vorticityAmplitude_sq]
      ring

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
end NavierStokes
end SaturationMonoid
