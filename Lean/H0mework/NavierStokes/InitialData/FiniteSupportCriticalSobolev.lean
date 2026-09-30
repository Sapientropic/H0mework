import Mathlib.Analysis.Calculus.MeanValue
import H0mework.NavierStokes.Fourier.IntegerLatticeCriticalKernel
import H0mework.NavierStokes.InitialData.FiniteSupportPhysicalInvariantTrajectory
import H0mework.NavierStokes.Fourier.ShellSerrinGeometry

/-!
# Cutoff-independent critical Sobolev bound for finite vorticity states

This module is the classical PDE consumer of the generated critical lattice
kernel.  For an arbitrary finite Fourier carrier it proves

```text
|u(x)|^2
  <= (2*pi)^-2 * (sum_{k in Z^3} |k|^-4)
       * sum_{k in modes} |k|^2 |omega_k|^2.
```

The zero mode is handled by the total Biot--Savart definition and contributes
zero to both sides.  The global lattice constant is finite independently of
the Galerkin cutoff.  Thus frequency growth and mode cardinality disappear
from the continuation-side geometry; the remaining analytic responsibility
is exactly the time-integrated vorticity-gradient mass.

The physical field below is the real-part Fourier compilation of an arbitrary
complex state.  Once the source-generated reality invariant is installed,
the same field has the exact Fourier coefficients needed by physical
Parseval.  No reality, transversality, cutoff, support coverage, or
dissipation budget is assumed by the present pointwise estimate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev

open scoped BigOperators Matrix

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicLocalEnergyAlgebra
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalIntegerLatticeCriticalKernel

noncomputable section

private theorem continuousAt_finset_sum'
    {alpha : Type}
    [DecidableEq alpha]
    (indices : Finset alpha)
    {f : alpha → ℝ → ℝ}
    {t : ℝ}
    (continuous : ∀ index ∈ indices, ContinuousAt (f index) t) :
    ContinuousAt (fun time => ∑ index ∈ indices, f index time) t := by
  induction indices using Finset.induction_on with
  | empty =>
      simpa using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t)
  | @insert index indices indexNotMem inductionHypothesis =>
      simp only [Finset.sum_insert indexNotMem]
      exact
        (continuous index (by simp)).add
          (inductionHypothesis fun later laterMem =>
            continuous later (by simp [laterMem]))

/-- Real-part Fourier velocity field compiled from an arbitrary finite
vorticity coefficient state. -/
def finiteStateVelocityRealPartField
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    PhysicalSpace → PhysicalSpace :=
  finiteRealComplexFourierField modes
    (finiteStateVelocityCoefficient state)

/-- Fourier density of the full vorticity-gradient mass, without the
physical `(2*pi)^2` derivative normalization. -/
def finiteStateVorticityEnstrophyMass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes,
    integerWaveNormSq wave *
      complexCoordinateAmplitudeSq (state wave)

theorem finiteStateVorticityEnstrophyMass_nonneg
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    0 ≤ finiteStateVorticityEnstrophyMass modes state := by
  exact Finset.sum_nonneg fun wave waveMem =>
    mul_nonneg (integerWaveNormSq_nonneg wave)
      (complexCoordinateAmplitudeSq_nonneg _)

/-- The full finite vorticity-gradient mass is continuous along every
differentiable coefficient trajectory. -/
theorem finiteStateVorticityEnstrophyMass_continuousAt_of_hasDerivAt
    (modes : Finset IntegerWavevector)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        finiteStateVorticityEnstrophyMass modes (trajectory time)) t := by
  classical
  unfold finiteStateVorticityEnstrophyMass
  let amplitude : IntegerWavevector → ℝ → ℝ :=
    fun wave time => complexCoordinateAmplitudeSq (trajectory time wave)
  have amplitudeContinuous :
      ∀ wave, ContinuousAt (amplitude wave) t := by
    intro wave
    have waveContinuous :
        ContinuousAt (fun time => trajectory time wave) t :=
      (complexVorticityTrajectoryWave_hasDerivAt
        trajectory t tangent wave evolves).continuousAt
    unfold amplitude complexCoordinateAmplitudeSq
    exact continuousAt_finset_sum' Finset.univ fun coordinate coordinateMem =>
      Complex.continuous_normSq.continuousAt.comp
        ((continuous_apply coordinate).continuousAt.comp waveContinuous)
  change
    ContinuousAt
      (fun time =>
        ∑ wave ∈ modes,
          integerWaveNormSq wave * amplitude wave time) t
  exact continuousAt_finset_sum' modes fun wave waveMem =>
    (amplitudeContinuous wave).const_mul _

/-- The global three-dimensional critical kernel is nonnegative. -/
theorem integerWaveCriticalKernel_tsum_nonneg :
    0 ≤ ∑' wave : IntegerWavevector, integerWaveCriticalKernel wave := by
  exact tsum_nonneg fun wave => integerWaveCriticalKernel_nonneg wave

/-- At one frequency, Biot--Savart inversion factors exactly into the
critical lattice kernel and one vorticity-gradient density. -/
theorem finiteStateVelocityCoefficient_criticalAmplitudeSq_le
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    complexCoordinateAmplitudeSq
        (finiteStateVelocityCoefficient state wave) ≤
      biotSavartSerrinConstant * integerWaveCriticalKernel wave *
        (integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) := by
  by_cases waveZero : wave = 0
  · subst wave
    simp [finiteStateVelocityCoefficient, complexCoordinateAmplitudeSq,
      integerWaveCriticalKernel]
  · have sourceBound :=
      biotSavartVelocityCoefficient_normSq_le
        wave (state wave) waveZero
    change
      complexCoordinateVectorNormSq
          (biotSavartVelocityCoefficient wave (state wave)) ≤ _
    calc
      complexCoordinateVectorNormSq
          (biotSavartVelocityCoefficient wave (state wave)) ≤
          complexCoordinateVectorNormSq (state wave) /
            ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) :=
        sourceBound
      _ =
          biotSavartSerrinConstant * integerWaveCriticalKernel wave *
            (integerWaveNormSq wave *
              complexCoordinateVectorNormSq (state wave)) := by
        have waveNormNe : integerWaveNormSq wave ≠ 0 :=
          integerWaveNormSq_ne_zero waveZero
        have piNe : Real.pi ≠ 0 := Real.pi_ne_zero
        unfold biotSavartSerrinConstant integerWaveCriticalKernel
        field_simp

/-! ## Finite and global critical Cauchy bounds -/

/-- Fourier velocity majorant on an arbitrary finite coefficient carrier. -/
def finiteStateVelocityMajorant
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : ℝ :=
  finiteVelocityFourierMajorant modes
    (finiteStateVelocityCoefficient state)

theorem finiteStateVelocityMajorant_nonneg
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    0 ≤ finiteStateVelocityMajorant modes state :=
  finiteVelocityFourierMajorant_nonneg _ _

/-- Exact finite-carrier critical Cauchy estimate before replacing the
finite lattice sum by its global constant. -/
theorem finiteStateVelocityMajorant_sq_le_criticalFiniteSum
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant modes state ^ 2 ≤
      biotSavartSerrinConstant *
        (∑ wave ∈ modes, integerWaveCriticalKernel wave) *
        finiteStateVorticityEnstrophyMass modes state := by
  have cauchyBound :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      modes
      (r := fun wave =>
        Real.sqrt
          (complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient state wave)))
      (f := fun wave =>
        biotSavartSerrinConstant * integerWaveCriticalKernel wave)
      (g := fun wave =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
      (fun wave waveMem =>
        mul_nonneg biotSavartSerrinConstant_nonneg
          (integerWaveCriticalKernel_nonneg wave))
      (fun wave waveMem =>
        mul_nonneg (integerWaveNormSq_nonneg wave)
          (complexCoordinateAmplitudeSq_nonneg _))
      (fun wave waveMem => by
        rw [Real.sq_sqrt
          (complexCoordinateAmplitudeSq_nonneg
            (finiteStateVelocityCoefficient state wave))]
        exact finiteStateVelocityCoefficient_criticalAmplitudeSq_le
          state wave)
  unfold finiteStateVelocityMajorant finiteVelocityFourierMajorant
    finiteStateVorticityEnstrophyMass
  calc
    (∑ wave ∈ modes,
        √(complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state wave))) ^ 2 ≤
        (∑ wave ∈ modes,
          biotSavartSerrinConstant * integerWaveCriticalKernel wave) *
          ∑ wave ∈ modes,
            integerWaveNormSq wave *
              complexCoordinateAmplitudeSq (state wave) :=
      cauchyBound
    _ =
        biotSavartSerrinConstant *
          (∑ wave ∈ modes, integerWaveCriticalKernel wave) *
          ∑ wave ∈ modes,
            integerWaveNormSq wave *
              complexCoordinateAmplitudeSq (state wave) := by
      have factorEq :
          (∑ wave ∈ modes,
            biotSavartSerrinConstant * integerWaveCriticalKernel wave) =
            biotSavartSerrinConstant *
              (∑ wave ∈ modes, integerWaveCriticalKernel wave) := by
        rw [Finset.mul_sum]
      rw [factorEq]

/-- Cutoff-independent majorant estimate using the finite global
three-dimensional lattice constant. -/
theorem finiteStateVelocityMajorant_sq_le_criticalGlobal
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant modes state ^ 2 ≤
      biotSavartSerrinConstant *
        (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave) *
        finiteStateVorticityEnstrophyMass modes state := by
  calc
    finiteStateVelocityMajorant modes state ^ 2 ≤
        biotSavartSerrinConstant *
          (∑ wave ∈ modes, integerWaveCriticalKernel wave) *
          finiteStateVorticityEnstrophyMass modes state :=
      finiteStateVelocityMajorant_sq_le_criticalFiniteSum modes state
    _ ≤
        biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave) *
          finiteStateVorticityEnstrophyMass modes state := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (finite_sum_integerWaveCriticalKernel_le_tsum modes)
          biotSavartSerrinConstant_nonneg)
        (finiteStateVorticityEnstrophyMass_nonneg modes state)

/-- Complete cutoff-independent pointwise bound for the finite real-part
velocity field. -/
theorem finiteStateVelocityRealPartField_norm_sq_le_criticalGlobal
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (x : PhysicalSpace) :
    ‖finiteStateVelocityRealPartField modes state x‖ ^ 2 ≤
      biotSavartSerrinConstant *
        (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave) *
        finiteStateVorticityEnstrophyMass modes state := by
  calc
    ‖finiteStateVelocityRealPartField modes state x‖ ^ 2 ≤
        finiteStateVelocityMajorant modes state ^ 2 :=
      (sq_le_sq₀
        (norm_nonneg _)
        (finiteStateVelocityMajorant_nonneg modes state)).mpr
        (finiteRealComplexFourierField_norm_le_velocityMajorant
          modes (finiteStateVelocityCoefficient state) x)
    _ ≤ _ :=
      finiteStateVelocityMajorant_sq_le_criticalGlobal modes state

private theorem continuousLinearMap_apply_eq_coordinateSum
    (D : PhysicalSpace →L[ℝ] PhysicalSpace)
    (v : PhysicalSpace) (i : Coordinate) :
    D v i =
      ∑ j : Coordinate,
        v j * D (EuclideanSpace.single j 1) i := by
  rw [← (EuclideanSpace.basisFun Coordinate ℝ).sum_repr v,
    map_sum]
  simp only [EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, map_smul,
    WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, PiLp.single_apply,
    mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]

private theorem continuousLinearMap_norm_le_sqrt_coordinateSquare
    (D : PhysicalSpace →L[ℝ] PhysicalSpace) :
    ‖D‖ ≤
      Real.sqrt
        (∑ i : Coordinate, ∑ j : Coordinate,
          (D (EuclideanSpace.single j 1) i) ^ 2) := by
  let G : ℝ :=
    ∑ i : Coordinate, ∑ j : Coordinate,
      (D (EuclideanSpace.single j 1) i) ^ 2
  have hG : 0 ≤ G := by
    dsimp [G]
    positivity
  apply D.opNorm_le_bound (Real.sqrt_nonneg G)
  intro v
  have hRows :
      ‖D v‖ ^ 2 ≤ ‖v‖ ^ 2 * G := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ i : Coordinate, (D v i) ^ 2) =
          ∑ i : Coordinate,
            (∑ j : Coordinate,
              v j * D (EuclideanSpace.single j 1) i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [continuousLinearMap_apply_eq_coordinateSum]
      _ ≤
          ∑ i : Coordinate,
            (∑ j : Coordinate, (v j) ^ 2) *
              ∑ j : Coordinate,
                (D (EuclideanSpace.single j 1) i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact
          Finset.sum_mul_sq_le_sq_mul_sq
            (Finset.univ : Finset Coordinate) v
              (fun j => D (EuclideanSpace.single j 1) i)
      _ = (∑ j : Coordinate, (v j) ^ 2) * G := by
        rw [Finset.mul_sum]
      _ = ‖v‖ ^ 2 * G := by
        rw [EuclideanSpace.real_norm_sq_eq]
  have hRhs : 0 ≤ Real.sqrt G * ‖v‖ :=
    mul_nonneg (Real.sqrt_nonneg G) (norm_nonneg v)
  rw [← sq_le_sq₀ (norm_nonneg (D v)) hRhs]
  simpa only [mul_pow, Real.sq_sqrt hG, mul_comm] using hRows

private theorem finiteRealComplexFourierField_norm_sq_le_card_mul_amplitude
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector)
    (x : PhysicalSpace) :
    ‖finiteRealComplexFourierField modes coefficient x‖ ^ 2 ≤
      (modes.card : ℝ) *
        ∑ wave ∈ modes,
          complexCoordinateAmplitudeSq (coefficient wave) := by
  calc
    ‖finiteRealComplexFourierField modes coefficient x‖ ^ 2 ≤
        finiteVelocityFourierMajorant modes coefficient ^ 2 :=
      finiteRealComplexFourierField_norm_sq_le_velocityMajorant_sq
        modes coefficient x
    _ ≤
        (modes.card : ℝ) *
          ∑ wave ∈ modes,
            (Real.sqrt
              (complexCoordinateAmplitudeSq (coefficient wave))) ^ 2 := by
      unfold finiteVelocityFourierMajorant
      exact sq_sum_le_card_mul_sum_sq
    _ =
        (modes.card : ℝ) *
          ∑ wave ∈ modes,
            complexCoordinateAmplitudeSq (coefficient wave) := by
      congr 1
      apply Finset.sum_congr rfl
      intro wave _
      rw [Real.sq_sqrt (complexCoordinateAmplitudeSq_nonneg _)]

/-- A finite physical Fourier band has pointwise derivative square bounded
by its cardinality times the exact Fourier vorticity-gradient mass. -/
theorem gradientDissipation_finiteRealComplexFourierField_le_card_mul_gradientMass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (x : PhysicalSpace) :
    gradientDissipation
        (finiteRealComplexFourierField modes state) x ≤
      (modes.card : ℝ) * (2 * Real.pi) ^ 2 *
        finiteStateVorticityEnstrophyMass modes state := by
  rw [gradientDissipation_finiteRealComplexFourierField]
  calc
    (∑ direction : Coordinate,
      velocityDot
        (finiteRealComplexFourierField modes
          (angularDerivativeCoefficient state direction))
        (finiteRealComplexFourierField modes
          (angularDerivativeCoefficient state direction)) x) ≤
        ∑ direction : Coordinate,
          (modes.card : ℝ) *
            ∑ wave ∈ modes,
              complexCoordinateAmplitudeSq
                (angularDerivativeCoefficient state direction wave) := by
      apply Finset.sum_le_sum
      intro direction _
      rw [show
        velocityDot
            (finiteRealComplexFourierField modes
              (angularDerivativeCoefficient state direction))
            (finiteRealComplexFourierField modes
              (angularDerivativeCoefficient state direction)) x =
          ‖finiteRealComplexFourierField modes
            (angularDerivativeCoefficient state direction) x‖ ^ 2 by
        unfold velocityDot
        rw [EuclideanSpace.real_norm_sq_eq]
        simp only [pow_two]]
      exact finiteRealComplexFourierField_norm_sq_le_card_mul_amplitude
        modes (angularDerivativeCoefficient state direction) x
    _ =
        (modes.card : ℝ) *
          ∑ wave ∈ modes,
            ∑ direction : Coordinate,
              complexCoordinateAmplitudeSq
                (angularDerivativeCoefficient state direction wave) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
    _ =
        (modes.card : ℝ) * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass modes state := by
      unfold finiteStateVorticityEnstrophyMass
      simp only [
        complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
        angularDerivativeCoefficient_normSq_sum]
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro wave _
      ring

/-- Exact finite-band spatial modulus obtained from the physical derivative
and Fourier-gradient mass, without a modewise trajectory assumption. -/
theorem finiteRealComplexFourierField_norm_sub_le_sqrt_card_gradientMass_mul_norm_sub
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (x y : PhysicalSpace) :
    ‖finiteRealComplexFourierField modes state y -
        finiteRealComplexFourierField modes state x‖ ≤
      Real.sqrt
          ((modes.card : ℝ) * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes state) *
        ‖y - x‖ := by
  let field : PhysicalSpace → PhysicalSpace :=
    finiteRealComplexFourierField modes state
  let bound : ℝ :=
    (modes.card : ℝ) * (2 * Real.pi) ^ 2 *
      finiteStateVorticityEnstrophyMass modes state
  have fieldDifferentiable : Differentiable ℝ field :=
    (finiteRealComplexFourierField_contDiff modes state).differentiable
      (by simp)
  have derivativeBound (point : PhysicalSpace) :
      ‖fderiv ℝ field point‖ ≤ Real.sqrt bound := by
    calc
      ‖fderiv ℝ field point‖ ≤
          Real.sqrt (gradientDissipation field point) := by
        simpa only [field, gradientDissipation] using
          (continuousLinearMap_norm_le_sqrt_coordinateSquare
            (fderiv ℝ field point))
      _ ≤ Real.sqrt bound := by
        exact Real.sqrt_le_sqrt
          (by
            simpa only [field, bound] using
              gradientDissipation_finiteRealComplexFourierField_le_card_mul_gradientMass
                modes state point)
  exact
    convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun point _ => fieldDifferentiable point)
      (fun point _ => derivativeBound point)
      (Set.mem_univ y) (Set.mem_univ x)

/-- The spatial modulus after the exact parabolic physical rescaling
`omega_r(x) = r^2 omega(center + r x)`. -/
theorem finiteRealComplexFourierField_parabolicScale_norm_sub_le
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (scale : ℝ)
    (scaleNonneg : 0 ≤ scale)
    (center x y : PhysicalSpace) :
    ‖(scale ^ 2 : ℝ) •
          finiteRealComplexFourierField modes state (center + scale • y) -
        (scale ^ 2 : ℝ) •
          finiteRealComplexFourierField modes state (center + scale • x)‖ ≤
      scale ^ 3 *
        Real.sqrt
          ((modes.card : ℝ) * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes state) *
        ‖y - x‖ := by
  have unscaled :=
    finiteRealComplexFourierField_norm_sub_le_sqrt_card_gradientMass_mul_norm_sub
      modes state (center + scale • x) (center + scale • y)
  calc
    ‖(scale ^ 2 : ℝ) •
          finiteRealComplexFourierField modes state (center + scale • y) -
        (scale ^ 2 : ℝ) •
          finiteRealComplexFourierField modes state (center + scale • x)‖ =
        scale ^ 2 *
          ‖finiteRealComplexFourierField modes state (center + scale • y) -
            finiteRealComplexFourierField modes state (center + scale • x)‖ := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (sq_nonneg scale)]
    _ ≤ scale ^ 2 *
        (Real.sqrt
            ((modes.card : ℝ) * (2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass modes state) *
          ‖(center + scale • y) - (center + scale • x)‖) :=
      mul_le_mul_of_nonneg_left unscaled (sq_nonneg scale)
    _ = scale ^ 3 *
        Real.sqrt
          ((modes.card : ℝ) * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes state) *
        ‖y - x‖ := by
      have argumentDifference :
          (center + scale • y) - (center + scale • x) =
            scale • (y - x) := by
        module
      rw [argumentDifference, norm_smul,
        Real.norm_of_nonneg scaleNonneg]
      ring

end

end ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
end NavierStokes
end SaturationMonoid
