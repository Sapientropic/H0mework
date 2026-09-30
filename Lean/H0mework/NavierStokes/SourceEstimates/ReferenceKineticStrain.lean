import H0mework.NavierStokes.Energy.WholeKineticDifferenceCancellation
import H0mework.NavierStokes.SourceEstimates.CoefficientWork

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.ReferenceKinetic

open scoped BigOperators Matrix
open Set Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinStretchingCriticalBound
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget

noncomputable section

def strain (modes : Finset IntegerWavevector) (field : ComplexVorticityHilbertState) : Real :=
  ∑ wave ∈ modes, vorticityRowAmplitude field wave

private theorem pair_work_le (state ambient : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector) (nonzero : second ≠ 0)
    (transverse : complexWavevector second ⬝ᵥ ambient second = 0) :
    |complexCoordinateRealInner (finiteStateVelocityCoefficient state output)
      (finiteStateVelocityBilinearPairContribution state ambient (first, second))| ≤
      vorticityRowAmplitude ambient second *
        (velocityRowAmplitude state first * velocityRowAmplitude state output) := by
  have dot := complexWavevector_dot_normSq_le second (finiteStateVelocityCoefficient state first)
  have pair : complexCoordinateAmplitudeSq
      (finiteStateVelocityBilinearPairContribution state ambient (first, second)) ≤
      complexCoordinateAmplitudeSq (ambient second) *
        complexCoordinateAmplitudeSq (finiteStateVelocityCoefficient state first) := by
    rw [finiteStateVelocityBilinearPairContribution,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq, complexCoordinateVectorNormSq_smul]
    simp only [Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_I,
      Complex.normSq_ofReal, one_mul]
    have scaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left dot
      (sq_nonneg (2 * Real.pi)))
      (complexCoordinateVectorNormSq_nonneg (finiteStateVelocityCoefficient ambient second))
    have norm := biotSavartVelocityCoefficient_normSq_of_transverse second (ambient second) nonzero transverse
    change complexCoordinateVectorNormSq (finiteStateVelocityCoefficient ambient second) = _ at norm
    rw [norm] at scaled ⊢
    simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] at scaled ⊢
    convert! scaled using 1 <;>
      field_simp [integerWaveNormSq_ne_zero nonzero, Real.pi_ne_zero]
  have bound := (complexCoordinateRealInner_sq_le
    (finiteStateVelocityCoefficient state output)
    (finiteStateVelocityBilinearPairContribution state ambient (first, second))).trans
      (mul_le_mul_of_nonneg_left pair (complexCoordinateAmplitudeSq_nonneg _))
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (vorticityRowAmplitude_nonneg _ _)
    (mul_nonneg (velocityRowAmplitude_nonneg _ _) (velocityRowAmplitude_nonneg _ _)))).mp
  rw [sq_abs, mul_pow, mul_pow, vorticityRowAmplitude_sq,
    velocityRowAmplitude_sq, velocityRowAmplitude_sq]
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] at bound ⊢
  nlinarith only [bound]

private theorem shifted_product_sum_le (modes : Finset IntegerWavevector)
    (field : ComplexVorticityHilbertState) (second : IntegerWavevector) :
    (∑ first ∈ modes.filter (fun first => first + second ∈ modes),
      velocityRowAmplitude field first * velocityRowAmplitude field (first + second)) ≤
      ∑ wave ∈ modes, complexCoordinateAmplitudeSq (finiteStateVelocityCoefficient field wave) := by
  classical
  let rows := modes.filter fun first => first + second ∈ modes
  have first : (∑ wave ∈ rows, velocityRowAmplitude field wave ^ 2) ≤
      ∑ wave ∈ modes, velocityRowAmplitude field wave ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have secondBound : (∑ wave ∈ rows, velocityRowAmplitude field (wave + second) ^ 2) ≤
      ∑ wave ∈ modes, velocityRowAmplitude field wave ^ 2 := by
    calc
      _ = ∑ wave ∈ rows.image (fun first => first + second), velocityRowAmplitude field wave ^ 2 := by
        symm
        exact Finset.sum_image (fun _ _ _ _ same => add_right_cancel same)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
        intro wave member
        rcases Finset.mem_image.mp member with ⟨first, inside, rfl⟩
        exact (Finset.mem_filter.mp inside).2) (fun _ _ _ => sq_nonneg _)
  have young : 2 * (∑ first ∈ rows,
      velocityRowAmplitude field first * velocityRowAmplitude field (first + second)) ≤
      (∑ first ∈ rows, velocityRowAmplitude field first ^ 2) +
        ∑ first ∈ rows, velocityRowAmplitude field (first + second) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun first _ => by
      nlinarith [sq_nonneg (velocityRowAmplitude field first - velocityRowAmplitude field (first + second))]
  simp only [velocityRowAmplitude_sq] at first secondBound young
  dsimp only [rows] at young
  linarith

/-- The surviving transport placement differentiates the finite reference,
so its coefficient is the vorticity ℓ¹ mass with no inverse viscosity. -/
theorem finite_pairing_abs_le_strain (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes) (state ambient : ComplexVorticityHilbertState)
    (transverse : FiniteStateTransverseOn modes ambient) :
    |finiteStateVelocityBilinearEnergyPairing modes state state ambient| ≤
      strain modes ambient * (2 * finiteStateVorticityKineticEnergy modes state) := by
  classical
  rw [finiteStateVelocityBilinearEnergyPairing_eq_pair_sum, Finset.sum_comm]
  have sliced : (∑ second ∈ modes, ∑ first ∈ modes,
      if first + second ∈ modes then complexCoordinateRealInner
        (finiteStateVelocityCoefficient state (first + second))
        (finiteStateVelocityBilinearPairContribution state ambient (first, second)) else 0) =
      ∑ second ∈ modes, ∑ first ∈ modes.filter (fun first => first + second ∈ modes),
        complexCoordinateRealInner (finiteStateVelocityCoefficient state (first + second))
          (finiteStateVelocityBilinearPairContribution state ambient (first, second)) := by
    simp only [Finset.sum_filter]
  rw [sliced]
  calc
    _ ≤ ∑ second ∈ modes, ∑ first ∈ modes.filter (fun first => first + second ∈ modes),
        |complexCoordinateRealInner (finiteStateVelocityCoefficient state (first + second))
          (finiteStateVelocityBilinearPairContribution state ambient (first, second))| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ second ∈ modes, vorticityRowAmplitude ambient second *
        (∑ first ∈ modes.filter (fun first => first + second ∈ modes),
          velocityRowAmplitude state first * velocityRowAmplitude state (first + second)) := by
      apply Finset.sum_le_sum
      intro second member
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun first _ => pair_work_le state ambient _ first second
        (fun zero => zeroNotMem (zero ▸ member)) (transverse second member)
    _ ≤ ∑ second ∈ modes, vorticityRowAmplitude ambient second *
        (∑ wave ∈ modes, complexCoordinateAmplitudeSq (finiteStateVelocityCoefficient state wave)) :=
      Finset.sum_le_sum fun second _ => mul_le_mul_of_nonneg_left
        (shifted_product_sum_le modes state second) (vorticityRowAmplitude_nonneg _ _)
    _ = _ := by
      rw [← Finset.sum_mul, finiteStateVelocityAmplitudeSq_sum_eq_two_kineticEnergy]
      rfl

end
end SaturationMonoid.NavierStokes.ReferenceKinetic
