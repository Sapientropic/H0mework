import H0mework.NavierStokes.SourceGeometry.VectorWorkRow
import H0mework.NavierStokes.InitialData.FiniteSupportCriticalSobolev

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open scoped Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev

noncomputable section

theorem finite_velocity_test_sq_le (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes) (state : ComplexVorticityHilbertState) (a x : PhysicalSpace) :
    inner ℝ a (finiteStateVelocityRealPartField modes state x) ^ 2 ≤
      ((∑ wave ∈ modes, testGramRow wave a) / (2 * Real.pi) ^ 2) *
        finiteStateVorticityEnstrophyMass modes state := by
  have bound := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul modes
    (r := fun wave => inner ℝ a (realComplexFourierMode wave
      (biotSavartVelocityCoefficient wave (state wave)) x))
    (f := fun wave => testGramRow wave a / (2 * Real.pi) ^ 2)
    (g := fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq (state wave))
    (fun wave _ => div_nonneg (testGramRow_nonneg wave a) (sq_nonneg _))
    (fun wave _ => mul_nonneg (integerWaveNormSq_nonneg wave) (complexCoordinateAmplitudeSq_nonneg _))
    (fun wave inside => biot_row_inner_sq_le wave (fun h => zeroNotMem (h ▸ inside))
      a x (state wave))
  simpa only [finiteStateVelocityRealPartField, finiteRealComplexFourierField,
    finiteStateVelocityCoefficient, inner_sum, Finset.sum_div,
    finiteStateVorticityEnstrophyMass] using bound

theorem finite_velocity_norm_sq_le_of_testGram (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes) (state : ComplexVorticityHilbertState)
    (C : ℝ) (C0 : 0 ≤ C)
    (gram : ∀ a : PhysicalSpace, (∑ wave ∈ modes, testGramRow wave a) ≤ C * ‖a‖ ^ 2)
    (x : PhysicalSpace) :
    ‖finiteStateVelocityRealPartField modes state x‖ ^ 2 ≤
      (C / (2 * Real.pi) ^ 2) * finiteStateVorticityEnstrophyMass modes state := by
  let u := finiteStateVelocityRealPartField modes state x
  have D0 := finiteStateVorticityEnstrophyMass_nonneg modes state
  have bound := finite_velocity_test_sq_le modes zeroNotMem state u x
  change inner ℝ u u ^ 2 ≤ _ at bound
  rw [real_inner_self_eq_norm_sq] at bound
  by_cases zero : ‖u‖ ^ 2 = 0
  · change ‖u‖ ^ 2 ≤ _
    rw [zero]
    exact mul_nonneg (div_nonneg C0 (sq_nonneg _)) D0
  · have positive : 0 < ‖u‖ ^ 2 := (sq_nonneg _).lt_of_ne' zero
    have scaled : ‖u‖ ^ 2 * ‖u‖ ^ 2 ≤
        ‖u‖ ^ 2 * ((C / (2 * Real.pi) ^ 2) * finiteStateVorticityEnstrophyMass modes state) := by
      calc
        ‖u‖ ^ 2 * ‖u‖ ^ 2 ≤
            ((∑ wave ∈ modes, testGramRow wave u) / (2 * Real.pi) ^ 2) *
              finiteStateVorticityEnstrophyMass modes state := by simpa only [pow_two] using bound
        _ ≤ ((C * ‖u‖ ^ 2) / (2 * Real.pi) ^ 2) *
              finiteStateVorticityEnstrophyMass modes state :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (gram u) (sq_nonneg _)) D0
        _ = _ := by ring
    exact le_of_mul_le_mul_left scaled positive

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
