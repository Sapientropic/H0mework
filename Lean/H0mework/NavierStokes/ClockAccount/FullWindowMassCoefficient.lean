import H0mework.NavierStokes.NativeWorkWhole.RestartBlockKineticLedger
import H0mework.NavierStokes.Butterfly.StackedKineticAdvance

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.WindowMassCoefficient

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalIntegerLatticeCriticalKernelExplicitTail
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientWholeRestartBlockKineticLedger
open RationalVorticityEvaluator
open RationalVorticityEvaluator.ButterflyStackedKineticAdvance

noncomputable section

def epsilon : Real :=
  wholeRestartCubicFourthCoefficient butterflyGainViscosity / butterflyGainViscosity.coeff

def halfCriticalMass : Real :=
  butterflyGainViscosity.coeff ^ 2 * (2 * Real.pi) ^ 2 /
    (2 * criticalEnstrophyLatticeConstant)

theorem epsilon_eq : epsilon = 6561 / 89989120000000000000000 := by
  unfold epsilon wholeRestartCubicFourthCoefficient
  rw [butterflyGainSeventhCoefficient_eq]
  unfold biotSavartSerrinConstant butterflyGainViscosity
  field_simp [Real.pi_ne_zero]
  ring

theorem kernel_tsum_le_fifty_three :
    (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave) ≤ 53 := by
  have pointwise : ∀ wave : IntegerWavevector, integerWaveCriticalKernel wave ≤ 1 := by
    intro wave
    by_cases zero : wave = 0
    · simp [zero]
    · have normOne := one_le_integerWaveNormSq wave zero
      have inverseLe : (integerWaveNormSq wave)⁻¹ ≤ 1 := by
        exact inv_le_one_of_one_le₀ normOne
      unfold integerWaveCriticalKernel
      exact pow_le_one₀ (inv_nonneg.mpr (integerWaveNormSq_nonneg wave)) inverseLe
  apply summable_integerWaveCriticalKernel.tsum_le_of_sum_le
  intro modes
  have low : (∑ wave ∈ modes ∩ integerWaveFrequencyCube 1,
      integerWaveCriticalKernel wave) ≤ 27 := by
    have restricted := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.inter_subset_right : modes ∩ integerWaveFrequencyCube 1 ⊆
        integerWaveFrequencyCube 1)
      (fun wave _ _ => integerWaveCriticalKernel_nonneg wave)
    have cube : (∑ wave ∈ integerWaveFrequencyCube 1,
        integerWaveCriticalKernel wave) ≤ 27 := by
      calc
        _ ≤ ∑ _wave ∈ integerWaveFrequencyCube 1, (1 : Real) :=
          Finset.sum_le_sum fun wave _ => pointwise wave
        _ = 27 := by simp [integerWaveFrequencyCube_card]
    exact restricted.trans cube
  have high := finiteModes_integerWaveCriticalKernel_tail_le 1 (by omega) modes
  norm_num at high
  have split := Finset.sum_inter_add_sum_sdiff
    modes (integerWaveFrequencyCube 1) integerWaveCriticalKernel
  linarith

theorem halfCriticalMass_half_eq :
    halfCriticalMass / 2 =
      1 / (40000 * ∑' wave : IntegerWavevector, integerWaveCriticalKernel wave) := by
  unfold halfCriticalMass criticalEnstrophyLatticeConstant
    biotSavartSerrinConstant butterflyGainViscosity
  field_simp [Real.pi_ne_zero]
  ring

theorem epsilon_le_halfCriticalMass_half : epsilon ≤ halfCriticalMass / 2 := by
  rw [epsilon_eq, halfCriticalMass_half_eq]
  have kernelPos : 0 < ∑' wave : IntegerWavevector, integerWaveCriticalKernel wave := by
    have positive := criticalEnstrophyLatticeConstant_pos
    unfold criticalEnstrophyLatticeConstant at positive
    exact pos_of_mul_pos_right positive biotSavartSerrinConstant_nonneg
  have reciprocal := one_div_le_one_div_of_le
    (mul_pos (by norm_num : (0 : Real) < 40000) kernelPos)
    (mul_le_mul_of_nonneg_left kernel_tsum_le_fifty_three
      (by norm_num : (0 : Real) ≤ 40000))
  calc
    _ ≤ 1 / (40000 * (53 : Real)) := by norm_num
    _ ≤ _ := reciprocal

end
end SaturationMonoid.NavierStokes.WindowMassCoefficient
