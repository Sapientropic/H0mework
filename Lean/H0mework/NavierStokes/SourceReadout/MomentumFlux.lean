import H0mework.NavierStokes.SourceReadout.StressAlgebra
import H0mework.NavierStokes.CorrectionControl.Rows

/-!
# Complete source momentum flux

The original whole velocity generates every ordered-pair stress coefficient.
Absolute summability, tensor symmetry and the kinetic bound retain every input
frequency, including the mean stress.
-/

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeStressSource

open scoped BigOperators
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeReceiptKineticTimeModulus
open NativeStressCurlAlgebra
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw

noncomputable section

/-- The full momentum flux, before divergence, uses every ordered source pair. -/
def quadraticFlux (velocity : ComplexVorticityHilbertState) : NativeFluidStressFourierState :=
  fun wave output input => -∑' first : IntegerWavevector,
    velocity first input * velocity (wave - first) output

private theorem coordinate_norm_le_amplitude (velocity : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    ‖velocity wave coordinate‖ ≤ vorticityRowAmplitude velocity wave := by
  apply (norm_le_pi_norm (velocity wave) coordinate).trans
  apply (sq_le_sq₀ (norm_nonneg _) (vorticityRowAmplitude_nonneg _ _)).mp
  rw [vorticityRowAmplitude_sq]
  exact complexCoordinateVector_norm_sq_le_amplitudeSq _

theorem flux_pair_summable (velocity : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    Summable (fun first : IntegerWavevector =>
      velocity first input * velocity (wave - first) output) := by
  apply Summable.of_norm
  apply (summable_fixedOutputVorticityAmplitudeProduct velocity velocity wave).of_nonneg_of_le
  · intro first
    exact norm_nonneg _
  · intro first
    rw [norm_mul]
    exact mul_le_mul (coordinate_norm_le_amplitude velocity first input)
      (coordinate_norm_le_amplitude velocity (wave - first) output)
      (norm_nonneg _) (vorticityRowAmplitude_nonneg _ _)

theorem quadraticFlux_norm_le_mass (velocity : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖quadraticFlux velocity wave output input‖ ≤ wholeVorticityEuclideanMass velocity := by
  have sum := flux_pair_summable velocity wave output input
  unfold quadraticFlux
  rw [norm_neg]
  apply (norm_tsum_le_tsum_norm sum.norm).trans
  calc
    (∑' first, ‖velocity first input * velocity (wave - first) output‖) ≤
        ∑' first, vorticityRowAmplitude velocity first *
          vorticityRowAmplitude velocity (wave - first) := by
      apply Summable.tsum_le_tsum _ sum.norm
        (summable_fixedOutputVorticityAmplitudeProduct velocity velocity wave)
      intro first
      rw [norm_mul]
      exact mul_le_mul (coordinate_norm_le_amplitude velocity first input)
        (coordinate_norm_le_amplitude velocity (wave - first) output)
        (norm_nonneg _) (vorticityRowAmplitude_nonneg _ _)
    _ ≤ Real.sqrt (wholeVorticityEuclideanMass velocity) *
        Real.sqrt (wholeVorticityEuclideanMass velocity) :=
      tsum_fixedOutputVorticityAmplitudeProduct_le_mass velocity velocity wave
    _ = _ := Real.mul_self_sqrt (tsum_nonneg fun _ => sq_nonneg _)

theorem quadraticFlux_symmetric (velocity : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    quadraticFlux velocity wave output input = quadraticFlux velocity wave input output := by
  unfold quadraticFlux
  congr 1
  calc
    (∑' first, velocity first input * velocity (wave - first) output) =
        ∑' first, velocity (wave - first) input * velocity first output := by
      simpa only [outputSubEquiv, Equiv.coe_fn_mk, sub_sub_cancel] using
        (outputSubEquiv wave).tsum_eq
          (fun first => velocity first input * velocity (wave - first) output) |>.symm
    _ = _ := tsum_congr fun _ => mul_comm _ _

/-- The original projection reads its stress from the same complete velocity flux. -/
def correctionStress (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : NativeFluidStressFourierState :=
  fun wave output input =>
    (if wave ∈ modes then quadraticFlux (wholeBiotSavartVelocityState state) wave output input
      else 0) -
    quadraticFlux (wholeBiotSavartVelocityState (complexSharpSupportProjection modes state))
      wave output input

theorem quadraticFlux_biotSavart_norm_le (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖quadraticFlux (wholeBiotSavartVelocityState state) wave output input‖ ≤
      puncturedWholeVorticityKineticMass state := by
  exact (quadraticFlux_norm_le_mass _ wave output input).trans_eq
    (wholeVorticityEuclideanMass_wholeBiotSavartVelocityState state transverse)

/-- All nine original stress coordinates are controlled by the same kinetic ball. -/
theorem correctionStress_norm_le_kinetic (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) (transverse : WholeStateTransverse state)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖correctionStress modes state wave output input‖ ≤
      2 * puncturedWholeVorticityKineticMass state := by
  have massNonneg : 0 ≤ puncturedWholeVorticityKineticMass state := by
    rw [← wholeVorticityEuclideanMass_wholeBiotSavartVelocityState state transverse]
    exact tsum_nonneg fun _ => sq_nonneg _
  have projectedMass : wholeVorticityEuclideanMass
      (wholeBiotSavartVelocityState (complexSharpSupportProjection modes state)) ≤
      wholeVorticityEuclideanMass (wholeBiotSavartVelocityState state) := by
    rw [NativeTurbulenceControl.velocity_projection]
    unfold wholeVorticityEuclideanMass
    apply Summable.tsum_le_tsum _ (summable_vorticityRowAmplitude_sq _)
      (summable_vorticityRowAmplitude_sq _)
    intro frequency
    by_cases inside : frequency ∈ modes
    · simp only [vorticityRowAmplitude, complexSharpSupportProjection_apply, if_pos inside]
      rfl
    · simp only [vorticityRowAmplitude, complexSharpSupportProjection_apply, if_neg inside]
      simp only [complexCoordinateAmplitudeSq, Pi.zero_apply, map_zero, Finset.sum_const_zero,
        Real.sqrt_zero, zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
  rw [wholeVorticityEuclideanMass_wholeBiotSavartVelocityState state transverse] at projectedMass
  have resolved := (quadraticFlux_norm_le_mass
    (wholeBiotSavartVelocityState (complexSharpSupportProjection modes state)) wave output input).trans
    projectedMass
  have full : ‖if wave ∈ modes then
      quadraticFlux (wholeBiotSavartVelocityState state) wave output input else 0‖ ≤
        puncturedWholeVorticityKineticMass state := by
    split_ifs
    · exact quadraticFlux_biotSavart_norm_le state transverse wave output input
    · simpa only [norm_zero] using massNonneg
  exact (norm_sub_le _ _).trans ((add_le_add full resolved).trans_eq (by ring))


end
end SaturationMonoid.NavierStokes.NativeStressSource
