import H0mework.NavierStokes.SourceEstimates.NonlinearWork
import H0mework.NavierStokes.SourceEstimates.WholeKineticCarrier
import H0mework.NavierStokes.Energy.WholeKineticDifferenceCancellation

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.CriticalError

open Set Filter
open scoped Topology
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientWholeActionTube
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy

noncomputable section

theorem coefficientWork_eq_inner (left right : ComplexVorticityHilbertState) :
    CoefficientWork.value left right = ∑ coordinate : Coordinate,
      (inner Complex (wholeCoordinateSliceCLM coordinate left) (wholeCoordinateSliceCLM coordinate right)).re := by
  have rowSum (coordinate : Coordinate) : Summable fun wave : IntegerWavevector =>
      (inner Complex (wholeCoordinateSliceCLM coordinate left wave) (wholeCoordinateSliceCLM coordinate right wave)).re :=
    (Complex.hasSum_re (lp.hasSum_inner (wholeCoordinateSliceCLM coordinate left)
      (wholeCoordinateSliceCLM coordinate right))).summable
  symm
  simp_rw [lp.inner_eq_tsum, Complex.re_tsum (lp.hasSum_inner _ _).summable]
  rw [← Summable.tsum_finsetSum (fun coordinate _ => rowSum coordinate)]
  apply tsum_congr
  intro wave
  unfold complexCoordinateRealInner
  apply Finset.sum_congr rfl
  intro coordinate _
  simp [RCLike.inner_apply, Complex.mul_re, wholeCoordinateSliceCLM_apply]
  ring

theorem coefficientWork_continuous : Continuous (fun fields : ComplexVorticityHilbertState × ComplexVorticityHilbertState =>
    CoefficientWork.value fields.1 fields.2) := by
  simp_rw [coefficientWork_eq_inner]
  apply continuous_finsetSum
  intro coordinate _
  exact Complex.continuous_re.comp (((wholeCoordinateSliceCLM coordinate).continuous.comp continuous_fst).inner
    ((wholeCoordinateSliceCLM coordinate).continuous.comp continuous_snd))

theorem work_eq_weighted (field : ComplexVorticityHilbertState) (transverse : WholeStateTransverse field)
    (gradient : Summable fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq (field wave)) :
    NonlinearWork.value field = CoefficientWork.value (NonlinearWork.gradientState field gradient)
      (wholeStateVorticityNonlinearNegativeOneState field transverse gradient) := by
  apply tsum_congr
  intro wave
  rw [NonlinearWork.gradientState, wholeStateVorticityViscousNegativeOneState_apply,
    wholeStateVorticityViscousNegativeOneWeightedCoefficient, one_mul,
    wholeStateVorticityNonlinearNegativeOneState_apply, wholeStateVorticityNonlinearNegativeOneWeightedCoefficient]
  by_cases zero : wave = 0
  · subst wave
    rw [if_pos rfl, wholeStateVorticityNonlinearCoefficientAt_zero_of_transverse field transverse]
    simp [complexCoordinateRealInner]
  · rw [if_neg zero, WholeKineticDecay.realInner_smul_left, complexCoordinateRealInner_real_smul_right,
      ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.2 (integerWaveViscousMultiplier_pos ⟨wave, zero⟩)).ne', one_mul]

theorem projected_work_eq_finite (modes : Finset IntegerWavevector) (field : ComplexVorticityHilbertState) :
    NonlinearWork.value (complexSharpSupportProjection modes field) = finiteStateVorticityNonlinearWork modes field := by
  unfold NonlinearWork.value finiteStateVorticityNonlinearWork
  simp_rw [wholeStateVorticityNonlinearCoefficientAt_projection_eq_finite]
  rw [tsum_eq_sum (s := modes)]
  · apply Finset.sum_congr rfl
    intro wave inside
    simp only [complexSharpSupportProjection_apply, if_pos inside]
  · intro wave outside
    simp [complexSharpSupportProjection_apply, outside, complexCoordinateRealInner]

end
end SaturationMonoid.NavierStokes.CriticalError
