import H0mework.NavierStokes.StressDynamics.CommonAdvector

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeConvectionFlux

open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeCommonAdvectorAction NativeHigherTimeJets NativeStressCurlAlgebra NativeTimeJetCarrier

noncomputable section

theorem mixed_divergence (left right : ComplexVorticityHilbertState)
    (transverse : ∀ wave, complexWavevector wave ⬝ᵥ left wave = 0) (wave : IntegerWavevector) :
    nativeFluidStressDivergenceCoefficient (mixedFlux left right) wave =
      wholeStateVelocityBilinearCoefficientAt left right wave := by
  let row : IntegerWavevector → NativeFluidStressCoefficient :=
    fun first output input => -(right (wave - first) output * left first input)
  have summable : Summable row := by
    apply Pi.summable.mpr
    intro output
    apply Pi.summable.mpr
    intro input
    simpa only [row, mul_comm] using (mixed_pair_summable left right wave output input).neg
  have same : mixedFlux left right wave = ∑' first, row first := by
    funext output input
    rw [tsum_apply summable, tsum_apply (Pi.summable.mp summable output)]
    simp only [mixedFlux, row, ← tsum_neg, mul_comm]
  change stressDivergenceCLM wave (mixedFlux left right wave) = _
  rw [same, (stressDivergenceCLM wave).map_tsum summable]
  unfold wholeStateVelocityBilinearCoefficientAt
  apply tsum_congr
  intro first
  have pair := nativeFluidStressDivergenceCoefficient_negativePair left right first (wave - first) (transverse first)
  rw [show first + (wave - first) = wave by abel] at pair
  exact pair

theorem finite_convection (modes : Finset IntegerWavevector)
    (advector velocity : ComplexVorticityHilbertState)
    (advectorSupported : ∀ wave, wave ∉ modes → advector wave = 0)
    (velocitySupported : ∀ wave, wave ∉ modes → velocity wave = 0) (wave : IntegerWavevector) :
    convectionCLM modes advector wave velocity =
      wholeStateVelocityBilinearCoefficientAt (wholeBiotSavartVelocityState advector) velocity wave := by
  unfold wholeStateVelocityBilinearCoefficientAt
  rw [tsum_eq_sum (s := modes) (fun first outside => by
    simp [wholeStateVelocityBilinearPairContribution, wholeBiotSavartVelocityState_apply,
      finiteStateVelocityCoefficient, advectorSupported first outside, biotSavartVelocityCoefficient])]
  simp only [convectionCLM, sum_apply]
  change (∑ first ∈ modes, ∑ second ∈ modes,
    (if first + second = wave then pairCLM advector first second else 0) velocity) = _
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.sum_eq_single (wave - first)]
  · rw [if_pos (show first + (wave - first) = wave by abel)]
    rfl
  · intro second _ different
    rw [if_neg (fun same => different (by rw [← same]; abel))]
    rfl
  · intro outside
    rw [if_pos (show first + (wave - first) = wave by abel)]
    rw [pairCLM, smul_apply]
    change -_ • velocity (wave - first) = 0
    rw [velocitySupported _ outside, smul_zero]

theorem operator_stress_row (modes : Finset IntegerWavevector)
    (nu : ThreeDimensionalPeriodicFilteredNavierStokesGenerator.Viscosity)
    (advector velocity : ComplexVorticityHilbertState)
    (advectorSupported : ∀ wave, wave ∉ modes → advector wave = 0)
    (velocitySupported : ∀ wave, wave ∉ modes → velocity wave = 0)
    (velocityTransverse : FiniteStateTransverseOn modes velocity)
    (wave : IntegerWavevector) (inside : wave ∈ modes) (nonzero : wave ≠ 0) :
    frozenOperator modes nu advector velocity wave =
      projectedDivergenceCLM wave (mixedFlux (wholeBiotSavartVelocityState advector) velocity wave) -
        (nu.coeff * integerWaveViscousMultiplier wave) • velocity wave := by
  rw [operator_apply, if_pos inside, finite_convection modes advector velocity advectorSupported velocitySupported,
    ← mixed_divergence _ _ (wholeBiotSavartVelocityState_transverse advector)]
  change (transverseProjectionCLM wave) (_ - _ • velocity wave) = _
  rw [map_sub, map_smul]
  simp only [transverseProjectionCLM_apply]
  rw [transverseProjection_eq_self_of_transverse nonzero (velocityTransverse wave inside)]
  rfl

end
end SaturationMonoid.NavierStokes.NativeConvectionFlux
