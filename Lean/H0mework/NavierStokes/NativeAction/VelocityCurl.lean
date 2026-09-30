import H0mework.NavierStokes.UnifiedAction.UnifiedGlobalDuhamel
import H0mework.NavierStokes.NativeAction.Write
import H0mework.NavierStokes.NativeAction.Carrier

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeCompleteVelocityCurl

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeEndpointVelocityCarrier NativeTimeJetCarrier NativeStressSource

noncomputable section

def dotCLM (wave : IntegerWavevector) : ComplexCoordinateVector →L[ℝ] ℂ :=
  ∑ direction : Coordinate, complexWavevector wave direction • ContinuousLinearMap.proj direction

theorem dotCLM_apply (wave : IntegerWavevector) (value : ComplexCoordinateVector) :
    dotCLM wave value = complexWavevector wave ⬝ᵥ value := by
  simp [dotCLM, dotProduct, complexWavevector]

variable {nu : Viscosity}

theorem initial_transverse (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) :
    dotCLM wave (NativeUnifiedGlobalDuhamel.velocity seed wave 0) = 0 := by
  rw [dotCLM_apply, NativeUnifiedGlobalDuhamel.velocity, NativeAbsoluteEventualControl.velocity_initial,
    wholeVelocity_punctured, wholeBiotSavartVelocityState_apply]
  exact complexWavevector_dot_biotSavartVelocityCoefficient _ _

theorem forcing_transverse (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (time : ℝ) :
    dotCLM wave (NativeUnifiedGlobalDuhamel.forcing seed wave time) = 0 := by
  rw [dotCLM_apply, NativeUnifiedGlobalDuhamel.forcing]
  exact complexWavevector_dot_transverseProjection _ _

theorem velocity_transverse (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    dotCLM wave (NativeUnifiedGlobalDuhamel.velocity seed wave time) = 0 := by
  have integral : IntervalIntegrable (fun actual =>
      Real.exp (-NativeUnifiedGlobalDuhamel.damping nu wave * (time - actual)) •
        NativeUnifiedGlobalDuhamel.forcing seed wave actual) volume 0 time :=
    (NativeUnifiedGlobalDuhamel.forcing_intervalIntegrable seed wave 0 time le_rfl nonnegative).continuousOn_smul
      (by fun_prop)
  have written := congrArg (dotCLM wave)
    (NativeUnifiedGlobalDuhamel.source_duhamel seed wave 0 time le_rfl nonnegative)
  rw [map_add, map_smul, initial_transverse, smul_zero, zero_add,
    ← (dotCLM wave).intervalIntegral_comp_comm integral] at written
  simpa only [map_smul, forcing_transverse, smul_zero, intervalIntegral.integral_zero] using written

theorem source_transverse (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (nonnegative : 0 ≤ time) :
    WholeStateTransverse (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) := by
  intro wave
  rw [NativeUnifiedCompleteSource.velocity_read]
  exact velocity_transverse seed wave time nonnegative

theorem source_velocity_from_curl (modes : Finset IntegerWavevector)
    (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) :
    wholeBiotSavartVelocityState (NativeCompleteFilteredWrite.state modes seed time) =
      complexSharpSupportProjection modes (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) := by
  apply lp.ext
  funext wave
  simp only [wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient,
    NativeCompleteFilteredWrite.state_apply, complexSharpSupportProjection_apply]
  by_cases included : wave ∈ modes
  · simp only [if_pos included]
    by_cases zero : wave = 0
    · subst wave
      simp [wholeVelocity_zero, biotSavartVelocityCoefficient]
    · rw [biotSavartVelocityCoefficient_fourierCurlCoefficient wave _ zero,
        transverseProjection_eq_self_of_transverse zero
          (source_transverse seed time nonnegative wave)]
  · simp only [if_neg included, biotSavartVelocityCoefficient_zero_vorticity]

theorem resolved_zero (modes : Finset IntegerWavevector)
    (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    NativeCompleteFilteredWrite.state modes seed time 0 = 0 := by
  rw [NativeCompleteFilteredWrite.state_apply]
  split_ifs <;> simp [fourierCurlCoefficient]

theorem resolved_transverse (modes : Finset IntegerWavevector)
    (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    WholeStateTransverse (NativeCompleteFilteredWrite.state modes seed time) := by
  intro wave
  rw [NativeCompleteFilteredWrite.state_apply]
  split_ifs
  · simp [fourierCurlCoefficient, dotProduct, cross_apply, Fin.sum_univ_three]
    ring
  · simp

theorem resolved_generator_original (modes : Finset IntegerWavevector)
    (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (wave : IntegerWavevector) :
    NativeCompleteAction.resolvedGenerator nu modes (NativeUnifiedCompleteSource.source seed time) wave =
      wholeLatticeVorticityFourierTangentAt nu.coeff (NativeCompleteFilteredWrite.state modes seed time) wave := by
  change nativeFluidConstitutiveVorticityAction
      (quadraticFlux (complexSharpSupportProjection modes
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst))) wave -
      (nu.coeff * integerWaveViscousMultiplier wave) •
        fourierCurlCoefficient wave (complexSharpSupportProjection modes
          (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) wave) = _
  rw [← source_velocity_from_curl modes seed time nonnegative,
    quadraticFlux_biotSavart_action _ (resolved_zero modes seed time) (resolved_transverse modes seed time)]
  unfold wholeLatticeVorticityFourierTangentAt
  congr 1
  congr 1
  rw [source_velocity_from_curl modes seed time nonnegative,
    complexSharpSupportProjection_apply, NativeCompleteFilteredWrite.state_apply]
  split_ifs <;> simp [fourierCurlCoefficient]

end
end SaturationMonoid.NavierStokes.NativeCompleteVelocityCurl
