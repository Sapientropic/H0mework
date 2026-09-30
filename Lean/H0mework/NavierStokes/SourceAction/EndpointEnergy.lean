import H0mework.NavierStokes.SourceAction.Dissipation
import H0mework.NavierStokes.VelocityGalerkin.UniformKineticLedger

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeFullOrderRecovery

open Set MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open NativeFullOrderEnergy NativeFullOrderAction NativeFullOrderEvolution

noncomputable section

variable {nu : Viscosity}
  {endpoint : ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.WholeRestartVelocityEndpointState}
  {radius : ℕ}

theorem endpoint_energy_hasDerivAt
    (stage : GeneratedWholeRestartVelocityEndpointGalerkinStage nu endpoint radius)
    (weight : IntegerWavevector → ℝ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun actual => weightedVelocityEnergy (wholeRestartModes radius) weight (stage.trajectory actual))
      (2 * ∑ wave ∈ wholeRestartModes radius, weight wave ^ 2 * complexCoordinateRealInner
        (finiteStateVelocityCoefficient (stage.trajectory time) wave)
        (biotSavartVelocityCoefficient wave
          (finiteStateVorticityGenerator (wholeRestartModes radius) nu.coeff (stage.trajectory time) wave))) time := by
  have actual := (stage.physical time inside).1
  rw [← frozenGenerator_self (wholeRestartModes radius) nu.coeff (stage.trajectory time)] at actual
  have derivative := observed_energy_from_stageNine
    (weightedVelocityRead (wholeRestartModes radius) weight)
    (frozenGenerator (wholeRestartModes radius) nu.coeff (stage.trajectory time))
    stage.trajectory univ time actual.hasDerivWithinAt
  rw [frozenGenerator_self, real_inner_comm, weightedVelocityRead_inner] at derivative
  simpa only [weightedVelocityRead_norm_sq, hasDerivWithinAt_univ, finiteStateVelocityCoefficient] using derivative

theorem endpoint_energy_action_hasDerivAt
    (stage : GeneratedWholeRestartVelocityEndpointGalerkinStage nu endpoint radius)
    (weight : IntegerWavevector → ℝ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun actual => weightedVelocityEnergy (wholeRestartModes radius) weight (stage.trajectory actual))
      (2 * weightedVelocityNonlinearWork (wholeRestartModes radius) weight (stage.trajectory time) -
        2 * nu.coeff * weightedVelocityDissipation (wholeRestartModes radius) weight (stage.trajectory time)) time := by
  have derivative := endpoint_energy_hasDerivAt stage weight time inside
  have work :
      (∑ wave ∈ wholeRestartModes radius, weight wave ^ 2 * complexCoordinateRealInner
        (finiteStateVelocityCoefficient (stage.trajectory time) wave)
        (biotSavartVelocityCoefficient wave
          (finiteStateVorticityGenerator (wholeRestartModes radius) nu.coeff (stage.trajectory time) wave))) =
      weightedVelocityNonlinearWork (wholeRestartModes radius) weight (stage.trajectory time) -
        nu.coeff * weightedVelocityDissipation (wholeRestartModes radius) weight (stage.trajectory time) := by
    unfold weightedVelocityNonlinearWork weightedVelocityDissipation
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro wave waveMem
    have waveNe : wave ≠ 0 := fun same =>
      zero_not_mem_puncturedIntegerWaveFrequencyCube radius (same ▸ waveMem)
    rw [biotSavart_finiteStateVorticityGenerator_eq_velocityUpdate
      (wholeRestartModes radius) (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
      nu.coeff (stage.trajectory time) (fun actual _ => (stage.physical time inside).2.2.1 actual) wave waveMem,
      complexCoordinateRealInner_sub_right,
      complexCoordinateRealInner_transverseProjection wave
        (finiteStateVelocityCoefficient (stage.trajectory time) wave) _ waveNe
        (by exact complexWavevector_dot_biotSavartVelocityCoefficient wave (stage.trajectory time wave)),
      complexCoordinateRealInner_real_smul_right, complexCoordinateRealInner_self,
      wholeStateVelocityNonlinearCoefficientAt_finiteStateWholeVelocity]
    ring
  rw [work] at derivative
  convert derivative using 1
  ring

theorem endpoint_energy_retained_dissipation
    (stage : GeneratedWholeRestartVelocityEndpointGalerkinStage nu endpoint radius)
    (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) :
    deriv (fun actual => weightedVelocityEnergy (wholeRestartModes radius)
      (wordWeight order ceiling) (stage.trajectory actual)) time +
        nu.coeff * weightedVelocityDissipation (wholeRestartModes radius)
          (wordWeight order ceiling) (stage.trajectory time) ≤
      wordRate order nu * finiteStateVelocityMajorant (wholeRestartModes radius)
        (stage.trajectory time) ^ 2 * weightedVelocityEnergy (wholeRestartModes radius)
          (wordWeight order ceiling) (stage.trajectory time) := by
  have source := NativeFullOrderStress.power_young (wholeRestartModes radius) order ceiling nonnegative
    (finiteStateWholeVelocity (wholeRestartModes radius) (stage.trajectory time))
    (finite_amplitude_summable (wholeRestartModes radius) (stage.trajectory time))
    (finite_velocity_supported (wholeRestartModes radius) (stage.trajectory time)) nu.coeff nu.coeff_pos
  rw [finite_majorant_eq, finite_energy_eq, finite_dissipation_eq] at source
  rw [(endpoint_energy_action_hasDerivAt stage (wordWeight order ceiling) time inside).deriv]
  rw [show 2 * weightedVelocityNonlinearWork (wholeRestartModes radius) (wordWeight order ceiling)
      (stage.trajectory time) - 2 * nu.coeff * weightedVelocityDissipation (wholeRestartModes radius)
      (wordWeight order ceiling) (stage.trajectory time) + nu.coeff * weightedVelocityDissipation
      (wholeRestartModes radius) (wordWeight order ceiling) (stage.trajectory time) =
    2 * weightedVelocityNonlinearWork (wholeRestartModes radius) (wordWeight order ceiling)
      (stage.trajectory time) - nu.coeff * weightedVelocityDissipation (wholeRestartModes radius)
      (wordWeight order ceiling) (stage.trajectory time) by ring]
  rw [finite_work_eq_stress]
  exact source

end
end SaturationMonoid.NavierStokes.NativeFullOrderRecovery
