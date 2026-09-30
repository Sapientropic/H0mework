import H0mework.NavierStokes.SourceAction.HilbertDiracCurrent
import H0mework.NavierStokes.RecoveryAction.RecoveryJointAction

set_option autoImplicit false
open scoped BigOperators Topology ComplexOrder

namespace SaturationMonoid.NavierStokes.NativeRecoveryPairedCarrier

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeRecoveryUnifiedCurrent NativeRecoveryAEWindows NativeRecoveryJointCurrent
open NativeRecoveryEscapeCarrier NativeRecoveryEscapeStress NativeEndpointVelocityCarrier
open NativeStressPairingCarrier NativeHilbertDiracCurrent NativeStressSource NativeCofinalFluxPairing

noncomputable section

variable {nu : Viscosity}

def mean (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) : WholeRestartVelocityEndpointState :=
  endpoint (receipt initial) (clock initial time)

theorem mean_velocity (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) :
    wholeVelocity (mean initial time) = NativeRecoveryUnifiedCurrent.velocity initial time.1 := by
  rw [velocity_read]
  exact NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _ (NativeRecoveryPhysical.wholeMild_zero _ _ _)

theorem source_covariance_positive (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) :
    (NativeStressPairingCarrier.covariance (mean initial time) (stress initial time)).PosSemidef := by
  by_cases regular : time.1 ∈ regularSet (receipt initial) (terminal initial)
  · rw [stress_regular initial time regular, ← mean_velocity]
    constructor
    · ext left right
      simp [NativeStressPairingCarrier.covariance]
    · intro coefficients
      simp [NativeStressPairingCarrier.covariance]
  · rw [stress_uncovered initial time regular]
    exact covariance_posSemidef (sourceStress initial time.1 time.2 regular) (clock initial time).2.2

def source (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) : Data where
  mean := mean initial time
  reality := endpoint_reality (clock initial time)
  stress := stress initial time
  positive := source_covariance_positive initial time

theorem source_stress_symmetric (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (wave : IntegerWavevector) (output input : Coordinate) :
    (source initial time).stress wave output input = (source initial time).stress wave input output := by
  change stress initial time wave output input = stress initial time wave input output
  by_cases regular : time.1 ∈ regularSet (receipt initial) (terminal initial)
  · rw [stress_regular initial time regular]
    exact quadraticFlux_symmetric _ wave output input
  · rw [stress_uncovered initial time regular]
    let generated := sourceStress initial time.1 time.2 regular
    have first := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp generated.stress_tendsto wave) output) input
    have second := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp generated.stress_tendsto wave) input) output
    apply tendsto_nhds_unique first
    apply second.congr'
    exact Eventually.of_forall fun index => quadraticFlux_symmetric _ wave input output

theorem source_current (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (direction : Fin 4) (wave : IntegerWavevector) :
    diracCurrent (source initial time) direction wave = current initial time direction wave := by
  rw [diracCurrent_eq _ direction wave (source_stress_symmetric initial time wave), pairedCurrent_eq]
  change NativePairedCurrentFourier.coefficient (wholeVelocity (mean initial time)) (stress initial time) direction wave = _
  rw [mean_velocity]
  rfl

theorem source_velocity (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    inner ℂ (background (source initial time) wave) (component (source initial time) (0, coordinate)) =
      NativeRecoveryUnifiedCurrent.velocity initial time.1 wave coordinate := by
  rw [background_component, sub_zero]
  change wholeVelocity (mean initial time) wave coordinate = _
  rw [mean_velocity]

theorem source_stress (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (wave : IntegerWavevector) (output input : Coordinate) :
    -inner ℂ (component (source initial time) (wave, output)) (component (source initial time) (0, input)) =
      stress initial time wave output input := by
  rw [component_inner, sub_zero, neg_neg]
  rfl

theorem source_energy_le (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) :
    (∑ coordinate : Coordinate, ‖component (source initial time) (0, coordinate)‖ ^ 2) ≤ budget initial := by
  rw [component_energy]
  change -(∑ coordinate : Coordinate, (stress initial time 0 coordinate coordinate).re) ≤ _
  by_cases regular : time.1 ∈ regularSet (receipt initial) (terminal initial)
  · rw [stress_regular initial time regular, ← mean_velocity]
    have trace := bilinearFlux_zero_trace (mean initial time) (source initial time).reality
    simp only [bilinearFlux_diagonal] at trace
    rw [trace, neg_neg]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (endpoint_norm_bound (clock initial time))
  · rw [stress_uncovered initial time regular]
    let escape := NativeRecoveryCoverage.sourceUncoveredAction initial time.1 time.2 regular
    let generated := sourceStress initial time.1 time.2 regular
    have converges := (tendsto_finsetSum Finset.univ (fun coordinate _ =>
      Complex.continuous_re.continuousAt.tendsto.comp
        (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp generated.stress_tendsto 0) coordinate) coordinate))).neg
    apply le_of_tendsto' converges
    intro index
    have trace := bilinearFlux_zero_trace (NativeRecoveryEscapeCarrier.velocity escape (generated.refinement index))
      (NativeRecoveryEscapeCarrier.velocity_reality escape (clock initial time).2.2 (generated.refinement index))
    simp only [bilinearFlux_diagonal] at trace
    change -(∑ coordinate : Coordinate,
      (quadraticFlux (wholeVelocity (NativeRecoveryEscapeCarrier.velocity escape (generated.refinement index))) 0 coordinate coordinate).re) ≤ _
    rw [trace, neg_neg]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (velocity_norm_bound escape (clock initial time).2.2 (generated.refinement index))

end
end SaturationMonoid.NavierStokes.NativeRecoveryPairedCarrier
