import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryUnifiedCurrent
import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryMixed

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryCurrentAction

open Set Filter MeasureTheory UnitAddTorus
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.Stage9CU.Fluid.CurrentReadout
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open NativeRecoveryUnifiedCurrent NativeRecoveryAEWindows NativeHigherTimeJets
open NativeRecoveryMixedWindow NativeFullOrderSynthesis
open NativePairedCurrentFourier (coefficient trace)
open NativeCofinalRecoveryAction (zeroTime recoveryVelocity)
open NativeFluidSpatialOperators (slice)

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {nu : Viscosity}

def momentum (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) : ComplexVorticityHilbertState :=
  NativeRecoveryStrongWindow.rate (receipt initial) actual

theorem momentum_row (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) (wave : IntegerWavevector) :
    momentum initial actual wave = NativeRecoveryRowAction.rateRow (receipt initial) wave actual := by
  obtain ⟨lower, window, inside⟩ := regular_window initial actual member
  exact window.rate_row actual ⟨inside.1.le, inside.2.le⟩ wave

theorem velocity_hasDerivAt (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) :
    HasDerivAt (velocity initial) (momentum initial actual) actual := by
  obtain ⟨lower, window, inside⟩ := regular_window initial actual member
  exact (window.velocity_hasDerivWithinAt actual ⟨inside.1.le, inside.2.le⟩).hasDerivAt (Icc_mem_nhds inside.1 inside.2)

theorem field_hasDerivAt (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) (space : PhysicalSpace) :
    HasDerivAt (fun sample => field initial (slice sample space)) (spatialField (momentum initial actual) space) actual := by
  obtain ⟨lower, window, inside⟩ := regular_window initial actual member
  simp only [field_on_slice]
  have original := (spatialWord_hasDerivWithinAt window 0 (fun direction => Fin.elim0 direction) space actual
    ⟨inside.1.le, inside.2.le⟩).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
  unfold spatialWord physicalRateWord at original
  simp only [iteratedFDeriv_zero_apply] at original
  change HasDerivAt (fun sample => spatialField (velocity initial sample) space)
    (spatialField (momentum initial actual) space) actual at original
  exact original

theorem spatial_current_hasDerivAt (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) (space : PhysicalSpace) (direction : Fin 3) :
    HasDerivAt (fun sample => current (matter initial) (dual initial) direction.succ (slice sample space))
      (spatialField (momentum initial actual) space direction) actual := by
  rw [spatial_read]
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) direction).hasFDerivAt.comp_hasDerivAt actual
    (field_hasDerivAt initial actual member space)

theorem temporal_current_hasDerivAt (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) (space : PhysicalSpace) :
    HasDerivAt (fun sample => current (matter initial) (dual initial) 0 (slice sample space))
      (inner ℝ (field initial (slice actual space)) (spatialField (momentum initial actual) space) / 4) actual := by
  rw [temporal_read]
  convert! ((field_hasDerivAt initial actual member space).norm_sq.div_const 8).const_add 2 using 1
  ring

def physicalCoefficient (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  mFourierCoeff (fun point => (NativePairedCurrentFourier.field (velocity initial actual) direction point : ℂ)) wave

theorem physicalCoefficient_eq (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 4) (wave : IntegerWavevector) :
    physicalCoefficient initial actual direction wave =
      coefficient (velocity initial actual) (NativeStressSource.quadraticFlux (velocity initial actual)) direction wave :=
  NativePairedCurrentFourier.current_fourier _ (velocity_reality initial actual) direction wave

theorem controlled_current_coefficient (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) (direction : Fin 4) (wave : IntegerWavevector) :
    mFourierCoeff (fun point => (continuousCurrent initial actual direction point : ℂ)) wave = physicalCoefficient initial actual direction wave := by
  rw [controlled_current_fourier initial actual member, physicalCoefficient_eq]

theorem temporal_response (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (wave : IntegerWavevector) :
    physicalCoefficient initial actual 0 wave - NativeCofinalPairedCurrent.source initial 0 wave =
      -trace (NativeCofinalRecoveryAction.stressTransition initial actual) wave / 8 := by
  rw [physicalCoefficient_eq]
  change (NativePairedCurrentFourier.baseline wave - trace (NativeStressSource.quadraticFlux (velocity initial actual)) wave / 8) -
    (NativePairedCurrentFourier.baseline wave - trace (NativeCofinalStress.sourceGeneratedCofinalStress initial).stress wave / 8) = _
  simp only [NativeCofinalRecoveryAction.stressTransition, trace, Pi.sub_apply, Finset.sum_sub_distrib]
  dsimp only [velocity, receipt]
  ring

theorem current_right_tendsto (initial : GeneratedWholeRestartCurrent nu) (direction : Fin 4) (wave : IntegerWavevector) :
    Tendsto (fun time : Icc (0 : ℝ) 1 => physicalCoefficient initial time.1 direction wave)
      (𝓝 zeroTime) (𝓝 (coefficient (NativeCofinalMomentumAction.endpointVelocity initial)
        (NativeStressSource.quadraticFlux (NativeCofinalMomentumAction.endpointVelocity initial)) direction wave)) := by
  have rows : Tendsto (fun time => fun wave => recoveryVelocity initial time wave) (𝓝 zeroTime)
      (𝓝 (fun wave => NativeCofinalMomentumAction.endpointVelocity initial wave)) := by
    apply tendsto_pi_nhds.mpr
    intro wave
    exact ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.tendsto _).comp
      (NativeCofinalRecoveryAction.recoveryVelocity_right_tendsto initial)
  have joint := rows.prodMk_nhds (NativeCofinalRecoveryAction.recoveryStress_right_tendsto initial)
  have original := (NativeCofinalPairedCurrent.coefficient_continuous direction wave).tendsto _ |>.comp joint
  apply original.congr'
  apply Eventually.of_forall
  intro time
  change coefficient (fun frequency => recoveryVelocity initial time frequency)
    (NativeStressSource.quadraticFlux (recoveryVelocity initial time)) direction wave = physicalCoefficient initial time.1 direction wave
  rw [physicalCoefficient_eq]
  have same : velocity initial time.1 = recoveryVelocity initial time := NativeRecoveryRowAction.velocity_on_interval (receipt initial) time
  rw [same]

theorem generated_next_initial_velocity (initial : GeneratedWholeRestartCurrent nu) :
    velocity initial (terminal initial) = wholeBiotSavartVelocityState (NativeCofinalUnifiedField.target initial).initialState := by
  apply lp.ext
  funext wave
  change NativeRecoveryRowAction.velocity (receipt initial) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 wave = _
  rw [NativeRecoveryRowAction.velocity_on_interval]
  exact ((sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent_sameEvent initial).2.2 wave).symm

theorem generated_next_initial_current (initial : GeneratedWholeRestartCurrent nu) (direction : Fin 4) (wave : IntegerWavevector) :
    physicalCoefficient initial (terminal initial) direction wave =
      mFourierCoeff (fun point => (NativePairedCurrentFourier.field
        (wholeBiotSavartVelocityState (NativeCofinalUnifiedField.target initial).initialState) direction point : ℂ)) wave := by
  rw [physicalCoefficient, generated_next_initial_velocity]

end
end SaturationMonoid.NavierStokes.NativeRecoveryCurrentAction
