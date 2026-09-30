import H0mework.Versions.X.NavierStokes.CofinalAction.CofinalUnifiedField

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeCofinalUnifiedAction

open Set
open PhysicsCore.ProofFreeRicherAnholonomicSource
open PhysicsCore.Stage9CU.Fluid.CurrentReadout
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearDuhamelRegeneration
open NativeFullOrderSynthesis NativeStressSource NativeCofinalUnifiedField
open NativeFluidSpatialOperators (slice)

noncomputable section

variable {nu : Viscosity}

def velocity (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) : ComplexVorticityHilbertState :=
  NativeReceiptSpacetime.velocity (receipt initial) actual

def momentum (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) : ComplexVorticityHilbertState :=
  NativeReceiptSpacetime.timeJet (window initial) 1 actual

def inletVelocity (initial : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  biotSavartVelocityCoefficient wave ((target initial).contact.physicalState wave)

theorem inlet_from_cofinal (initial : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    inletVelocity initial wave =
      finiteStateVorticityHeatMultiplier nu.coeff (target initial).contact.time.1 wave •
        (Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) *
          (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) • NativeCofinalMomentumAction.endpointVelocity initial wave +
          NativeCofinalRecoveryAction.cofinalImpulse initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 wave +
          NativeCofinalRecoveryAction.transitionImpulse initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 wave) +
        biotSavartVelocityCoefficient wave (receiptWeightedNonlinearDuhamelAt
          (target initial).receipt wave nonzero (target initial).contact.time) :=
  NativeCofinalRecoveryAction.next_whole_Duhamel_from_cofinal_stress initial (target initial).contact.time wave nonzero

theorem velocity_write (initial : GeneratedWholeRestartCurrent nu)
    (time : Icc (0 : ℝ) (wholeRestartDuration (target initial).contact))
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    velocity initial time.1 wave = finiteStateVorticityHeatMultiplier nu.coeff time.1 wave • inletVelocity initial wave +
      biotSavartVelocityCoefficient wave (receiptWeightedNonlinearDuhamelAt (receipt initial) wave nonzero time) := by
  have written := congrArg (biotSavartVelocityCLM wave)
    (wholeContinuousMildSerrinReceipt_row_sub_heat_eq (receipt initial) wave nonzero time)
  rw [map_sub, map_smul] at written
  simp only [biotSavartVelocityCLM_apply] at written
  rw [velocity, NativeReceiptSpacetime.velocity, NativeReceiptSpacetime.state_on_interval (receipt initial) time]
  exact (eq_add_of_sub_eq written).trans (add_comm _ _)

theorem velocity_from_cofinal (initial : GeneratedWholeRestartCurrent nu)
    (time : Icc (0 : ℝ) (wholeRestartDuration (target initial).contact))
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    velocity initial time.1 wave = finiteStateVorticityHeatMultiplier nu.coeff time.1 wave •
      (finiteStateVorticityHeatMultiplier nu.coeff (target initial).contact.time.1 wave •
        (Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) *
          (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) • NativeCofinalMomentumAction.endpointVelocity initial wave +
          NativeCofinalRecoveryAction.cofinalImpulse initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 wave +
          NativeCofinalRecoveryAction.transitionImpulse initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 wave) +
        biotSavartVelocityCoefficient wave (receiptWeightedNonlinearDuhamelAt
          (target initial).receipt wave nonzero (target initial).contact.time)) +
      biotSavartVelocityCoefficient wave (receiptWeightedNonlinearDuhamelAt (receipt initial) wave nonzero time) := by
  rw [velocity_write initial time wave nonzero, inlet_from_cofinal initial wave nonzero]

theorem field_velocity (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (space : PhysicalSpace) :
    field initial (slice actual space) = spatialField (velocity initial actual) space := field_on_slice initial actual space

theorem field_hasDerivWithinAt (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) (space : PhysicalSpace) :
    HasDerivWithinAt (fun sample => field initial (slice sample space)) (spatialField (momentum initial actual) space)
      (Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) actual := by
  simp only [field_velocity]
  exact NativeTimeChartPhysicalAction.receipt_physical_hasDerivWithinAt (window initial) actual inside space

theorem spatial_current_hasDerivWithinAt (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) (space : PhysicalSpace) (direction : Fin 3) :
    HasDerivWithinAt (fun sample => current (matter initial) (dual initial) direction.succ (slice sample space))
      (spatialField (momentum initial actual) space direction)
      (Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) actual := by
  rw [spatial_read]
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) direction).hasFDerivAt.comp_hasDerivWithinAt actual
    (field_hasDerivWithinAt initial actual inside space)

theorem temporal_current_hasDerivWithinAt (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) (space : PhysicalSpace) :
    HasDerivWithinAt (fun sample => current (matter initial) (dual initial) 0 (slice sample space))
      (inner ℝ (field initial (slice actual space)) (spatialField (momentum initial actual) space) / 4)
      (Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) actual := by
  rw [temporal_read]
  convert! ((field_hasDerivWithinAt initial actual inside space).norm_sq.div_const 8).const_add 2 using 1
  ring

theorem momentum_row (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) (wave : IntegerWavevector) :
    momentum initial actual wave = receiptMomentumAction (receipt initial) wave actual :=
  NativeReceiptSpacetime.timeJet_one_row (window initial) actual inside wave

end
end SaturationMonoid.NavierStokes.NativeCofinalUnifiedAction
