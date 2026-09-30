import H0mework.NavierStokes.MomentumAction.ReceiptMomentumIntegral
import H0mework.NavierStokes.KineticRestart.KineticVelocityWholeCarrierMorphism

set_option autoImplicit false
open scoped ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeReceiptStrongVelocityWrite

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeEndpointVelocityCarrier NativeStressSource NativeOriginalMomentumIntegral NativeFullOrderTime

noncomputable section

def velocityActionCLM : ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState :=
  wholeVelocityCLM.comp ((wholeRestartKineticToVelocityCLM.comp puncturedEuclideanizeCLM).restrictScalars ℝ)

theorem velocityActionCLM_nonzero (state : ComplexVorticityHilbertState) (wave : NonzeroIntegerWavevector) :
    velocityActionCLM state wave.1 = biotSavartVelocityCoefficient wave.1
      ((Real.sqrt (integerWaveViscousMultiplier wave.1) : ℂ) • state wave.1) := by
  funext coordinate
  change wholeVelocity (wholeRestartKineticToVelocityCLM (puncturedEuclideanizeCLM state)) wave.1 coordinate = _
  rw [wholeVelocity_nonzero, wholeRestartKineticToVelocityCLM_apply, wholeRestartKineticToVelocityRowCLM_apply]
  rfl

theorem velocityActionCLM_zero (state : ComplexVorticityHilbertState) : velocityActionCLM state 0 = 0 :=
  wholeVelocity_zero _

variable {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}

def action (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (time : Icc (0 : ℝ) duration) : ComplexVorticityHilbertState :=
  velocityActionCLM (receipt.wholeTangent time)

theorem action_L2 (receipt : WholeContinuousMildSerrinReceipt nu initial duration) :
    MemLp (action receipt) 2 (commonTimeMeasure duration) :=
  (Lp.memLp receipt.wholeTangent).continuousLinearMap_comp velocityActionCLM

theorem action_integrable (receipt : WholeContinuousMildSerrinReceipt nu initial duration) :
    Integrable (action receipt) (commonTimeMeasure duration) :=
  (action_L2 receipt).integrable (by norm_num)

theorem action_row_ae (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (wave : IntegerWavevector) :
    ∀ᵐ time ∂commonTimeMeasure duration, action receipt time wave = receiptMomentumAction receipt wave time.1 := by
  by_cases zero : wave = 0
  · subst wave
    exact Eventually.of_forall fun time => by
      rw [action, velocityActionCLM_zero]
      simp [receiptMomentumAction, biotSavartVelocityCoefficient]
  · filter_upwards [receipt.rowTangent_eq_wholeTangent_ae wave zero,
      receipt.rowTangent_eq_unforced_ae wave zero, receipt.wholePath_eq_transverse_ae] with time weighted unforced same
    change velocityActionCLM (receipt.wholeTangent time) wave = _
    rw [velocityActionCLM_nonzero _ ⟨wave, zero⟩, weighted, unforced, ← same,
      ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityBilinearCoefficientAt_self]
    change biotSavartVelocityCoefficient wave
      (wholeLatticeVorticityFourierTangentAt nu.coeff (receipt.wholePath time) wave) =
      biotSavartVelocityCoefficient wave
        (wholeLatticeVorticityFourierTangentAt nu.coeff (receipt.wholePath (projIcc 0 duration receipt.requestedTimePos.le time.1)) wave)
    rw [projIcc_of_mem receipt.requestedTimePos.le time.2]

theorem original_row_integral (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (time : Icc (0 : ℝ) duration) (wave : IntegerWavevector) :
    (∫ sample in Iic time, receiptMomentumAction receipt wave sample.1 ∂commonTimeMeasure duration) =
      wholeBiotSavartVelocityState (receipt.wholePath time) wave - wholeBiotSavartVelocityState initial wave := by
  rw [commonTime_integral_Iic_eq_intervalIntegral duration receipt.requestedTimePos.le time]
  have original := receipt_primitive receipt wave time
  have same : (∫ actual in 0..time.1, momentumAt nu (receiptVelocity receipt actual) wave) =
      ∫ actual in 0..time.1, receiptMomentumAction receipt wave actual := by
    apply intervalIntegral.integral_congr
    intro actual inside
    rw [uIcc_of_le time.2.1] at inside
    exact receipt_action receipt wave ⟨actual, inside.1, inside.2.trans time.2.2⟩
  rw [same, receipt_row receipt wave time, receipt_row receipt wave ⟨0, le_rfl, receipt.requestedTimePos.le⟩,
    receipt_velocity_row_eq receipt wave time,
    receipt_velocity_row_eq receipt wave ⟨0, le_rfl, receipt.requestedTimePos.le⟩,
    receipt.wholePath_initial] at original
  exact original.symm

theorem source_integral (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (time : Icc (0 : ℝ) duration) :
    (∫ sample in Iic time, action receipt sample ∂commonTimeMeasure duration) =
      wholeBiotSavartVelocityState (receipt.wholePath time) - wholeBiotSavartVelocityState initial := by
  apply lp.ext
  funext wave
  have commutes := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).integral_comp_comm
    ((action_integrable receipt).restrict (s := Iic time))
  change (∫ sample in Iic time, action receipt sample wave ∂commonTimeMeasure duration) =
    (∫ sample in Iic time, action receipt sample ∂commonTimeMeasure duration) wave at commutes
  change (∫ sample in Iic time, action receipt sample ∂commonTimeMeasure duration) wave =
    wholeBiotSavartVelocityState (receipt.wholePath time) wave - wholeBiotSavartVelocityState initial wave
  rw [← commutes]
  calc
    _ = ∫ sample in Iic time, receiptMomentumAction receipt wave sample.1 ∂commonTimeMeasure duration := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (action_row_ae receipt wave)] with sample same
      exact same
    _ = _ := original_row_integral receipt time wave

end
end SaturationMonoid.NavierStokes.NativeReceiptStrongVelocityWrite
