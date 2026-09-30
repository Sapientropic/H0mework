import H0mework.NavierStokes.CofinalAction.CofinalMomentum
import H0mework.NavierStokes.RecoveryAction.RecoveryPhysical
import H0mework.NavierStokes.RecoveryAction.RecoveryRowAction

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeCofinalRecoveryAction

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPhysicalRightTrace
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointMacroCausalDuhamel
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearDuhamelRegeneration
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open NativeStressSource NativeCofinalStress NativeCofinalStressDefect NativeEndpointVelocityCarrier
open NativeTimeJetCarrier NativeHigherTimeJets NativeRecoveryPhysical NativeRecoveryRowAction
open NativeCofinalMomentumAction

noncomputable section

variable {nu : Viscosity}

def zeroTime : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩

def recoveryVelocity (initial : GeneratedWholeRestartCurrent nu) (time : Icc (0 : ℝ) 1) : ComplexVorticityHilbertState :=
  (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).wholePath time

theorem recoveryVelocity_right_tendsto (initial : GeneratedWholeRestartCurrent nu) :
    Tendsto (recoveryVelocity initial) (𝓝 zeroTime) (𝓝 (endpointVelocity initial)) := by
  have original := sourceGeneratedNativeTemporalWholeMildReadWrite_physical_tendsto_initial initial
  have mapped := wholeVelocityCLM.continuous.tendsto _ |>.comp original
  exact mapped.congr' (Eventually.of_forall fun time =>
    wholeVelocity_puncturedEuclideanize _
      (wholeMild_zero _ (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) time))

theorem recoveryStress_right_tendsto (initial : GeneratedWholeRestartCurrent nu) :
    Tendsto (fun time => quadraticFlux (recoveryVelocity initial time)) (𝓝 zeroTime)
      (𝓝 (quadraticFlux (endpointVelocity initial))) := by
  apply tendsto_pi_nhds.mpr
  intro wave
  apply tendsto_pi_nhds.mpr
  intro output
  apply tendsto_pi_nhds.mpr
  intro input
  have continuous : Continuous (fun state : ComplexVorticityHilbertState => mixedFluxCLM wave output input state state) :=
    (mixedFluxCLM wave output input).continuous.clm_apply continuous_id
  have source := continuous.tendsto _ |>.comp (recoveryVelocity_right_tendsto initial)
  simpa only [Function.comp_def, mixedFluxCLM_apply, mixedFlux_diagonal] using source

def recoveryMomentum (initial : GeneratedWholeRestartCurrent nu) (time : Icc (0 : ℝ) 1) : NativeFluidVorticityTangent :=
  fun wave => projectedDivergenceCLM wave (quadraticFlux (recoveryVelocity initial time) wave) -
    (nu.coeff * integerWaveViscousMultiplier wave) • recoveryVelocity initial time wave

theorem recoveryMomentum_eq_original (initial : GeneratedWholeRestartCurrent nu) (time : Icc (0 : ℝ) 1) (wave : IntegerWavevector) :
    recoveryMomentum initial time wave = rateRow (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) wave time.1 := by
  rw [rateRow, nonlinearRow, velocity_on_interval]
  rfl

theorem recoveryMomentum_right_tendsto (initial : GeneratedWholeRestartCurrent nu) :
    Tendsto (recoveryMomentum initial) (𝓝 zeroTime) (𝓝 (resolvedMomentum initial)) := by
  apply tendsto_pi_nhds.mpr
  intro wave
  have nonlinear := (projectedDivergenceCLM wave).continuous.tendsto _ |>.comp
    (tendsto_pi_nhds.mp (recoveryStress_right_tendsto initial) wave)
  have velocity := ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.tendsto _
    ).comp (recoveryVelocity_right_tendsto initial)
  exact nonlinear.sub (velocity.const_smul (nu.coeff * integerWaveViscousMultiplier wave))

theorem cofinal_recovery_action_jump (initial : GeneratedWholeRestartCurrent nu) :
    momentum (sourceGeneratedCofinalStress initial) - resolvedMomentum initial =
      internalMomentum (sourceGeneratedCofinalStress initial) := by
  rw [momentum_decomposition]
  abel

theorem source_generated_action_jump_tendsto (initial : GeneratedWholeRestartCurrent nu) :
    Tendsto (fun time => momentum (sourceGeneratedCofinalStress initial) - recoveryMomentum initial time)
      (𝓝 zeroTime) (𝓝 (internalMomentum (sourceGeneratedCofinalStress initial))) := by
  rw [← cofinal_recovery_action_jump]
  exact tendsto_const_nhds.sub (recoveryMomentum_right_tendsto initial)

theorem source_generated_original_action_jump_tendsto (initial : GeneratedWholeRestartCurrent nu) :
    Tendsto (fun time : Icc (0 : ℝ) 1 => momentum (sourceGeneratedCofinalStress initial) -
      fun wave => rateRow (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) wave time.1)
      (𝓝 zeroTime) (𝓝 (internalMomentum (sourceGeneratedCofinalStress initial))) := by
  simpa only [← recoveryMomentum_eq_original] using source_generated_action_jump_tendsto initial

theorem endpointVelocity_coefficient (initial : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) :
    endpointVelocity initial wave = wholeRestartVelocityEndpointCoefficient
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint wave := by
  by_cases zero : wave = 0
  · subst wave
    simp [endpointVelocity]
  · funext coordinate
    rw [endpointVelocity, wholeVelocity_nonzero _ ⟨wave, zero⟩, wholeRestartVelocityEndpointCoefficient_of_ne _ _ zero]

theorem recovery_nonlinear_integrable (initial : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) :
    IntervalIntegrable (nonlinearRow (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) wave) volume 0 1 := by
  apply (inheritedForcing_integrable (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) wave).congr_ae
  rw [uIoc_of_le zero_le_one]
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  filter_upwards [inheritedForcing_eq_source_ae (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) wave]
    with time same inside
  exact same ⟨inside.1.le, inside.2⟩

def stressTransition (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) : NativeFluidStressFourierState :=
  quadraticFlux (velocity (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) actual) -
    (sourceGeneratedCofinalStress initial).stress

theorem stressTransition_action (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (wave : IntegerWavevector) :
    projectedDivergenceCLM wave (stressTransition initial actual wave) =
      nonlinearRow (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) wave actual -
        projectedDivergenceCLM wave ((sourceGeneratedCofinalStress initial).stress wave) := by
  change projectedDivergenceCLM wave (_ - _) = _
  rw [map_sub]
  rfl

def cofinalImpulse (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  ∫ earlier in (0 : ℝ)..time, Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) * (time - earlier)) •
    projectedDivergenceCLM wave ((sourceGeneratedCofinalStress initial).stress wave)

def transitionImpulse (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  ∫ earlier in (0 : ℝ)..time, Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) * (time - earlier)) •
    projectedDivergenceCLM wave (stressTransition initial earlier wave)

theorem recovery_nonlinear_impulse (initial : GeneratedWholeRestartCurrent nu) (time : Icc (0 : ℝ) 1)
    (wave : IntegerWavevector) :
    (∫ earlier in (0 : ℝ)..time.1, Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) * (time.1 - earlier)) •
      nonlinearRow (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) wave earlier) =
        cofinalImpulse initial time.1 wave + transitionImpulse initial time.1 wave := by
  have paid := (recovery_nonlinear_integrable initial wave).mono_set
    (show uIcc (0 : ℝ) time.1 ⊆ uIcc (0 : ℝ) 1 by
      rw [uIcc_of_le time.2.1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl time.2.2)
  have constantPaid : IntervalIntegrable (fun earlier => Real.exp
      (-(nu.coeff * integerWaveViscousMultiplier wave) * (time.1 - earlier)) •
        projectedDivergenceCLM wave ((sourceGeneratedCofinalStress initial).stress wave)) volume 0 time.1 :=
    (by fun_prop : Continuous _).intervalIntegrable 0 time.1
  have transitionPaid : IntervalIntegrable (fun earlier => Real.exp
      (-(nu.coeff * integerWaveViscousMultiplier wave) * (time.1 - earlier)) •
        projectedDivergenceCLM wave (stressTransition initial earlier wave)) volume 0 time.1 := by
    simp_rw [stressTransition_action]
    exact (paid.sub intervalIntegrable_const).continuousOn_smul (by fun_prop)
  rw [cofinalImpulse, transitionImpulse, ← intervalIntegral.integral_add constantPaid transitionPaid]
  apply intervalIntegral.integral_congr
  intro earlier _
  dsimp only
  rw [stressTransition_action, smul_sub]
  abel

theorem recovery_Duhamel_from_cofinal_stress (initial : GeneratedWholeRestartCurrent nu)
    (time : Icc (0 : ℝ) 1) (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    recoveryVelocity initial time wave =
      Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) * time.1) • endpointVelocity initial wave +
        cofinalImpulse initial time.1 wave + transitionImpulse initial time.1 wave := by
  let receipt := sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial
  have original := rowExtension_on_interval receipt wave nonzero time
  rw [rowExtension, heatDuhamelComplexCoordinatePath_eq_heat_add_integral, sub_zero] at original
  have forcingSame : (∫ earlier in (0 : ℝ)..time.1,
      Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) * (time.1 - earlier)) • inheritedForcing receipt wave earlier) =
      ∫ earlier in (0 : ℝ)..time.1,
        Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) * (time.1 - earlier)) • nonlinearRow receipt wave earlier := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [inheritedForcing_eq_source_ae receipt wave] with earlier same inside
    rw [uIoc_of_le time.2.1] at inside
    rw [same ⟨inside.1.le, inside.2.trans time.2.2⟩]
  rw [forcingSame, velocity_on_interval receipt time] at original
  change _ = recoveryVelocity initial time wave at original
  rw [← original, endpointVelocity_coefficient, recovery_nonlinear_impulse initial time wave, ← add_assoc]
  rfl

theorem next_initial_Duhamel_from_cofinal_stress (initial : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    biotSavartVelocityCoefficient wave ((sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).initialState wave) =
      Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) * (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) •
        endpointVelocity initial wave + cofinalImpulse initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 wave +
        transitionImpulse initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 wave := by
  rw [(sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent_sameEvent initial).2.2 wave]
  exact recovery_Duhamel_from_cofinal_stress initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time wave nonzero

theorem next_whole_Duhamel_from_cofinal_stress (initial : GeneratedWholeRestartCurrent nu)
    (time : Icc (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).duration)
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    biotSavartVelocityCoefficient wave
      ((sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).receipt.wholePath time wave) =
      finiteStateVorticityHeatMultiplier nu.coeff time.1 wave •
        (Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) * (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) •
          endpointVelocity initial wave + cofinalImpulse initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 wave +
          transitionImpulse initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 wave) +
        biotSavartVelocityCoefficient wave (receiptWeightedNonlinearDuhamelAt
          (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).receipt wave nonzero time) := by
  have write := congrArg (biotSavartVelocityCLM wave)
    (wholeContinuousMildSerrinReceipt_row_sub_heat_eq
      (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).receipt wave nonzero time)
  rw [map_sub, map_smul] at write
  simp only [biotSavartVelocityCLM_apply] at write
  rw [next_initial_Duhamel_from_cofinal_stress initial wave nonzero] at write
  exact (eq_add_of_sub_eq write).trans (add_comm _ _)

theorem nativeLaw_next_Duhamel_from_cofinal_stress
    {initial : GeneratedWholeRestartCurrent nu} {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry)
    (modes : Finset IntegerWavevector) (wave : IntegerWavevector) (nonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) law.recovery.next.duration) :
    (if wave ∈ modes then biotSavartVelocityCoefficient wave (law.recovery.next.receipt.wholePath time wave) else 0) =
      (if wave ∈ modes then finiteStateVorticityHeatMultiplier nu.coeff time.1 wave •
        (Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) * (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) •
          endpointVelocity initial wave + cofinalImpulse initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 wave +
          transitionImpulse initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 wave) else 0) +
      biotSavartVelocityCoefficient wave
        (resolvedReceiptWeightedNonlinearDuhamelAt law.recovery.next.receipt modes wave time +
          nativeTurbulenceWeightedDuhamelAt law.recovery.next.receipt modes wave time) := by
  have initialWrite : biotSavartVelocityCoefficient wave (law.recovery.next.initialState wave) =
      Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) * (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) •
        endpointVelocity initial wave + cofinalImpulse initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 wave +
        transitionImpulse initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 wave := by
    rw [law.recoveryPhysicalEvolution.2.2 wave]
    exact recovery_Duhamel_from_cofinal_stress initial (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time wave nonzero
  have write := congrArg (biotSavartVelocityCLM wave) (law.recoveryNextDuhamelEvolution modes wave nonzero time)
  by_cases inside : wave ∈ modes
  · rw [if_pos inside, map_sub, map_smul] at write
    simp only [biotSavartVelocityCLM_apply] at write
    rw [initialWrite] at write
    simp only [if_pos inside]
    exact (eq_add_of_sub_eq write).trans (add_comm _ _)
  · rw [if_neg inside, map_zero] at write
    simpa only [if_neg inside, zero_add, biotSavartVelocityCLM_apply] using write

end
end SaturationMonoid.NavierStokes.NativeCofinalRecoveryAction
