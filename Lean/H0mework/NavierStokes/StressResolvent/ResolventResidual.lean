import H0mework.NavierStokes.StressResolvent.ResolventEquation
import H0mework.NavierStokes.FullOrder.RecoveryTimeBackgroundProjection
import H0mework.NavierStokes.TimeGramAction.RecoveryTimeGramForce

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeResolventResidual

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeResolventCompactness NativeSourceResolvent NativeResolventEquation
open NativeEndpointVelocityCarrier NativeCofinalFluxPairing NativeTimeJetCarrier
open NativeRecoveryTimeGramReadout NativeRecoveryTimeBackgroundProjection

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def stressDifference (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) (target : State) :
    NativeFluidStressFourierState :=
  stressRead stress pointLe node - bilinearFlux (mean stress pointLe node) target

theorem difference_retains_original (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (target : State) (wave : IntegerWavevector) (output input : Coordinate) :
    stressDifference stress pointLe node target wave output input =
      -inner ℂ (residual stress pointLe node wave output) (residual stress pointLe node 0 input) +
        bilinearFlux (mean stress pointLe node) (mean stress pointLe node - target) wave output input := by
  have original := residual_stress stress pointLe node (wave, output) (0, input)
  have read : wholeVelocity (mean stress pointLe node) = receipt.wholePath (physicalTime escape pointLe node) :=
    NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _
      (NativeRecoveryPhysical.wholeMild_zero ledger receipt _)
  rw [sub_zero, ← read, ← bilinearFlux_diagonal] at original
  change stressRead stress pointLe node wave output input -
    bilinearFlux (mean stress pointLe node) target wave output input = _
  rw [bilinearFlux_sub_right]
  linear_combination original

theorem momentum_difference (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (target : State) (wave : IntegerWavevector) :
    NativeRecoveryTimeGramForce.momentum stress pointLe node wave =
      (projectedDivergenceCLM wave (bilinearFlux (mean stress pointLe node) target wave) -
        (nu.coeff * integerWaveViscousMultiplier wave) • wholeVelocity target wave) +
      projectedDivergenceCLM wave (stressDifference stress pointLe node target wave) -
        (nu.coeff * integerWaveViscousMultiplier wave) •
          (wholeVelocity (mean stress pointLe node) wave - wholeVelocity target wave) := by
  have read : velocityRead stress pointLe node wave = wholeVelocity (mean stress pointLe node) wave := by
    rw [mean, NativeRecoveryEscapeCarrier.endpoint,
      NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _
        (NativeRecoveryPhysical.wholeMild_zero ledger receipt _)]
    exact funext (source_velocity stress pointLe node wave)
  rw [NativeRecoveryTimeGramForce.momentum, read]
  change _ = _ + projectedDivergenceCLM wave (stressRead stress pointLe node wave -
    bilinearFlux (mean stress pointLe node) target wave) - _
  rw [map_sub, smul_sub]
  abel

theorem source_stress_write (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) :
    ∃ target : State,
      Tendsto (fun index => NativeSourceResolvent.endpoint stress pointLe index node step positive.le)
        ((generated stress pointLe).refinement : Filter ℕ) (𝓝 target) ∧
      Summable (curlDensity target) ∧ (∑' wave, curlDensity target wave) ≤
        ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 / (2 * step * nu.coeff) ∧
      ∀ wave : Wave, NativeRecoveryTimeGramForce.momentum stress pointLe node wave.1 =
        step⁻¹ • (wholeVelocity target wave.1 - wholeVelocity (mean stress pointLe node) wave.1) +
        projectedDivergenceCLM wave.1 (stressDifference stress pointLe node target wave.1) -
          (nu.coeff * integerWaveViscousMultiplier wave.1) •
            (wholeVelocity (mean stress pointLe node) wave.1 - wholeVelocity target wave.1) := by
  obtain ⟨target, strong, paid, bounded, equation⟩ := source_equation_generated stress pointLe node step positive
  refine ⟨target, strong, paid, bounded, ?_⟩
  intro wave
  have actual := equation wave
  let rate := projectedDivergenceCLM wave.1 (bilinearFlux (mean stress pointLe node) target wave.1) -
    (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity target wave.1
  have difference : wholeVelocity target wave.1 - wholeVelocity (mean stress pointLe node) wave.1 = step • rate := by
    rw [← actual]
    abel
  have slope : step⁻¹ • (wholeVelocity target wave.1 - wholeVelocity (mean stress pointLe node) wave.1) = rate := by
    rw [difference, inv_smul_smul₀ positive.ne']
  rw [slope]
  exact momentum_difference stress pointLe node target wave.1

end
end SaturationMonoid.NavierStokes.NativeResolventResidual
