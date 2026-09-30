import H0mework.NavierStokes.StressEvolution.ZeroStepLimit

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeWholeResolventZeroStress

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw
open NativeOriginalResolventInput NativeOriginalStressAction NativeResolventEquation NativeEndpointVelocityCarrier
open NativeCompleteStressBilinear NativeWholeResolventZeroLimit NativeWholeResolventZeroAction

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem source_velocity (source : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℕ → ℝ) (positive : ∀ index, 0 < step index) (vanishes : Tendsto step atTop (𝓝 0)) :
    Tendsto (fun index => resolved source pointLe node (step index) (positive index))
      atTop (𝓝 (mean source pointLe node)) :=
  tendsto_subtype_rng.mp (operator_recovers_input source pointLe node step positive vanishes (meanInput source pointLe node))

theorem source_stress (source : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℕ → ℝ) (positive : ∀ index, 0 < step index) (vanishes : Tendsto step atTop (𝓝 0)) :
    Tendsto (fun index => resolvedStress source pointLe node (step index) (positive index)) atTop
      (𝓝 (mixed (wholeVelocity (mean source pointLe node)) (wholeVelocity (mean source pointLe node)))) := by
  have read := wholeVelocityCLM.continuous.tendsto _ |>.comp (source_velocity source pointLe node step positive vanishes)
  exact (mixedCLM (wholeVelocity (mean source pointLe node))).continuous.tendsto _ |>.comp read

theorem complete_residual (source : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℕ → ℝ) (positive : ∀ index, 0 < step index) (vanishes : Tendsto step atTop (𝓝 0)) :
    Tendsto (fun index => retainedStress source pointLe node (step index) (positive index)) atTop
      (𝓝 (originalStress source pointLe node -
        mixed (wholeVelocity (mean source pointLe node)) (wholeVelocity (mean source pointLe node)))) :=
  tendsto_const_nhds.sub (source_stress source pointLe node step positive vanishes)

theorem complete_residual_read (source : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (output input : Coordinate) :
    NativeCompleteStressCarrier.read (originalStress source pointLe node -
      mixed (wholeVelocity (mean source pointLe node)) (wholeVelocity (mean source pointLe node))) wave output input =
      -inner ℂ (NativeRecoveryTimeBackgroundProjection.residual source pointLe node wave output)
        (NativeRecoveryTimeBackgroundProjection.residual source pointLe node 0 input) := by
  change (NativeCompleteStressCarrier.readCLM wave output input) (_ - _) = _
  rw [map_sub, NativeCompleteStressCarrier.readCLM_apply, NativeCompleteStressCarrier.readCLM_apply, mixed_read]
  rw [originalStress, NativeCompleteStressCarrier.read_ofBound]
  have residual := NativeResolventResidual.difference_retains_original source pointLe node
    (mean source pointLe node) wave output input
  have zero : wholeVelocity (0 : NativeResolventCompactness.State) = 0 := wholeVelocityCLM.map_zero
  simpa only [NativeResolventResidual.stressDifference, Pi.sub_apply,
    NativeCofinalFluxPairing.bilinearFlux, NativeHigherTimeJets.mixedFlux,
    sub_self, zero, lp.coeFn_zero, Pi.zero_apply, mul_zero, tsum_zero, neg_zero, add_zero] using residual

end
end SaturationMonoid.NavierStokes.NativeWholeResolventZeroStress
