import H0mework.Versions.X.NavierStokes.StressWeakInput.OriginalInput
import H0mework.Versions.X.NavierStokes.StressResolvent.ResolventResidual
import H0mework.Versions.X.NavierStokes.StressAction.StressDynamicsBilinear
import H0mework.Versions.X.NavierStokes.StressAction.CompleteStressAction

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalStressAction

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeResolventCompactness NativeWholeResolventLimit NativeOriginalResolventInput NativeResolventEquation
open NativeEndpointVelocityCarrier NativeRecoveryTimeGramReadout NativeResolventResidual
open NativeRecoveryTimeBackgroundProjection
open NativeCompleteStressAction NativeCofinalFluxPairing NativeTimeJetCarrier
open NativeRawStressAction NativeCofinalStressPositivity

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def originalStress (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) :
    NativeCompleteStressCarrier.Space :=
  NativeCompleteStressCarrier.ofBound (stressRead stress pointLe node) (bound receipt ^ 2)
    (NativeRecoveryTimeGramForce.stress_bound stress pointLe node)

theorem rawStress_kernel (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (node : TimeNode) (wave : IntegerWavevector) (output input : Coordinate) :
    NativeCompleteStressCarrier.read
      (rawStress stress index (timeAt escape pointLe (stress.refinement index) node).1) wave output input =
      -gram escape pointLe (stress.refinement index) (.inr (node, wave, output)) (.inr (node, 0, input)) := by
  rw [rawStress, NativeCompleteStressBilinear.mixed_read, rawField_node]
  change bilinearFlux _ _ wave output input =
    -inner ℂ (shiftedComponent _ (wave, output)) (shiftedComponent _ (0, input))
  rw [shiftedComponent_inner _ (velocity_reality escape pointLe (stress.refinement index) node),
    sub_zero, neg_neg]

theorem rawStress_rows (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (output input : Coordinate) :
    Tendsto (fun index => NativeCompleteStressCarrier.read
      (rawStress stress index (timeAt escape pointLe (stress.refinement index) node).1) wave output input)
      ((generated stress pointLe).refinement : Filter ℕ)
      (𝓝 (NativeCompleteStressCarrier.read (originalStress stress pointLe node) wave output input)) := by
  simpa only [rawStress_kernel, originalStress, NativeCompleteStressCarrier.read_ofBound, stressRead]
    using (pairing_tendsto stress pointLe (.inr (node, wave, output)) (.inr (node, 0, input))).neg

def resolved (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) : State :=
  (operator stress pointLe node step positive (meanInput stress pointLe node)).1

def resolvedStress (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) : NativeCompleteStressCarrier.Space :=
  NativeCompleteStressBilinear.mixed (wholeVelocity (mean stress pointLe node))
    (wholeVelocity (resolved stress pointLe node step positive))

def retainedStress (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) : NativeCompleteStressCarrier.Space :=
  originalStress stress pointLe node - resolvedStress stress pointLe node step positive

theorem retainedStress_read (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) :
    NativeCompleteStressCarrier.read (retainedStress stress pointLe node step positive) =
      stressDifference stress pointLe node (resolved stress pointLe node step positive) := by
  funext wave output input
  change (NativeCompleteStressCarrier.readCLM wave output input)
    (originalStress stress pointLe node - resolvedStress stress pointLe node step positive) = _
  rw [map_sub, NativeCompleteStressCarrier.readCLM_apply, NativeCompleteStressCarrier.readCLM_apply,
    originalStress, NativeCompleteStressCarrier.read_ofBound, resolvedStress, NativeCompleteStressBilinear.mixed_read]
  rfl

theorem retainedStress_original (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (wave : IntegerWavevector) (output input : Coordinate) :
    NativeCompleteStressCarrier.read (retainedStress stress pointLe node step positive) wave output input =
      -inner ℂ (residual stress pointLe node wave output) (residual stress pointLe node 0 input) +
        bilinearFlux (mean stress pointLe node) (mean stress pointLe node -
          resolved stress pointLe node step positive) wave output input := by
  rw [retainedStress_read]
  exact difference_retains_original stress pointLe node _ wave output input

theorem resolved_momentum (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) :
    momentumCLM nu (WithLp.toLp 2
      (resolved stress pointLe node step positive, resolvedStress stress pointLe node step positive)) =
      NativeNegativeFourMomentum.embed (step⁻¹ •
        (resolved stress pointLe node step positive - mean stress pointLe node)) := by
  apply lp.ext
  funext wave
  have equation := NativeWholeResolventEquation.operator_equation stress pointLe node step positive
    (meanInput stress pointLe node) wave
  change wholeVelocity (resolved stress pointLe node step positive) wave.1 - step •
    (projectedDivergenceCLM wave.1 (bilinearFlux (mean stress pointLe node)
      (resolved stress pointLe node step positive) wave.1) -
      (nu.coeff * integerWaveViscousMultiplier wave.1) •
        wholeVelocity (resolved stress pointLe node step positive) wave.1) =
          wholeVelocity (mean stress pointLe node) wave.1 at equation
  have rate : projectedDivergenceCLM wave.1 (bilinearFlux (mean stress pointLe node)
      (resolved stress pointLe node step positive) wave.1) -
      (nu.coeff * integerWaveViscousMultiplier wave.1) •
        wholeVelocity (resolved stress pointLe node step positive) wave.1 =
      step⁻¹ • (wholeVelocity (resolved stress pointLe node step positive) wave.1 -
        wholeVelocity (mean stress pointLe node) wave.1) := by
    rw [← equation]
    simp only [sub_sub_cancel, inv_smul_smul₀ positive.ne']
  unfold resolvedStress NativeCompleteStressBilinear.mixed
  rw [momentumCLM_source]
  change NativeNegativeFourMomentum.weightedRowCLM wave.1
    (projectedDivergenceCLM wave.1 (bilinearFlux (mean stress pointLe node)
      (resolved stress pointLe node step positive) wave.1) -
      (nu.coeff * integerWaveViscousMultiplier wave.1) •
        wholeVelocity (resolved stress pointLe node step positive) wave.1) = _
  have transport : wholeVelocity (step⁻¹ •
      (resolved stress pointLe node step positive - mean stress pointLe node)) wave.1 =
      step⁻¹ • (wholeVelocity (resolved stress pointLe node step positive) wave.1 -
        wholeVelocity (mean stress pointLe node) wave.1) := by
    change wholeVelocityCLM (step⁻¹ •
      (resolved stress pointLe node step positive - mean stress pointLe node)) wave.1 = _
    rw [map_smul, map_sub]
    rfl
  rw [rate, ← transport]
  exact NativeNegativeFourMomentum.weightedRowCLM_row _ wave

/-- The complete original source keeps its residual under the actual resolved action. -/
theorem original_momentum (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) :
    momentumCLM nu (WithLp.toLp 2 (mean stress pointLe node, originalStress stress pointLe node)) =
      NativeNegativeFourMomentum.embed (step⁻¹ •
        (resolved stress pointLe node step positive - mean stress pointLe node)) +
      divergenceCLM (retainedStress stress pointLe node step positive) -
        viscousCLM nu (mean stress pointLe node - resolved stress pointLe node step positive) := by
  rw [← resolved_momentum]
  change divergenceCLM (originalStress stress pointLe node) - viscousCLM nu (mean stress pointLe node) =
    (divergenceCLM (resolvedStress stress pointLe node step positive) -
      viscousCLM nu (resolved stress pointLe node step positive)) +
      divergenceCLM (originalStress stress pointLe node - resolvedStress stress pointLe node step positive) -
        viscousCLM nu (mean stress pointLe node - resolved stress pointLe node step positive)
  rw [map_sub, map_sub]
  abel

end
end SaturationMonoid.NavierStokes.NativeOriginalStressAction
