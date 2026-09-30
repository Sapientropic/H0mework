import H0mework.NavierStokes.StressWeakInput.OriginalInput
import H0mework.NavierStokes.RecoveryAction.RecoveryTimeStrongRefinement
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeCriticalSerrin

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeWholeH1OriginalSource

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw
open NativeOriginalResolventInput NativeResolventCompactness NativeEndpointVelocityCarrier

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem meanInput_curl_summable_ae (source : StressAt escape) (pointLe : point ≤ 1) :
    ∀ᵐ time ∂commonTimeMeasure 1, Summable (curlDensity (meanInput source pointLe (.fixed time)).1) := by
  have generated := wholePointwiseGradientDensity_ae_summable
    1 receipt.core.stateLimit receipt.core.gradient_summable
  filter_upwards [generated, receipt.stateLimit_ae] with time gradient same
  have path : Summable (fun wave => integerWaveNormSq wave *
      complexCoordinateAmplitudeSq (receipt.wholePath time wave)) := by
    rw [same]
    exact gradient
  have physical := (path.mul_left ((2 * Real.pi) ^ 2)).subtype (fun wave => wave ≠ 0)
  apply physical.congr
  intro wave
  change (2 * Real.pi) ^ 2 * (integerWaveNormSq wave.1 *
      complexCoordinateAmplitudeSq (receipt.wholePath time wave.1)) =
    integerWaveViscousMultiplier wave.1 * ‖puncturedEuclideanize (receipt.wholePath time) wave‖ ^ 2
  rw [puncturedEuclideanize_apply, euclideanCoordinateRow_norm_sq, integerWaveViscousMultiplier]
  ring

/-- The existing source-selected sequence, with its original physical L² norm. -/
theorem originalInput_strong_ae (source : StressAt escape) (pointLe : point ≤ 1) :
    ∀ᵐ time ∂commonTimeMeasure 1, Tendsto
      (fun n => originalInput source pointLe
        ((NativeRecoveryTimeStrongRefinement.generated source pointLe).index n) (.fixed time))
      atTop (𝓝 (meanInput source pointLe (.fixed time))) := by
  filter_upwards [(NativeRecoveryTimeStrongRefinement.generated source pointLe).converges] with time strong
  have physical := (puncturedEuclideanizeCLM.restrictScalars ℝ).continuous.tendsto _ |>.comp strong
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n => puncturedEuclideanize (wholeVelocity
      (originalInput source pointLe ((NativeRecoveryTimeStrongRefinement.generated source pointLe).index n)
        (.fixed time)).1)) atTop (𝓝 (meanInput source pointLe (.fixed time)).1) at physical
  apply physical.congr'
  apply Eventually.of_forall
  intro n
  apply lp.ext
  funext wave
  rw [puncturedEuclideanize_apply]
  apply PiLp.ext
  intro coordinate
  exact wholeVelocity_nonzero _ wave coordinate

end
end SaturationMonoid.NavierStokes.NativeWholeH1OriginalSource
