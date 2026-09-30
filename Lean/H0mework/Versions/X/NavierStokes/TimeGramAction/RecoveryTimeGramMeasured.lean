import H0mework.Versions.X.NavierStokes.TimeGramAction.RecoveryTimeGramReadout

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryTimeGramMeasured

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryEscapeCarrier
open NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel NativeRecoveryTimeGramReadout
open NativeEndpointVelocityCarrier NativeCofinalStressPositivity NativeStressSource
open NativePairedCarrierJets NativeRecoveryPhysical NativePhysicalFourier NativeTimeJetCarrier

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem endpoint_component (time : Icc (0 : ℝ) 1) (wave : IntegerWavevector) (coordinate : Coordinate) :
    shiftedCLM wave coordinate (receipt.wholePath time) = shiftedComponent (endpoint receipt time) (wave, coordinate) := by
  change shifted (receipt.wholePath time) wave coordinate = shifted (wholeVelocity (endpoint receipt time)) wave coordinate
  rw [endpoint, wholeVelocity_puncturedEuclideanize _ (wholeMild_zero ledger receipt time)]

theorem source_stress_ae (stress : StressAt escape) (pointLe : point ≤ 1) :
    ∀ᵐ time ∂commonTimeMeasure 1,
      stressRead stress pointLe (.fixed time) = quadraticFlux (receipt.wholePath time) := by
  filter_upwards [(generated stress pointLe).fixedStrong] with time strong
  funext wave output input
  have component (shift : IntegerWavevector) (coordinate : Coordinate) :=
    (shiftedCLM shift coordinate).continuous.tendsto _ |>.comp strong
  have actual := (component wave output).inner (𝕜 := ℂ) (component 0 input)
  have selected := pairing_tendsto stress pointLe (.inr (.fixed time, wave, output)) (.inr (.fixed time, 0, input))
  have same : inner ℂ
      (NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (.fixed time, wave, output)))
      (NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (.fixed time, 0, input))) =
      inner ℂ (shiftedCLM wave output (receipt.wholePath time)) (shiftedCLM 0 input (receipt.wholePath time)) :=
    tendsto_nhds_unique selected actual
  rw [stressRead, same, endpoint_component, endpoint_component,
    shiftedComponent_inner _ (endpoint_reality time), NativeCofinalFluxPairing.bilinearFlux_diagonal,
    neg_neg, sub_zero, endpoint, wholeVelocity_puncturedEuclideanize _ (wholeMild_zero ledger receipt time)]

def forcing (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) 1) : ComplexCoordinateVector :=
  projectedDivergenceCLM wave (stressRead stress pointLe (.fixed time) wave)

theorem source_forcing_ae (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    forcing stress pointLe wave =ᵐ[commonTimeMeasure 1]
      wholeVelocityLerayProjectionSpaceTime wave (receipt.core.nonlinearLimit wave) := by
  filter_upwards [source_stress_ae stress pointLe,
    NativeRecoveryNonlinear.wholeMild_lerayLimit_eq_flux receipt wave] with time tensor original
  rw [forcing, tensor, original, projectedDivergenceCLM_apply]
  rfl

theorem forcing_memLp (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    MemLp (forcing stress pointLe wave) 1 (commonTimeMeasure 1) :=
  (Lp.memLp (wholeVelocityLerayProjectionSpaceTime wave (receipt.core.nonlinearLimit wave))).ae_eq
    (source_forcing_ae stress pointLe wave).symm

def forcingLp (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) : NonlinearRowSpaceTimeState 1 :=
  (forcing_memLp stress pointLe wave).toLp (forcing stress pointLe wave)

theorem source_forcingLp (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    forcingLp stress pointLe wave = wholeVelocityLerayProjectionSpaceTime wave (receipt.core.nonlinearLimit wave) := by
  apply Lp.ext
  exact (forcing_memLp stress pointLe wave).coeFn_toLp.trans (source_forcing_ae stress pointLe wave)

theorem source_mild_from_kernel (stress : StressAt escape) (pointLe : point ≤ 1)
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) (time : Icc (0 : ℝ) 1) :
    velocityRead stress pointLe (.fixed time) wave = fixedWaveHeatDuhamelValue 1 nu.coeff wave
      (wholeRestartVelocityEndpointCoefficient ledger.family.endpointReceipt.velocityEndpoint wave)
      (forcingLp stress pointLe wave) time := by
  have mean : velocityRead stress pointLe (.fixed time) wave = receipt.wholePath time wave :=
    funext fun coordinate => source_velocity stress pointLe (.fixed time) wave coordinate
  rw [mean, source_forcingLp]
  exact receipt.row_mild_identity wave nonzero time

end
end SaturationMonoid.NavierStokes.NativeRecoveryTimeGramMeasured
