import H0mework.Versions.X.NavierStokes.NativeAction.Evolution

set_option autoImplicit false
open scoped ContDiff BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeCompleteActionOperator

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open SourceGeneratedNativeResponseDisposition NativeCompleteStressAction NativeEndpointVelocityCarrier
open NativeTimeJetCarrier
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator

noncomputable section

private theorem stress_read_row (value : NativeCompleteStressCarrier.Space) (wave : NonzeroIntegerWavevector) :
    NativeCompleteStressCarrier.read value wave.1 =
      integerWaveNormSq wave.1 • NativeCompleteStressCarrier.untensor (value wave.1) := by
  funext output input
  change (NativeCompleteStressCarrier.weight wave.1)⁻¹ • value wave.1 (output, input) =
    integerWaveNormSq wave.1 • value wave.1 (output, input)
  rw [NativeCompleteStressCarrier.weight, if_neg wave.2, inv_inv]

theorem divergence_complete_row (value : NativeCompleteStressCarrier.Space) (wave : NonzeroIntegerWavevector) :
    divergenceCLM value wave = NativeNegativeFourMomentum.weightedRowCLM wave.1
      (projectedDivergenceCLM wave.1 (NativeCompleteStressCarrier.read value wave.1)) := by
  change rowCLM wave (value wave.1) = _
  rw [stress_read_row, map_smul, map_smul]
  change (integerWaveNormSq wave.1)⁻¹ • euclideanCoordinateRow
    (projectedDivergenceCLM wave.1 (NativeCompleteStressCarrier.untensor (value wave.1))) =
      integerWaveNormSq wave.1 • (NativeNegativeFourMomentum.weight wave.1 • euclideanCoordinateRow
        (projectedDivergenceCLM wave.1 (NativeCompleteStressCarrier.untensor (value wave.1))))
  rw [smul_smul]
  congr 1
  unfold NativeNegativeFourMomentum.weight
  field_simp

theorem momentum_complete_row (nu : Viscosity) (value : FullSpace) (wave : NonzeroIntegerWavevector) :
    momentumCLM nu value wave = NativeNegativeFourMomentum.weightedRowCLM wave.1
      (NativeCompleteAction.momentum nu value wave.1) := by
  change divergenceCLM value.snd wave - viscousCLM nu value.fst wave = _
  rw [divergence_complete_row, viscousCLM_source, ← map_sub]
  rfl

theorem curl_complete_momentum (nu : Viscosity) (value : FullSpace) (wave : IntegerWavevector) :
    NativeCompleteFilteredWrite.curlRowCLM wave (momentumCLM nu value) =
      fourierCurlCoefficient wave (NativeCompleteAction.momentum nu value wave) := by
  rw [NativeCompleteFilteredWrite.curlRowCLM_apply]
  by_cases zero : wave = 0
  · subst wave
    simp [fourierCurlCoefficient]
  · apply congrArg (fourierCurlCoefficient wave)
    funext coordinate
    rw [Pi.smul_apply, wholeVelocity_nonzero _ ⟨wave, zero⟩, momentum_complete_row]
    have original := congrArg (fun row : ComplexCoordinateEuclidean => row coordinate)
      (NativeCompleteFilteredWrite.decode_weighted_row ⟨wave, zero⟩ (NativeCompleteAction.momentum nu value wave))
    simpa only [PiLp.smul_apply, euclideanCoordinateRow_apply] using original

/-- The original three-channel native action on its complete velocity/stress input. -/
def actionCLM (nu : Viscosity) (modes : Finset IntegerWavevector) :
    FullSpace →L[ℝ] ComplexVorticityHilbertState :=
  (NativeCompleteFilteredWrite.readCLM modes).comp (momentumCLM nu)

theorem nativeRHS_eq_actionCLM (nu : Viscosity) (modes : Finset IntegerWavevector) :
    NativeCompleteEvolution.nativeRHS nu modes = actionCLM nu modes := by
  funext value
  apply lp.ext
  funext wave
  rw [NativeCompleteEvolution.nativeRHS_apply, NativeCompleteEvolution.nativeRow_is_complete_action,
    NativeCompleteAction.filteredAction, actionCLM, ContinuousLinearMap.comp_apply,
    NativeCompleteFilteredWrite.readCLM_apply, curl_complete_momentum]

/-- All orders concern differentiation in the complete source input, including the stress directions. -/
theorem nativeRHS_contDiff (nu : Viscosity) (modes : Finset IntegerWavevector) :
    ContDiff ℝ ∞ (NativeCompleteEvolution.nativeRHS nu modes) := by
  rw [nativeRHS_eq_actionCLM]
  exact (actionCLM nu modes).contDiff

theorem nativeRHS_hasFDerivAt (nu : Viscosity) (modes : Finset IntegerWavevector) (value : FullSpace) :
    HasFDerivAt (NativeCompleteEvolution.nativeRHS nu modes) (actionCLM nu modes) value := by
  rw [nativeRHS_eq_actionCLM]
  exact (actionCLM nu modes).hasFDerivAt

theorem source_primitive {nu : Viscosity} (modes : Finset IntegerWavevector)
    (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) (space : StageNineSpatialPoint) :
    NativeCompleteFilteredWrite.state modes seed 0 +
      canonicalTimePrimitive (fun point => actionCLM nu modes
        (NativeUnifiedCompleteSource.source seed (canonicalTimeProjection point)))
        (canonicalCauchySlicePoint time space) = NativeCompleteFilteredWrite.state modes seed time := by
  simpa only [NativeCompleteEvolution.generatedState, nativeRHS_eq_actionCLM] using
    NativeCompleteEvolution.source_primitive modes seed time nonnegative space

theorem complete_source_next {nu : Viscosity} (modes : Finset IntegerWavevector)
    (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    (actionCLM nu modes (NativeUnifiedCompleteSource.source seed (response.2.clockAdvance + time)),
      NativeCompleteCorrectionRead.residual (NativeUnifiedCompleteSource.source seed (response.2.clockAdvance + time))) =
    (actionCLM nu modes (NativeUnifiedCompleteSource.source response.1 time),
      NativeCompleteCorrectionRead.residual (NativeUnifiedCompleteSource.source response.1 time)) := by
  rw [NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative]

end

end SaturationMonoid.NavierStokes.NativeCompleteActionOperator
