import H0mework.NavierStokes.UnifiedAction.UnifiedCompleteSource
import H0mework.NavierStokes.RecoveryAction.RecoveryJointAction

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeCompleteFilteredWrite

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
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open SourceGeneratedNativeResponseDisposition
open NativeEndpointVelocityCarrier NativeCompleteStressAction NativeTimeJetCarrier
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator

noncomputable section

/-- Decode the original negative-order row before taking its physical Fourier curl. -/
def curlRowCLM (wave : IntegerWavevector) : WholeRestartVelocityEndpointState →L[ℝ] ComplexCoordinateVector :=
  ((fourierCurlCoefficientContinuousLinearMap wave).restrictScalars ℝ).comp
    (integerWaveNormSq wave ^ 2 •
      ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).comp wholeVelocityCLM))

theorem curlRowCLM_apply (wave : IntegerWavevector) (value : WholeRestartVelocityEndpointState) :
    curlRowCLM wave value = fourierCurlCoefficient wave
      (integerWaveNormSq wave ^ 2 • wholeVelocity value wave) := rfl

/-- Finite filtering makes this exact physical curl a continuous map of the whole input carrier. -/
def readCLM (modes : Finset IntegerWavevector) :
    WholeRestartVelocityEndpointState →L[ℝ] ComplexVorticityHilbertState :=
  ∑ wave ∈ modes,
    (lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).comp
      (curlRowCLM wave)

theorem readCLM_apply (modes : Finset IntegerWavevector) (value : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) :
    readCLM modes value wave = if wave ∈ modes then curlRowCLM wave value else 0 := by
  simp only [readCLM, sum_apply, ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]
  change finiteComplexVorticityState modes (fun frequency => curlRowCLM frequency value) wave = _
  exact finiteComplexVorticityState_apply _ _ _

theorem decode_embed (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    integerWaveNormSq wave ^ 2 • wholeVelocity (NativeNegativeFourMomentum.embed value) wave =
      wholeVelocity value wave := by
  by_cases zero : wave = 0
  · subst wave
    simp
  · funext coordinate
    rw [Pi.smul_apply, wholeVelocity_nonzero _ ⟨wave, zero⟩, wholeVelocity_nonzero _ ⟨wave, zero⟩]
    have original := congrArg (fun row : ComplexCoordinateEuclidean => row coordinate)
      (NativeNegativeFourMomentum.embed_reconstruct value ⟨wave, zero⟩)
    simpa only [PiLp.smul_apply] using original

theorem readCLM_embed (modes : Finset IntegerWavevector) (value : WholeRestartVelocityEndpointState) :
    readCLM modes (NativeNegativeFourMomentum.embed value) =
      finiteComplexVorticityState modes (fun wave => fourierCurlCoefficient wave (wholeVelocity value wave)) := by
  apply lp.ext
  funext wave
  rw [readCLM_apply, finiteComplexVorticityState_apply, curlRowCLM_apply, decode_embed]

theorem decode_weighted_row (wave : NonzeroIntegerWavevector) (row : ComplexCoordinateVector) :
    integerWaveNormSq wave.1 ^ 2 • NativeNegativeFourMomentum.weightedRowCLM wave.1 row =
      euclideanCoordinateRow row := by
  change integerWaveNormSq wave.1 ^ 2 •
    (NativeNegativeFourMomentum.weight wave.1 • euclideanCoordinateRow row) = _
  rw [NativeNegativeFourMomentum.weight, smul_smul, ← mul_pow,
    mul_inv_cancel₀ (integerWaveNormSq_pos wave.2).ne', one_pow, one_smul]

variable {nu : Viscosity}

def state (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ComplexVorticityHilbertState := readCLM modes (NativeGlobalHilbertAction.sourceState seed time)

def action (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ComplexVorticityHilbertState := readCLM modes (momentumCLM nu (NativeUnifiedCompleteSource.source seed time))

theorem state_apply (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (time : ℝ) (wave : IntegerWavevector) :
    state modes seed time wave = if wave ∈ modes then
      fourierCurlCoefficient wave (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave) else 0 := by
  rw [state, NativeGlobalHilbertAction.sourceState, readCLM_embed,
    finiteComplexVorticityState_apply, NativeUnifiedCompleteSource.velocity_read]

theorem curl_source_action (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    curlRowCLM wave (momentumCLM nu (NativeUnifiedCompleteSource.source seed time)) =
      fourierCurlCoefficient wave
        (projectedDivergenceCLM wave (NativeCompleteStressCarrier.read (NativeUnifiedCompleteSource.source seed time).snd wave) -
          (nu.coeff * integerWaveViscousMultiplier wave) •
            wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave) := by
  rw [curlRowCLM_apply]
  by_cases zero : wave = 0
  · subst wave
    simp [fourierCurlCoefficient]
  · rw [NativeUnifiedCompleteSource.stress_read, NativeUnifiedCompleteSource.velocity_read]
    apply congrArg (fourierCurlCoefficient wave)
    funext coordinate
    rw [Pi.smul_apply, wholeVelocity_nonzero _ ⟨wave, zero⟩,
      NativeUnifiedCompleteSource.source_momentum, NativeUnifiedGlobalStressSource.source_momentum]
    have original := congrArg (fun row : ComplexCoordinateEuclidean => row coordinate)
      (decode_weighted_row ⟨wave, zero⟩
        (projectedDivergenceCLM wave (NativeUnifiedGlobalStressSource.stress seed time wave) -
          (nu.coeff * integerWaveViscousMultiplier wave) •
            wholeVelocity (NativeAbsoluteEventualControl.velocity seed time) wave))
    simpa only [NativeUnifiedGlobalStressSource.momentumRow, NativeUnifiedGlobalStressSource.stress,
      NativeUnifiedGlobalStressSource.source_velocity, PiLp.smul_apply, euclideanCoordinateRow_apply] using original

theorem action_apply (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (time : ℝ) (wave : IntegerWavevector) :
    action modes seed time wave = if wave ∈ modes then
      fourierCurlCoefficient wave
        (projectedDivergenceCLM wave (NativeCompleteStressCarrier.read (NativeUnifiedCompleteSource.source seed time).snd wave) -
          (nu.coeff * integerWaveViscousMultiplier wave) •
            wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave) else 0 := by
  rw [action, readCLM_apply, curl_source_action]

theorem source_action_integrable (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ)
    (a_nonnegative : 0 ≤ a) (b_nonnegative : 0 ≤ b) :
    IntervalIntegrable (fun time => momentumCLM nu (NativeUnifiedCompleteSource.source seed time)) volume a b := by
  simp only [NativeUnifiedCompleteSource.source_momentum]
  exact (NativeUnifiedGlobalActionFeed.action_intervalIntegrable seed a a_nonnegative).symm.trans
    (NativeUnifiedGlobalActionFeed.action_intervalIntegrable seed b b_nonnegative)

theorem source_hasDerivAt_ae (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (state modes seed) (action modes seed time) time := by
  filter_upwards [NativeUnifiedCompleteSource.source_hasDerivAt_ae seed] with time derivative
  intro positive
  exact (readCLM modes).hasFDerivAt.comp_hasDerivAt time (derivative positive)

theorem source_integral (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (a b : ℝ) (a_nonnegative : 0 ≤ a) (b_nonnegative : 0 ≤ b) :
    state modes seed b - state modes seed a = ∫ time in a..b, action modes seed time := by
  have original := congrArg (readCLM modes)
    (NativeUnifiedCompleteSource.source_integral seed a b a_nonnegative b_nonnegative)
  rw [map_sub, ← (readCLM modes).intervalIntegral_comp_comm
    (source_action_integrable seed a b a_nonnegative b_nonnegative)] at original
  exact original

def generatedState (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu) (point : BasePoint) :
    ComplexVorticityHilbertState := state modes seed 0 +
      canonicalTimePrimitive (fun point => action modes seed (canonicalTimeProjection point)) point

theorem source_primitive (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (time : ℝ) (nonnegative : 0 ≤ time) (space : StageNineSpatialPoint) :
    generatedState modes seed (canonicalCauchySlicePoint time space) = state modes seed time := by
  have original := congrArg (readCLM modes)
    (NativeUnifiedCompleteSource.source_primitive seed time nonnegative space)
  rw [map_add] at original
  unfold canonicalTimePrimitive at original
  unfold generatedState canonicalTimePrimitive
  simp only [canonicalTimeProjection_slice] at original ⊢
  rw [← (readCLM modes).intervalIntegral_comp_comm (source_action_integrable seed 0 time le_rfl nonnegative)] at original
  exact original

theorem state_generated_next (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    state modes seed (response.2.clockAdvance + time) = state modes response.1 time := by
  have same := congrArg (fun value : FullSpace => readCLM modes (NativeNegativeFourMomentum.embed value.fst))
    (NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative)
  simpa only [NativeUnifiedCompleteSource.velocity_read, state, NativeGlobalHilbertAction.sourceState] using same

theorem action_generated_next (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    action modes seed (response.2.clockAdvance + time) = action modes response.1 time :=
  congrArg (fun value : FullSpace => readCLM modes (momentumCLM nu value))
    (NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative)

theorem generatedState_next (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) (space : StageNineSpatialPoint) :
    generatedState modes seed (canonicalCauchySlicePoint (response.2.clockAdvance + time) space) =
      generatedState modes response.1 (canonicalCauchySlicePoint time space) := by
  rw [source_primitive modes seed _ (add_nonneg response.2.clockAdvance_pos.le nonnegative),
    source_primitive modes response.1 time nonnegative,
    state_generated_next modes seed response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeCompleteFilteredWrite
