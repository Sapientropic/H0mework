import H0mework.Versions.X.NavierStokes.NativeAction.Equation
import H0mework.Versions.X.NavierStokes.FullOrder.RecoveryPairedAction
import H0mework.Versions.X.NavierStokes.FullOrder.RecoveryTimeCanonical
import H0mework.Versions.X.NavierStokes.GlobalAction.GlobalPhysicalCarrier

set_option autoImplicit false
open scoped Topology ComplexOrder

namespace SaturationMonoid.NavierStokes.NativeCompletePairedAction

open Set Filter MeasureTheory
open SourceGeneratedNativeResponseDisposition SourceGeneratedNativeBoundedRun
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeStressSource
open NativeStressPairingCarrier NativeHilbertDiracCurrent NativeTimeJetCarrier
open NativeFiniteMacroPhysical NativeEventualTailControl
open PhysicsCore.DiracCliffordRepresentation

noncomputable section

private def PairLaw (value : NativeUnifiedGlobalStressSource.State) : Prop :=
  (covariance value.1 value.2).PosSemidef ∧
    ∀ wave output input, value.2 wave output input = value.2 wave input output

private theorem ordinary_law (mean : WholeRestartVelocityEndpointState) :
    PairLaw (NativeUnifiedGlobalStressSource.ordinary mean) := by
  constructor
  · constructor
    · ext left right
      simp [covariance, NativeUnifiedGlobalStressSource.ordinary]
    · intro coefficients
      simp [covariance, NativeUnifiedGlobalStressSource.ordinary]
  · exact quadraticFlux_symmetric _

variable {nu : Viscosity} {seed current next : GeneratedWholeRestartCurrent nu}

private theorem root_law (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    PairLaw (NativeMacroMomentumIntegral.recoveryCurve (NativeRecoveryUnifiedCurrent.receipt initial) time,
      NativeUnifiedStressSource.rootStress initial time) := by
  by_cases zero : time = 0
  · subst time
    have mean : wholeVelocity (NativeMacroMomentumIntegral.recoveryCurve
        (NativeRecoveryUnifiedCurrent.receipt initial) 0) = wholeVelocity (cofinal initial).mean := by
      rw [NativeMacroMomentumIntegral.recoveryCurve_full,
        NativeRecoveryRowAction.velocity_on_interval (NativeRecoveryUnifiedCurrent.receipt initial) ⟨0, by norm_num⟩]
      apply lp.ext
      funext wave
      exact NativeRecoveryMomentumIntegral.source_recovery_zero initial wave
    rw [PairLaw, NativeUnifiedStressSource.rootStress_zero]
    constructor
    · have same : covariance (NativeMacroMomentumIntegral.recoveryCurve
          (NativeRecoveryUnifiedCurrent.receipt initial) 0)
          (NativeCofinalStress.sourceGeneratedCofinalStress initial).stress =
          covariance (cofinal initial).mean (cofinal initial).stress := by
        unfold NativeStressPairingCarrier.covariance
        rw [mean]
        rfl
      rw [same]
      exact (cofinal initial).positive
    · exact cofinal_stress_symmetric initial
  · by_cases inside : time ∈ NativeRecoveryJointCurrent.Time initial
    · rw [PairLaw, NativeUnifiedStressSource.rootStress_at_time initial ⟨time, inside⟩]
      constructor
      · have same : covariance (NativeMacroMomentumIntegral.recoveryCurve
            (NativeRecoveryUnifiedCurrent.receipt initial) time)
            (NativeRecoveryJointCurrent.stress initial ⟨time, inside⟩) =
            covariance (NativeRecoveryPairedCarrier.mean initial ⟨time, inside⟩)
            (NativeRecoveryJointCurrent.stress initial ⟨time, inside⟩) := by
          unfold NativeStressPairingCarrier.covariance
          rw [NativeMacroMomentumIntegral.recoveryCurve_full, NativeRecoveryPairedCarrier.mean_velocity]
          rfl
        rw [same]
        exact NativeRecoveryPairedCarrier.source_covariance_positive initial ⟨time, inside⟩
      · exact NativeRecoveryPairedCarrier.source_stress_symmetric initial ⟨time, inside⟩
    · simpa only [PairLaw, NativeUnifiedStressSource.rootStress, if_neg zero, dif_neg inside,
        NativeUnifiedStressSource.rootOrdinary, NativeUnifiedGlobalStressSource.ordinary,
        covariance, NativeMacroMomentumIntegral.recoveryCurve_full, NativeRecoveryUnifiedCurrent.velocity] using
        ordinary_law (NativeMacroMomentumIntegral.recoveryCurve (NativeRecoveryUnifiedCurrent.receipt initial) time)

private theorem stage_law (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ) :
    PairLaw (NativeUnifiedGlobalStressSource.stage step time) := by
  by_cases inside : time ∈ Icc (wholeRestartVelocityAccumulationTime current) step.clockAdvance
  · have localTime : time - wholeRestartVelocityAccumulationTime current ∈
        Icc (0 : ℝ) (NativeMacroMomentumIntegral.recoveryTime step) := by
      rw [NativeMacroMomentumIntegral.clock_split] at inside
      constructor <;> linarith [inside.1, inside.2]
    have mean := NativeUnifiedMacroActionFeed.physical_recovery step _ localTime
    rw [add_sub_cancel] at mean
    simpa only [NativeUnifiedGlobalStressSource.stage, NativeUnifiedStressSource.macroStress,
      if_pos inside, mean] using root_law current (time - wholeRestartVelocityAccumulationTime current)
  · simpa only [NativeUnifiedGlobalStressSource.stage, NativeUnifiedStressSource.macroStress,
      if_neg inside, NativeUnifiedStressSource.macroOrdinary, NativeUnifiedGlobalStressSource.ordinary] using
      ordinary_law (step.physicalStageTrajectory time)

private theorem history_law
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) (time : ℝ) :
    PairLaw (NativeUnifiedGlobalStressSource.history arrival time) := by
  induction arrival with
  | initial => exact ordinary_law _
  | @step prior arrival response generated previous =>
      by_cases before : time ≤ clock arrival
      · simpa only [NativeUnifiedGlobalStressSource.history,
          endpointSplice_of_le _ _ _ _ before] using previous
      · simpa only [NativeUnifiedGlobalStressSource.history,
          endpointSplice_of_lt _ _ _ _ (lt_of_not_ge before)] using stage_law response.2 (time - clock arrival)

private theorem source_law (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    PairLaw (NativeUnifiedGlobalStressSource.source initial time) := by
  by_cases before : time ≤ clock (terminal initial).arrival
  · simpa only [NativeUnifiedGlobalStressSource.source, NativeUnifiedGlobalStressSource.global,
      endpointSplice_of_le _ _ _ _ before] using history_law (terminal initial).arrival time
  · simpa only [NativeUnifiedGlobalStressSource.source, NativeUnifiedGlobalStressSource.global,
      endpointSplice_of_lt _ _ _ _ (lt_of_not_ge before)] using
      ordinary_law (NativeFiniteMacroGlobal.tail (terminal initial) (time - clock (terminal initial).arrival))

/-- The original complete input supplies the existing canonical Gram-pair producer. -/
def source (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) : Data where
  mean := (NativeUnifiedCompleteSource.source initial time).fst
  stress := NativeCompleteStressCarrier.read (NativeUnifiedCompleteSource.source initial time).snd
  reality := by
    rw [NativeUnifiedCompleteSource.velocity_read]
    intro wave coordinate
    have original := congrFun (NativeGlobalPhysicalCarrier.source_reality initial time wave.1) coordinate
    change wholeVelocity (NativeAbsoluteEventualControl.velocity initial time)
      (nonzeroIntegerWavevectorNeg wave).1 coordinate =
        star (wholeVelocity (NativeAbsoluteEventualControl.velocity initial time) wave.1 coordinate) at original
    simpa only [wholeVelocity_nonzero] using original
  positive := by
    simpa only [NativeUnifiedCompleteSource.velocity_read, NativeUnifiedCompleteSource.stress_read,
      NativeUnifiedGlobalStressSource.stress, NativeUnifiedGlobalStressSource.source_velocity] using
      (source_law initial time).1

theorem source_symmetric (initial : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    (source initial time).stress wave output input = (source initial time).stress wave input output := by
  simpa only [source, NativeUnifiedCompleteSource.stress_read, NativeUnifiedGlobalStressSource.stress] using
    (source_law initial time).2 wave output input

theorem source_current (initial : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (direction : Fin 4) (wave : IntegerWavevector) :
    diracCurrent (source initial time) direction wave =
      NativePairedCurrentFourier.coefficient
        (wholeVelocity (NativeUnifiedCompleteSource.source initial time).fst)
        (NativeCompleteStressCarrier.read (NativeUnifiedCompleteSource.source initial time).snd) direction wave := by
  rw [diracCurrent_eq _ direction wave (source_symmetric initial time wave), pairedCurrent_eq]
  rfl

theorem material_component (data : Data) (wave : IntegerWavevector) (coordinate : Coordinate) :
    NativeRecoveryTimeCanonical.readComponent (matter data wave) coordinate = component data (wave, coordinate) :=
  NativeRecoveryTimeCanonical.readComponent_program (background data)
    (fun frequency direction => component data (frequency, direction)) wave coordinate

theorem material_stress (data : Data) (wave : IntegerWavevector) (output input : Coordinate) :
    -inner ℂ (NativeRecoveryTimeCanonical.readComponent (matter data wave) output)
      (NativeRecoveryTimeCanonical.readComponent (matter data 0) input) = data.stress wave output input := by
  rw [material_component, material_component, component_inner, sub_zero, neg_neg]

/-- The original constitutive action reads the same material Gram and canonical Γ current. -/
def momentum (nu : Viscosity) (data : Data) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  projectedDivergenceCLM wave (fun output input =>
    -inner ℂ (NativeRecoveryTimeCanonical.readComponent (matter data wave) output)
      (NativeRecoveryTimeCanonical.readComponent (matter data 0) input)) -
    (nu.coeff * integerWaveViscousMultiplier wave) • fun coordinate => diracCurrent data coordinate.succ wave

theorem source_momentum (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    momentum nu (source initial time) wave =
      NativeCompleteAction.momentum nu (NativeUnifiedCompleteSource.source initial time) wave := by
  simp only [momentum, material_stress, source_current, NativePairedCurrentFourier.coefficient, Fin.cases_succ]
  rfl

def vorticityAction (nu : Viscosity) (modes : Finset IntegerWavevector) (data : Data) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState modes (fun wave => fourierCurlCoefficient wave (momentum nu data wave))

theorem source_nativeRHS (initial : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (modes : Finset IntegerWavevector) :
    NativeCompleteEvolution.nativeRHS nu modes (NativeUnifiedCompleteSource.source initial time) =
      vorticityAction nu modes (source initial time) := by
  apply lp.ext
  funext wave
  rw [NativeCompleteEvolution.nativeRHS_apply, NativeCompleteEvolution.nativeRow_is_complete_action,
    vorticityAction, finiteComplexVorticityState_apply, source_momentum]
  rfl

private theorem data_ext {first second : Data}
    (mean : first.mean = second.mean) (stress : first.stress = second.stress) : first = second := by
  cases first
  cases second
  cases mean
  cases stress
  rfl

theorem source_next (initial : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) initial)
    (generated : generatedWholeRestartEndpointMacroRespond initial = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    source initial (response.2.clockAdvance + time) = source response.1 time := by
  have original := NativeUnifiedCompleteSource.source_generated_next initial response generated time nonnegative
  apply data_ext
  · exact congrArg (fun value : FullSpace => value.fst) original
  · exact congrArg (fun value : FullSpace => NativeCompleteStressCarrier.read value.snd) original

theorem current_next (initial : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) initial)
    (generated : generatedWholeRestartEndpointMacroRespond initial = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    diracCurrent (source initial (response.2.clockAdvance + time)) = diracCurrent (source response.1 time) :=
  congrArg diracCurrent (source_next initial response generated time nonnegative)

theorem source_hasDerivAt_ae (initial : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector) :
    ∀ᵐ time : ℝ, 0 < time →
      HasDerivAt (NativeCompleteFilteredWrite.state modes initial)
        (vorticityAction nu modes (source initial time)) time := by
  simpa only [source_nativeRHS] using NativeCompleteEvolution.source_hasDerivAt_ae modes initial

private def rowRead (wave : NonzeroIntegerWavevector) (coordinate : Coordinate) :
    WholeRestartVelocityEndpointState →L[ℝ] ℂ :=
  integerWaveNormSq wave.1 ^ 2 •
    (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Coordinate => ℂ) coordinate).restrictScalars ℝ).comp
      (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave))

private theorem rowRead_apply (wave : NonzeroIntegerWavevector) (coordinate : Coordinate)
    (value : WholeRestartVelocityEndpointState) :
    rowRead wave coordinate value = integerWaveNormSq wave.1 ^ 2 • value wave coordinate := rfl

private theorem rowRead_state (initial : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : NonzeroIntegerWavevector) (coordinate : Coordinate) :
    rowRead wave coordinate (NativeGlobalHilbertAction.sourceState initial time) =
      diracCurrent (source initial time) coordinate.succ wave.1 := by
  rw [source_current]
  change _ = wholeVelocity (NativeUnifiedCompleteSource.source initial time).fst wave.1 coordinate
  rw [NativeUnifiedCompleteSource.velocity_read, wholeVelocity_nonzero]
  exact congrArg (fun value : ComplexCoordinateEuclidean => value coordinate)
    (NativeGlobalHilbertAction.sourceState_reconstruct initial time wave)

private theorem rowRead_action (initial : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : NonzeroIntegerWavevector) (coordinate : Coordinate) :
    rowRead wave coordinate (momentumCLM nu (NativeUnifiedCompleteSource.source initial time)) =
      momentum nu (source initial time) wave.1 coordinate := by
  rw [rowRead_apply, source_momentum, NativeUnifiedCompleteSource.source_momentum,
    NativeUnifiedGlobalStressSource.source_momentum]
  have original := congrArg (fun value : ComplexCoordinateEuclidean => value coordinate)
    (NativeCompleteFilteredWrite.decode_weighted_row wave
      (NativeCompleteAction.momentum nu (NativeUnifiedCompleteSource.source initial time) wave.1))
  simpa only [NativeUnifiedGlobalStressSource.momentumRow, NativeCompleteAction.momentum,
    NativeCompleteAction.velocity, NativeCompleteAction.stress, NativeUnifiedCompleteSource.stress_read,
    NativeUnifiedCompleteSource.velocity_read, NativeUnifiedGlobalStressSource.stress,
    NativeUnifiedGlobalStressSource.source_velocity, PiLp.smul_apply, euclideanCoordinateRow_apply] using original

/-- Actual physical-time differentiation of the same canonical spatial Γ current. -/
theorem spatial_current_hasDerivAt_ae (initial : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 < time → ∀ wave : IntegerWavevector, ∀ coordinate : Coordinate,
      HasDerivAt (fun sample => diracCurrent (source initial sample) coordinate.succ wave)
        (momentum nu (source initial time) wave coordinate) time := by
  filter_upwards [NativeUnifiedCompleteSource.source_hasDerivAt_ae initial] with time derivative
  intro positive wave coordinate
  by_cases zero : wave = 0
  · subst wave
    simpa [source_current, source_momentum, NativePairedCurrentFourier.coefficient,
      NativeCompleteAction.momentum, NativeCompleteAction.velocity, NativeTimeJetCarrier.projectedDivergenceCLM_apply,
      transverseProjection, integerWaveViscousMultiplier] using hasDerivAt_const time (0 : ℂ)
  · have original := (rowRead ⟨wave, zero⟩ coordinate).hasFDerivAt.comp_hasDerivAt time (derivative positive)
    simpa only [Function.comp_def, rowRead_state, rowRead_action] using original

end
end SaturationMonoid.NavierStokes.NativeCompletePairedAction
