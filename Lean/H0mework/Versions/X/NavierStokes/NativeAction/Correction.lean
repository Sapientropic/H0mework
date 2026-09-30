import H0mework.Versions.X.NavierStokes.UnifiedAction.UnifiedCompleteSource
import H0mework.Versions.X.NavierStokes.SourceAction.JointFilter

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeCompleteCorrectionRead

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open SourceGeneratedNativeResponseDisposition
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeStressSource NativeStressCurlAlgebra
open NativeRecoveryEscapeCorrection (projectStress resolvedStress)

noncomputable section

def residual (value : FullSpace) : NativeFluidStressFourierState :=
  NativeCompleteStressCarrier.read value.snd - quadraticFlux (wholeVelocity value.fst)

def correction (modes : Finset IntegerWavevector) (value : FullSpace) : NativeFluidStressFourierState :=
  NativeJointStressFilterControl.stress modes (wholeVelocity value.fst)
    (NativeCompleteStressCarrier.read value.snd)

theorem correction_tensor (modes : Finset IntegerWavevector) (value : FullSpace) :
    correction modes value = projectStress modes (NativeCompleteStressCarrier.read value.snd) -
      quadraticFlux (complexSharpSupportProjection modes (wholeVelocity value.fst)) := rfl

theorem correction_decomposition (modes : Finset IntegerWavevector) (value : FullSpace) :
    correction modes value = resolvedStress modes (wholeVelocity value.fst) +
      projectStress modes (residual value) := by
  funext wave output input
  simp only [correction, NativeJointStressFilterControl.stress, resolvedStress,
    projectStress, residual, Pi.add_apply, Pi.sub_apply]
  by_cases inside : wave ∈ modes <;> simp [inside]

theorem correction_action (modes : Finset IntegerWavevector) (value : FullSpace) :
    nativeFluidConstitutiveVorticityAction (correction modes value) =
      NativeWholeVelocityFilterControl.coefficient modes (wholeVelocity value.fst) +
        nativeFluidConstitutiveVorticityAction (projectStress modes (residual value)) := by
  funext wave
  exact NativeJointStressFilterControl.coefficient_decomposition modes
    (wholeVelocity value.fst) (NativeCompleteStressCarrier.read value.snd) wave

theorem original_native_action (modes : Finset IntegerWavevector)
    (vorticity : ComplexVorticityHilbertState) (zero : vorticity 0 = 0)
    (transverse : WholeStateTransverse vorticity) (stress : NativeFluidStressFourierState) :
    NativeJointStressFilterControl.coefficient modes (wholeBiotSavartVelocityState vorticity) stress =
      nativeTurbulenceCorrectionAt modes vorticity +
        nativeFluidConstitutiveVorticityAction (projectStress modes
          (stress - quadraticFlux (wholeBiotSavartVelocityState vorticity))) := by
  funext wave
  rw [NativeJointStressFilterControl.coefficient_decomposition,
    NativeWholeVelocityFilterControl.coefficient_eq_original modes vorticity zero transverse]
  rfl

variable {nu : Viscosity}

theorem source_residual (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    residual (NativeUnifiedCompleteSource.source seed time) =
      NativeUnifiedGlobalStressSource.stress seed time -
        quadraticFlux (wholeVelocity (NativeAbsoluteEventualControl.velocity seed time)) := by
  rw [residual, NativeUnifiedCompleteSource.stress_read, NativeUnifiedCompleteSource.velocity_read]

theorem source_correction (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (modes : Finset IntegerWavevector) :
    correction modes (NativeUnifiedCompleteSource.source seed time) =
      NativeJointStressFilterControl.stress modes
        (wholeVelocity (NativeAbsoluteEventualControl.velocity seed time))
        (NativeUnifiedGlobalStressSource.stress seed time) := by
  rw [correction, NativeUnifiedCompleteSource.stress_read, NativeUnifiedCompleteSource.velocity_read]

theorem source_action (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (modes : Finset IntegerWavevector) :
    nativeFluidConstitutiveVorticityAction (correction modes (NativeUnifiedCompleteSource.source seed time)) =
      NativeWholeVelocityFilterControl.coefficient modes
        (wholeVelocity (NativeAbsoluteEventualControl.velocity seed time)) +
      nativeFluidConstitutiveVorticityAction
        (projectStress modes (residual (NativeUnifiedCompleteSource.source seed time))) := by
  rw [correction_action, NativeUnifiedCompleteSource.velocity_read]

theorem residual_generated_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    residual (NativeUnifiedCompleteSource.source seed (response.2.clockAdvance + time)) =
      residual (NativeUnifiedCompleteSource.source response.1 time) :=
  congrArg residual (NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative)

theorem correction_generated_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) (modes : Finset IntegerWavevector) :
    correction modes (NativeUnifiedCompleteSource.source seed (response.2.clockAdvance + time)) =
      correction modes (NativeUnifiedCompleteSource.source response.1 time) :=
  congrArg (correction modes) (NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative)

theorem cofinal_residual (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) :
    residual (NativeUnifiedCompleteSource.source seed (wholeRestartVelocityAccumulationTime seed)) =
      (NativeCofinalStress.sourceGeneratedCofinalStress seed).stress -
        quadraticFlux (wholeVelocity
          (NativeAbsoluteEventualControl.velocity seed (wholeRestartVelocityAccumulationTime seed))) := by
  rw [source_residual, NativeUnifiedGlobalStressSource.source_cofinal_stress response generated]

theorem cofinal_correction (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (modes : Finset IntegerWavevector) :
    correction modes (NativeUnifiedCompleteSource.source seed (wholeRestartVelocityAccumulationTime seed)) =
      NativeJointStressFilterControl.stress modes
        (wholeVelocity (NativeAbsoluteEventualControl.velocity seed (wholeRestartVelocityAccumulationTime seed)))
        (NativeCofinalStress.sourceGeneratedCofinalStress seed).stress := by
  rw [source_correction, NativeUnifiedGlobalStressSource.source_cofinal_stress response generated]

theorem recovery_velocity (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (inside : time ∈ Icc (0 : ℝ) (NativeMacroMomentumIntegral.recoveryTime response.2)) :
    wholeVelocity (NativeAbsoluteEventualControl.velocity seed
      (wholeRestartVelocityAccumulationTime seed + time)) = NativeRecoveryUnifiedCurrent.velocity seed time := by
  rw [← NativeUnifiedGlobalStressSource.source_velocity,
    NativeUnifiedGlobalStressSource.source_step_read response generated _
      (by linarith [NativeMacroMomentumIntegral.accumulation_positive response.2, inside.1])
      (by rw [NativeMacroMomentumIntegral.clock_split]; linarith [inside.2])]
  change wholeVelocity (response.2.physicalStageTrajectory
    (wholeRestartVelocityAccumulationTime seed + time)) = _
  rw [NativeUnifiedMacroActionFeed.physical_recovery response.2 time inside,
    NativeMacroMomentumIntegral.recoveryCurve_full]
  rfl

theorem cofinal_residual_original (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) :
    residual (NativeUnifiedCompleteSource.source seed (wholeRestartVelocityAccumulationTime seed)) =
      NativeCofinalStressDefect.stressDefect (NativeCofinalStress.sourceGeneratedCofinalStress seed) := by
  have atZero := recovery_velocity seed response generated 0
    ⟨le_rfl, (NativeMacroMomentumIntegral.recoveryTime_mem response.2).1⟩
  simp only [add_zero] at atZero
  have original : NativeRecoveryUnifiedCurrent.velocity seed 0 = NativeCofinalMomentumAction.endpointVelocity seed := by
    rw [NativeRecoveryUnifiedCurrent.velocity,
      NativeRecoveryRowAction.velocity_on_interval (NativeRecoveryUnifiedCurrent.receipt seed) ⟨0, by norm_num⟩]
    apply lp.ext
    funext wave
    exact NativeRecoveryMomentumIntegral.source_recovery_zero seed wave
  rw [cofinal_residual seed response generated, atZero, original]
  rfl

theorem recovery_residual (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : NativeRecoveryJointCurrent.Time seed) :
    residual (NativeUnifiedCompleteSource.source seed (wholeRestartVelocityAccumulationTime seed + time.1)) =
      NativeRecoveryJointCurrent.stress seed time - quadraticFlux (NativeRecoveryUnifiedCurrent.velocity seed time.1) := by
  have inside : time.1 ∈ Icc (0 : ℝ) (NativeMacroMomentumIntegral.recoveryTime response.2) := by
    rw [NativeUnifiedMacroActionFeed.recoveryTime_eq_root]
    exact ⟨time.2.1.le, time.2.2.le⟩
  rw [source_residual, recovery_velocity seed response generated time.1 inside,
    NativeUnifiedGlobalStressSource.source_recovery_stress response generated time.1 inside,
    NativeUnifiedStressSource.rootStress_at_time seed time]

theorem recovery_correction (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : NativeRecoveryJointCurrent.Time seed) (modes : Finset IntegerWavevector) :
    correction modes (NativeUnifiedCompleteSource.source seed (wholeRestartVelocityAccumulationTime seed + time.1)) =
      NativeJointStressFilterControl.stress modes (NativeRecoveryUnifiedCurrent.velocity seed time.1)
        (NativeRecoveryJointCurrent.stress seed time) := by
  have inside : time.1 ∈ Icc (0 : ℝ) (NativeMacroMomentumIntegral.recoveryTime response.2) := by
    rw [NativeUnifiedMacroActionFeed.recoveryTime_eq_root]
    exact ⟨time.2.1.le, time.2.2.le⟩
  rw [source_correction, recovery_velocity seed response generated time.1 inside,
    NativeUnifiedGlobalStressSource.source_recovery_stress response generated time.1 inside,
    NativeUnifiedStressSource.rootStress_at_time seed time]

theorem uncovered_residual_original (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : NativeRecoveryJointCurrent.Time seed)
    (uncovered : time.1 ∉ NativeRecoveryAEWindows.regularSet
      (NativeRecoveryUnifiedCurrent.receipt seed) (NativeRecoveryUnifiedCurrent.terminal seed)) :
    residual (NativeUnifiedCompleteSource.source seed (wholeRestartVelocityAccumulationTime seed + time.1)) =
      NativeRecoveryEscapeStress.defect (NativeRecoveryEscapeStress.sourceStress seed time.1 time.2 uncovered)
        (NativeRecoveryJointCurrent.clock seed time).2.2 := by
  have endpoint := NativeRecoveryEscapeStress.fixedEndpoint_reads_original
    (NativeRecoveryCoverage.sourceUncoveredAction seed time.1 time.2 uncovered)
    (NativeRecoveryJointCurrent.clock seed time).2.2
  have same := endpoint.trans (NativeRecoveryJointCurrent.velocity_read seed time).symm
  rw [recovery_residual seed response generated time,
    NativeRecoveryJointCurrent.stress_uncovered seed time uncovered]
  unfold NativeRecoveryEscapeStress.defect
  exact congrArg (fun velocity : ComplexVorticityHilbertState =>
    (NativeRecoveryEscapeStress.sourceStress seed time.1 time.2 uncovered).stress - quadraticFlux velocity) same.symm

theorem uncovered_correction_original (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : NativeRecoveryJointCurrent.Time seed)
    (uncovered : time.1 ∉ NativeRecoveryAEWindows.regularSet
      (NativeRecoveryUnifiedCurrent.receipt seed) (NativeRecoveryUnifiedCurrent.terminal seed))
    (modes : Finset IntegerWavevector) :
    correction modes (NativeUnifiedCompleteSource.source seed (wholeRestartVelocityAccumulationTime seed + time.1)) =
      NativeRecoveryEscapeCorrection.correctionLimit
        (NativeRecoveryEscapeStress.sourceStress seed time.1 time.2 uncovered)
        (NativeRecoveryJointCurrent.clock seed time).2.2 modes := by
  have endpoint := NativeRecoveryEscapeStress.fixedEndpoint_reads_original
    (NativeRecoveryCoverage.sourceUncoveredAction seed time.1 time.2 uncovered)
    (NativeRecoveryJointCurrent.clock seed time).2.2
  have same := endpoint.trans (NativeRecoveryJointCurrent.velocity_read seed time).symm
  rw [recovery_correction seed response generated time modes,
    NativeRecoveryJointCurrent.stress_uncovered seed time uncovered]
  unfold NativeRecoveryEscapeCorrection.correctionLimit
  exact congrArg (fun velocity : ComplexVorticityHilbertState =>
    projectStress modes (NativeRecoveryEscapeStress.sourceStress seed time.1 time.2 uncovered).stress -
      quadraticFlux (complexSharpSupportProjection modes velocity)) same.symm

end
end SaturationMonoid.NavierStokes.NativeCompleteCorrectionRead
