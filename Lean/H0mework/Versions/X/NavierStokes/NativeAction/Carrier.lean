import H0mework.Versions.X.NavierStokes.UnifiedAction.UnifiedCompleteSource
import H0mework.Versions.X.NavierStokes.SourceAction.JointFilter

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeCompleteAction

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeStressSource NativeTimeJetCarrier
open NativeStressCurlAlgebra

noncomputable section

def velocity (value : FullSpace) : ComplexVorticityHilbertState := wholeVelocity value.fst

def stress (value : FullSpace) : NativeFluidStressFourierState := NativeCompleteStressCarrier.read value.snd

def momentum (nu : Viscosity) (value : FullSpace) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  projectedDivergenceCLM wave (stress value wave) -
    (nu.coeff * integerWaveViscousMultiplier wave) • velocity value wave

def filteredAction (nu : Viscosity) (modes : Finset IntegerWavevector)
    (value : FullSpace) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  if wave ∈ modes then fourierCurlCoefficient wave (momentum nu value wave) else 0

def resolvedGenerator (nu : Viscosity) (modes : Finset IntegerWavevector)
    (value : FullSpace) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  nativeFluidConstitutiveVorticityAction
    (quadraticFlux (complexSharpSupportProjection modes (velocity value))) wave -
      (nu.coeff * integerWaveViscousMultiplier wave) •
        fourierCurlCoefficient wave (complexSharpSupportProjection modes (velocity value) wave)

def correction (modes : Finset IntegerWavevector) (value : FullSpace) :
    IntegerWavevector → ComplexCoordinateVector :=
  NativeJointStressFilterControl.coefficient modes (velocity value) (stress value)

theorem full_native_action (nu : Viscosity) (modes : Finset IntegerWavevector)
    (value : FullSpace) (wave : IntegerWavevector) :
    filteredAction nu modes value wave =
      resolvedGenerator nu modes value wave + correction modes value wave := by
  let curl := (fourierCurlCoefficientContinuousLinearMap wave).restrictScalars ℝ
  have projected (tensor : NativeFluidStressCoefficient) :
      curl (projectedDivergenceCLM wave tensor) = NativeWholeVelocityFilterControl.rowAction wave tensor := by
    change fourierCurlCoefficient wave
      (transverseProjection wave (nativeFluidStressDivergenceCoefficient (fun _ => tensor) wave)) = _
    rw [fourierCurlCoefficient_transverseProjection]
    rfl
  unfold filteredAction resolvedGenerator correction
  change (if wave ∈ modes then curl (momentum nu value wave) else 0) =
    (NativeWholeVelocityFilterControl.rowAction wave
        (quadraticFlux (complexSharpSupportProjection modes (velocity value)) wave) -
      (nu.coeff * integerWaveViscousMultiplier wave) •
        curl (complexSharpSupportProjection modes (velocity value) wave)) +
      NativeWholeVelocityFilterControl.rowAction wave
        (NativeRecoveryEscapeCorrection.projectStress modes (stress value) wave -
          quadraticFlux (complexSharpSupportProjection modes (velocity value)) wave)
  rw [map_sub]
  by_cases included : wave ∈ modes
  · simp only [if_pos included, NativeRecoveryEscapeCorrection.projectStress,
      complexSharpSupportProjection_apply]
    change curl (projectedDivergenceCLM wave (stress value wave) -
        (nu.coeff * integerWaveViscousMultiplier wave) • velocity value wave) = _
    rw [map_sub, map_smul, projected]
    abel
  · simp only [if_neg included, NativeRecoveryEscapeCorrection.projectStress,
      complexSharpSupportProjection_apply, map_zero, smul_zero, sub_zero]
    abel

theorem source_native_action {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) (time : ℝ) (wave : IntegerWavevector) :
    filteredAction nu modes (NativeUnifiedCompleteSource.source seed time) wave =
      resolvedGenerator nu modes (NativeUnifiedCompleteSource.source seed time) wave +
        correction modes (NativeUnifiedCompleteSource.source seed time) wave :=
  full_native_action nu modes _ wave

theorem source_action_generated_next {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (modes : Finset IntegerWavevector) (time : ℝ) (nonnegative : 0 ≤ time) :
    (filteredAction nu modes (NativeUnifiedCompleteSource.source seed (response.2.clockAdvance + time)),
      correction modes (NativeUnifiedCompleteSource.source seed (response.2.clockAdvance + time))) =
    (filteredAction nu modes (NativeUnifiedCompleteSource.source response.1 time),
      correction modes (NativeUnifiedCompleteSource.source response.1 time)) := by
  rw [NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeCompleteAction
