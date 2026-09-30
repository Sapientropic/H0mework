import H0mework.Versions.X.NavierStokes.NativeAction.Evolution
import H0mework.Versions.X.NavierStokes.NativeAction.VelocityCurl

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeCompleteEquation

open Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeEndpointVelocityCarrier

noncomputable section

variable {nu : Viscosity}

theorem full_source_row (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (time : ℝ) (nonnegative : 0 ≤ time) (wave : IntegerWavevector) :
    NativeCompleteEvolution.nativeRHS nu modes (NativeUnifiedCompleteSource.source seed time) wave =
      wholeLatticeVorticityFourierTangentAt nu.coeff (NativeCompleteFilteredWrite.state modes seed time) wave +
      NativeWholeVelocityFilterControl.coefficient modes
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) wave +
      nativeFluidConstitutiveVorticityAction
        (NativeRecoveryEscapeCorrection.projectStress modes
          (NativeCompleteCorrectionRead.residual (NativeUnifiedCompleteSource.source seed time))) wave := by
  rw [NativeCompleteEvolution.nativeRHS_apply, NativeCompleteEvolution.nativeRow,
    NativeCompleteVelocityCurl.resolved_generator_original modes seed time nonnegative]

theorem source_native_equation (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 < time → ∀ wave : IntegerWavevector,
      HasDerivAt (fun actual => NativeCompleteFilteredWrite.state modes seed actual wave)
        (wholeLatticeVorticityFourierTangentAt nu.coeff (NativeCompleteFilteredWrite.state modes seed time) wave +
          NativeWholeVelocityFilterControl.coefficient modes
            (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) wave +
          nativeFluidConstitutiveVorticityAction
            (NativeRecoveryEscapeCorrection.projectStress modes
              (NativeCompleteCorrectionRead.residual (NativeUnifiedCompleteSource.source seed time))) wave) time := by
  filter_upwards [NativeCompleteEvolution.source_hasDerivAt_ae modes seed] with time derivative
  intro positive wave
  have row := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivAt
    time (derivative positive)
  change HasDerivAt (fun actual => NativeCompleteFilteredWrite.state modes seed actual wave)
    (NativeCompleteEvolution.nativeRHS nu modes (NativeUnifiedCompleteSource.source seed time) wave) time at row
  rw [full_source_row modes seed time positive.le] at row
  exact row

end
end SaturationMonoid.NavierStokes.NativeCompleteEquation
