import H0mework.NavierStokes.Restart.NativeAccumulationWholeNSVelocityJoin
import H0mework.NavierStokes.InitialData.FiniteModalPicardBounds

/-!
# Fixed-window vorticity landing at the actual accumulation interface

The endpoint source already generates the weak physical velocity row at the
accumulation time `T`.  This module curls that exact row before any
post-interface reentry is selected.  Every actual contact vorticity converges
on every fixed Fourier window to the resulting finite vorticity state.

The result fixes the finite-observer side of the same-T interface without
selecting a post-interface target.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open Set Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteModalPicardBounds
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationWholeNSVelocityJoin

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage
namespace FullFrameBoundaryVorticityFixedWindowLanding

variable {nu : Viscosity}

/-! ## The actual boundary row generated at `T` -/

/-- The formal vorticity row at `T`, obtained by curling the exact generated
weak velocity endpoint.  It is intentionally row-valued: whole `lp²`
summability is the remaining tail-settlement responsibility. -/
def accumulationBoundaryFormalVorticityRow
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  fourierCurlCoefficient wave
    (wholeRestartVelocityEndpointCoefficient
      (accumulationBoundaryVelocityEndpoint initial elapsedBounded) wave)

/-- Every fixed vorticity row of the actual contact sequence lands at the
curl of the source-generated boundary velocity row.  No whole-state limit,
tail certificate, or post-interface target is supplied. -/
theorem contactPhysicalState_row_tendsto_accumulationBoundary
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (wave : IntegerWavevector) :
    Tendsto
      (fun index => (run initial index).contact.physicalState wave)
      atTop
      (nhds (accumulationBoundaryFormalVorticityRow
        initial elapsedBounded wave)) := by
  by_cases waveZero : wave = 0
  · subst wave
    have contactZero :
        (fun index => (run initial index).contact.physicalState 0) =
          fun _ : Nat => 0 := by
      funext index
      exact (run initial index).contact.physicalState_zero
    rw [contactZero]
    simp [accumulationBoundaryFormalVorticityRow,
      fourierCurlCoefficient]
  · let nonzeroWave : NonzeroIntegerWavevector := ⟨wave, waveZero⟩
    have velocityTendsto :=
      wholeRestartContactVelocityState_tendsto_accumulationBoundary
        initial elapsedBounded nonzeroWave
    have curlContinuous : Continuous (fourierCurlCoefficient wave) := by
      unfold fourierCurlCoefficient
      fun_prop
    have curlTendsto :=
      (curlContinuous.tendsto
          (WithLp.ofLp
            (accumulationBoundaryVelocityEndpoint
              initial elapsedBounded nonzeroWave)))
        |>.comp velocityTendsto
    convert curlTendsto using 1
    · funext index
      change
        (run initial index).contact.physicalState wave =
          fourierCurlCoefficient wave
            (biotSavartVelocityCoefficient wave
              ((run initial index).contact.physicalState wave))
      exact
        (fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse
          wave ((run initial index).contact.physicalState wave) waveZero
          ((run initial index).contact.transverse wave)).symm
    · apply congrArg nhds
      unfold accumulationBoundaryFormalVorticityRow
      rw [wholeRestartVelocityEndpointCoefficient_of_ne _ wave waveZero]

/-! ## Strong landing on every finite window -/

/-- The finite whole-vorticity state forced by the boundary row on one
literal Fourier inventory. -/
def accumulationBoundaryFiniteVorticityState
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (modes : Finset IntegerWavevector) :
    ComplexVorticityHilbertState :=
  finiteModeExtension modes fun wave =>
    accumulationBoundaryFormalVorticityRow
      initial elapsedBounded wave.1

/-- Every fixed finite Fourier observation converges strongly at the actual
interface `T`.  Hence no finite observer can carry the exhausted relation's
remaining failure. -/
theorem contactPhysicalState_fixedWindow_tendsto_accumulationBoundary
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (modes : Finset IntegerWavevector) :
    Tendsto
      (fun index =>
        complexSharpSupportProjection modes
          (run initial index).contact.physicalState)
      atTop
      (nhds (accumulationBoundaryFiniteVorticityState
        initial elapsedBounded modes)) := by
  let finiteBoundary : FiniteModeVorticityCarrier modes := fun wave =>
    accumulationBoundaryFormalVorticityRow
      initial elapsedBounded wave.1
  have restrictedTendsto :
      Tendsto
        (fun index => finiteModeRestriction modes
          (run initial index).contact.physicalState)
        atTop
        (nhds finiteBoundary) := by
    apply tendsto_pi_nhds.mpr
    intro wave
    exact contactPhysicalState_row_tendsto_accumulationBoundary
      initial elapsedBounded wave.1
  have extendedTendsto :=
    (finiteModeExtension modes).continuous.tendsto finiteBoundary
      |>.comp restrictedTendsto
  convert extendedTendsto using 1
  · funext index
    simpa only [Function.comp_apply] using
      (finiteModeExtension_restriction modes
        (run initial index).contact.physicalState).symm
  · rfl

end FullFrameBoundaryVorticityFixedWindowLanding
end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
