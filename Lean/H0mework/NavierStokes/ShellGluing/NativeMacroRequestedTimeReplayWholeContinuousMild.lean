import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayWholeMildAssembly
import H0mework.NavierStokes.Energy.WholeTangentEnergyTransport

/-!
# Requested-time actual whole continuous mild update

The requested-time whole assembly already gives the continuous whole path,
its exact strong space-time representative, and the genuine transverse
nonlinear row.  This module keeps those objects on the same physical
interval and generates the corresponding real-line heat/Duhamel update:

* the actual nonlinear row is extended by zero outside the interval;
* the assembled row is identified with its integrating-factor path;
* the nonlinear-minus-viscous row tangent is generated from that path;
* absolute continuity and the almost-everywhere derivative law follow from
  the domain-generic heat/Duhamel theorem.

No trajectory, coverage, continuation, forcing certificate, or target path
is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWholeContinuousMild

open scoped ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
open
  ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayCriticalClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWholeMildAssembly
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildAssembly

noncomputable section

/--
The actual transverse nonlinear row on the real line, canonically zero
outside the caller-requested physical interval.
-/
def requestedTimeReplayActualWaveNonlinearExtension
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (closure :
      GeneratedRequestedTimeReplayCriticalClosure replay)
    (wave : IntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  commonTimeZeroExtension requestedTime
    (transverseSpaceTimeNonlinearRow
      closure.transverseLimit wave)

theorem requestedTimeReplayActualWaveNonlinearExtension_intervalIntegrable
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (closure :
      GeneratedRequestedTimeReplayCriticalClosure replay)
    (wave : IntegerWavevector) :
    IntervalIntegrable
      (requestedTimeReplayActualWaveNonlinearExtension
        closure wave)
      volume 0 requestedTime :=
  commonTimeZeroExtension_intervalIntegrable
    requestedTime requestedTimePos.le
    (transverseSpaceTimeNonlinearRow
      closure.transverseLimit wave)

/--
The integrating-factor path determined by the source-owned initial row and
the exact requested-time transverse nonlinear row.
-/
def requestedTimeReplayActualWaveHeatDuhamelPath
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (closure :
      GeneratedRequestedTimeReplayCriticalClosure replay)
    (wave : IntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  heatDuhamelComplexCoordinatePath
    (commonTimeReplayInitialState lineage wave)
    (requestedTimeReplayActualWaveNonlinearExtension
      closure wave)
    (ν.coeff * integerWaveViscousMultiplier wave)
    0

/--
The requested whole assembly already carries the direct causal mild
identity with the exact source initial row and transverse nonlinear row.
-/
theorem requestedTimeReplayWholePath_mild_identity
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (closure :
      GeneratedRequestedTimeReplayCriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    (requestedTimeReplayWholeMildAssembly closure).wholePath
        time wave =
      fixedWaveHeatDuhamelValue
        requestedTime ν.coeff wave
        (commonTimeReplayInitialState lineage wave)
        (transverseSpaceTimeNonlinearRow
          closure.transverseLimit wave)
        time := by
  change
    assemblyWholeMildPath
        (requestedTimeReplayWholeMildAssemblyInput closure)
        time wave =
      _
  rw [assemblyWholeMildPath_apply,
    assemblyWholeMildState_apply,
    assemblyMildCoefficient_eq_rowPath
      (requestedTimeReplayWholeMildAssemblyInput closure)
      time wave waveNonzero]
  exact
    (requestedTimeReplayWholeMildAssemblyInput
      closure).row_mild_identity wave waveNonzero time

/--
Every nonzero coordinate of the assembled whole path is exactly its actual
real-line heat/Duhamel update on the requested interval.
-/
theorem requestedTimeReplayWholePath_wave_eq_actualWaveHeatDuhamelPath
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (closure :
      GeneratedRequestedTimeReplayCriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    (requestedTimeReplayWholeMildAssembly closure).wholePath
        time wave =
      requestedTimeReplayActualWaveHeatDuhamelPath
        closure wave time.1 := by
  have convertedIntegral :=
    commonTime_integral_Iic_eq_intervalIntegral
      requestedTime requestedTimePos.le time
      (fun earlier =>
        finiteStateVorticityHeatMultiplier
            ν.coeff (time.1 - earlier) wave •
          requestedTimeReplayActualWaveNonlinearExtension
            closure wave earlier)
  have convertedIntegral' :
      (∫ earlier in Iic time,
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - earlier.1) wave •
            transverseSpaceTimeNonlinearRow
              closure.transverseLimit wave earlier
          ∂(commonTimeMeasure requestedTime)) =
        ∫ earlier in (0 : ℝ)..time.1,
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - earlier) wave •
            requestedTimeReplayActualWaveNonlinearExtension
              closure wave earlier := by
    rw [← convertedIntegral]
    apply integral_congr_ae
    filter_upwards with earlier
    rw [requestedTimeReplayActualWaveNonlinearExtension,
      commonTimeZeroExtension_of_mem
        requestedTime
        (transverseSpaceTimeNonlinearRow
          closure.transverseLimit wave)
        earlier.1 earlier.property]
  rw [requestedTimeReplayWholePath_mild_identity
    closure wave waveNonzero time]
  unfold fixedWaveHeatDuhamelValue
  rw [convertedIntegral']
  unfold requestedTimeReplayActualWaveHeatDuhamelPath
  rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
  unfold finiteStateVorticityHeatMultiplier
  simp only [sub_zero]

/--
The actual nonlinear-minus-viscous tangent of one assembled nonzero row.
-/
def requestedTimeReplayActualWaveTangent
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (closure :
      GeneratedRequestedTimeReplayCriticalClosure replay)
    (wave : IntegerWavevector)
    (_waveNonzero : wave ≠ 0) :
    Icc (0 : ℝ) requestedTime → ComplexCoordinateVector :=
  fun time =>
    transverseSpaceTimeNonlinearRow
        closure.transverseLimit wave time -
      (ν.coeff * integerWaveViscousMultiplier wave) •
        (requestedTimeReplayWholeMildAssembly
          closure).wholePath time wave

theorem requestedTimeReplayActualWaveHeatDuhamelPath_absolutelyContinuous
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (closure :
      GeneratedRequestedTimeReplayCriticalClosure replay)
    (wave : IntegerWavevector) :
    AbsolutelyContinuousOnInterval
      (requestedTimeReplayActualWaveHeatDuhamelPath
        closure wave)
      0 requestedTime :=
  heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
    (commonTimeReplayInitialState lineage wave)
    (ν.coeff * integerWaveViscousMultiplier wave)
    0
    (requestedTimeReplayActualWaveNonlinearExtension_intervalIntegrable
      closure wave)
    (by simp)

/--
The actual real-line heat/Duhamel path differentiates almost everywhere to
the same nonlinear-minus-viscous tangent carried by the assembled whole
path.
-/
theorem requestedTimeReplayActualWaveHeatDuhamelPath_ae_hasDerivAt
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (closure :
      GeneratedRequestedTimeReplayCriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    ∀ᵐ actual : ℝ,
      actual ∈ uIcc (0 : ℝ) requestedTime →
        HasDerivAt
          (requestedTimeReplayActualWaveHeatDuhamelPath
            closure wave)
          (commonTimeZeroExtension requestedTime
            (requestedTimeReplayActualWaveTangent
              closure wave waveNonzero)
            actual)
          actual := by
  have generated :=
    heatDuhamelComplexCoordinatePath_ae_hasDerivAt
      (commonTimeReplayInitialState lineage wave)
      (ν.coeff * integerWaveViscousMultiplier wave)
      0
      (requestedTimeReplayActualWaveNonlinearExtension_intervalIntegrable
        closure wave)
      (by simp)
  filter_upwards [generated] with actual derivative
  intro actualMem
  have actualIcc :
      actual ∈ Icc (0 : ℝ) requestedTime := by
    simpa [uIcc_of_le requestedTimePos.le] using actualMem
  have pathEq :=
    requestedTimeReplayWholePath_wave_eq_actualWaveHeatDuhamelPath
      closure wave waveNonzero ⟨actual, actualIcc⟩
  rw [commonTimeZeroExtension_of_mem
    requestedTime
    (requestedTimeReplayActualWaveTangent
      closure wave waveNonzero)
    actual actualIcc]
  unfold requestedTimeReplayActualWaveTangent
  rw [pathEq]
  rw [requestedTimeReplayActualWaveNonlinearExtension,
    commonTimeZeroExtension_of_mem
      requestedTime
      (transverseSpaceTimeNonlinearRow
        closure.transverseLimit wave)
      actual actualIcc] at derivative
  simpa only [
    requestedTimeReplayActualWaveHeatDuhamelPath,
    requestedTimeReplayActualWaveNonlinearExtension] using
      derivative actualMem

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWholeContinuousMild
end NavierStokes
end SaturationMonoid
