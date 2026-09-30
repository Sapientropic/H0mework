import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalWholeMildAssembly
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
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWholeContinuousMild

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
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Source
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Runtime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalCriticalClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWholeMildAssembly
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildAssembly

noncomputable section

/--
The actual transverse nonlinear row on the real line, canonically zero
outside the caller-requested physical interval.
-/
def localReplayV2ActualWaveNonlinearExtension
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay)
    (wave : IntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  commonTimeZeroExtension (sourceOwnedLocalReplayV2Duration lineage)
    (transverseSpaceTimeNonlinearRow
      closure.transverseLimit wave)

theorem localReplayV2ActualWaveNonlinearExtension_intervalIntegrable
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay)
    (wave : IntegerWavevector) :
    IntervalIntegrable
      (localReplayV2ActualWaveNonlinearExtension
        closure wave)
      volume 0 (sourceOwnedLocalReplayV2Duration lineage) :=
  commonTimeZeroExtension_intervalIntegrable
    (sourceOwnedLocalReplayV2Duration lineage) durationPos.le
    (transverseSpaceTimeNonlinearRow
      closure.transverseLimit wave)

/--
The integrating-factor path determined by the source-owned initial row and
the exact requested-time transverse nonlinear row.
-/
def localReplayV2ActualWaveHeatDuhamelPath
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay)
    (wave : IntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  heatDuhamelComplexCoordinatePath
    (commonTimeReplayInitialState lineage wave)
    (localReplayV2ActualWaveNonlinearExtension
      closure wave)
    (ν.coeff * integerWaveViscousMultiplier wave)
    0

/--
The requested whole assembly already carries the direct causal mild
identity with the exact source initial row and transverse nonlinear row.
-/
theorem localReplayV2WholePath_mild_identity
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) :
    (localReplayV2WholeMildAssembly closure).wholePath
        time wave =
      fixedWaveHeatDuhamelValue
        (sourceOwnedLocalReplayV2Duration lineage) ν.coeff wave
        (commonTimeReplayInitialState lineage wave)
        (transverseSpaceTimeNonlinearRow
          closure.transverseLimit wave)
        time := by
  change
    assemblyWholeMildPath
        (localReplayV2WholeMildAssemblyInput closure)
        time wave =
      _
  rw [assemblyWholeMildPath_apply,
    assemblyWholeMildState_apply,
    assemblyMildCoefficient_eq_rowPath
      (localReplayV2WholeMildAssemblyInput closure)
      time wave waveNonzero]
  exact
    (localReplayV2WholeMildAssemblyInput
      closure).row_mild_identity wave waveNonzero time

/--
Every nonzero coordinate of the assembled whole path is exactly its actual
real-line heat/Duhamel update on the requested interval.
-/
theorem localReplayV2WholePath_wave_eq_actualWaveHeatDuhamelPath
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) :
    (localReplayV2WholeMildAssembly closure).wholePath
        time wave =
      localReplayV2ActualWaveHeatDuhamelPath
        closure wave time.1 := by
  have convertedIntegral :=
    commonTime_integral_Iic_eq_intervalIntegral
      (sourceOwnedLocalReplayV2Duration lineage) durationPos.le time
      (fun earlier =>
        finiteStateVorticityHeatMultiplier
            ν.coeff (time.1 - earlier) wave •
          localReplayV2ActualWaveNonlinearExtension
            closure wave earlier)
  have convertedIntegral' :
      (∫ earlier in Iic time,
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - earlier.1) wave •
            transverseSpaceTimeNonlinearRow
              closure.transverseLimit wave earlier
          ∂(commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage))) =
        ∫ earlier in (0 : ℝ)..time.1,
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - earlier) wave •
            localReplayV2ActualWaveNonlinearExtension
              closure wave earlier := by
    rw [← convertedIntegral]
    apply integral_congr_ae
    filter_upwards with earlier
    rw [localReplayV2ActualWaveNonlinearExtension,
      commonTimeZeroExtension_of_mem
        (sourceOwnedLocalReplayV2Duration lineage)
        (transverseSpaceTimeNonlinearRow
          closure.transverseLimit wave)
        earlier.1 earlier.property]
  rw [localReplayV2WholePath_mild_identity
    closure wave waveNonzero time]
  unfold fixedWaveHeatDuhamelValue
  rw [convertedIntegral']
  unfold localReplayV2ActualWaveHeatDuhamelPath
  rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
  unfold finiteStateVorticityHeatMultiplier
  simp only [sub_zero]

/--
The actual nonlinear-minus-viscous tangent of one assembled nonzero row.
-/
def localReplayV2ActualWaveTangent
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay)
    (wave : IntegerWavevector)
    (_waveNonzero : wave ≠ 0) :
    Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage) → ComplexCoordinateVector :=
  fun time =>
    transverseSpaceTimeNonlinearRow
        closure.transverseLimit wave time -
      (ν.coeff * integerWaveViscousMultiplier wave) •
        (localReplayV2WholeMildAssembly
          closure).wholePath time wave

theorem localReplayV2ActualWaveHeatDuhamelPath_absolutelyContinuous
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay)
    (wave : IntegerWavevector) :
    AbsolutelyContinuousOnInterval
      (localReplayV2ActualWaveHeatDuhamelPath
        closure wave)
      0 (sourceOwnedLocalReplayV2Duration lineage) :=
  heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
    (commonTimeReplayInitialState lineage wave)
    (ν.coeff * integerWaveViscousMultiplier wave)
    0
    (localReplayV2ActualWaveNonlinearExtension_intervalIntegrable
      closure wave)
    (by simp)

/--
The actual real-line heat/Duhamel path differentiates almost everywhere to
the same nonlinear-minus-viscous tangent carried by the assembled whole
path.
-/
theorem localReplayV2ActualWaveHeatDuhamelPath_ae_hasDerivAt
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    ∀ᵐ actual : ℝ,
      actual ∈ uIcc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage) →
        HasDerivAt
          (localReplayV2ActualWaveHeatDuhamelPath
            closure wave)
          (commonTimeZeroExtension (sourceOwnedLocalReplayV2Duration lineage)
            (localReplayV2ActualWaveTangent
              closure wave waveNonzero)
            actual)
          actual := by
  have generated :=
    heatDuhamelComplexCoordinatePath_ae_hasDerivAt
      (commonTimeReplayInitialState lineage wave)
      (ν.coeff * integerWaveViscousMultiplier wave)
      0
      (localReplayV2ActualWaveNonlinearExtension_intervalIntegrable
        closure wave)
      (by simp)
  filter_upwards [generated] with actual derivative
  intro actualMem
  have actualIcc :
      actual ∈ Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage) := by
    simpa [uIcc_of_le durationPos.le] using actualMem
  have pathEq :=
    localReplayV2WholePath_wave_eq_actualWaveHeatDuhamelPath
      closure wave waveNonzero ⟨actual, actualIcc⟩
  rw [commonTimeZeroExtension_of_mem
    (sourceOwnedLocalReplayV2Duration lineage)
    (localReplayV2ActualWaveTangent
      closure wave waveNonzero)
    actual actualIcc]
  unfold localReplayV2ActualWaveTangent
  rw [pathEq]
  rw [localReplayV2ActualWaveNonlinearExtension,
    commonTimeZeroExtension_of_mem
      (sourceOwnedLocalReplayV2Duration lineage)
      (transverseSpaceTimeNonlinearRow
        closure.transverseLimit wave)
      actual actualIcc] at derivative
  simpa only [
    localReplayV2ActualWaveHeatDuhamelPath,
    localReplayV2ActualWaveNonlinearExtension] using
      derivative actualMem

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWholeContinuousMild
end NavierStokes
end SaturationMonoid
