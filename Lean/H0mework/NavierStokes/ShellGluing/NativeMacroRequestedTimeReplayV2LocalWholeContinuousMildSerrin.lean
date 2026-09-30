import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalRealityClosure
import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalWholeContinuousMild
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinUniqueness

/-!
# Requested-time replay as one whole mild/Serrin receipt

The actual infinite requested-time replay generates every datum of the
domain-generic whole mild/Serrin uniqueness consumer.  This module performs
the final same-carrier compilation:

```text
actual requested-time residual replay
→ strong whole state + transverse nonlinear state
→ continuous whole mild path
→ generated Fourier reality + whole gradient budget
→ actual real-line unforced row update.
```

No forcing, reality, target path, continuation witness, coverage family,
cutoff, caller smallness, or energy-payment hypothesis is introduced.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWholeContinuousMildSerrin

open scoped ENNReal Topology

open Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open
  ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open
  ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
open
  ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplaySource
open
  ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Source
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Runtime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalCriticalClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalMildForcing
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalRealityClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWholeMildAssembly
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWholeContinuousMild
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildAssembly
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

/--
The complete weighted whole tangent of the requested-time replay.  Both
summands live on its actual `L²_t H⁻¹_x` carrier.
-/
noncomputable def localReplayV2WholeNegativeOneTangent
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay) :
    SpaceTimeState (sourceOwnedLocalReplayV2Duration lineage) :=
  negativeOneForcing closure -
    wholeSpaceTimeViscousNegativeOneState
      ν.coeff closure.weakClosure.stateLimit
      closure.gradient_summable
      (wholePointwiseGradientDensity_ae_summable
        (sourceOwnedLocalReplayV2Duration lineage) closure.weakClosure.stateLimit
        closure.gradient_summable)

/--
The weighted requested-time tangent is represented almost everywhere by
the actual whole nonlinear-minus-viscous function.
-/
theorem localReplayV2WholeNegativeOneTangent_eq_unforced_ae
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay) :
    ∀ᵐ time ∂(commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)),
      localReplayV2WholeNegativeOneTangent closure time =
        wholeSpaceTimeNonlinearNegativeOneFunction
            closure.transverseLimit time -
          wholeSpaceTimeViscousNegativeOneFunction
            ν.coeff closure.weakClosure.stateLimit time := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (negativeOneForcing closure)
      (wholeSpaceTimeViscousNegativeOneState
        ν.coeff closure.weakClosure.stateLimit
        closure.gradient_summable
        (wholePointwiseGradientDensity_ae_summable
          (sourceOwnedLocalReplayV2Duration lineage) closure.weakClosure.stateLimit
          closure.gradient_summable)),
    wholeSpaceTimeNonlinearNegativeOneState_coeFn
      closure.transverseLimit
      (localReplayV2TransverseGradient_summable closure)
      (sourceOwnedLocalEnstrophyCeiling_pos
        (lineageReceiptModes lineage 0)
        (commonTimeReplayInitialState lineage)).le
      (localReplayV2TransverseCoefficientMass_ae_le closure),
    wholeSpaceTimeViscousNegativeOneState_coeFn
      ν.coeff closure.weakClosure.stateLimit
      closure.gradient_summable
      (wholePointwiseGradientDensity_ae_summable
        (sourceOwnedLocalReplayV2Duration lineage) closure.weakClosure.stateLimit
        closure.gradient_summable)] with
      time tangentEq nonlinearEq viscousEq
  have nonlinearEq' :
      negativeOneForcing closure time =
        wholeSpaceTimeNonlinearNegativeOneFunction
          closure.transverseLimit time := by
    simpa only [negativeOneForcing] using nonlinearEq
  rw [localReplayV2WholeNegativeOneTangent, tangentEq]
  change
    negativeOneForcing closure time -
        wholeSpaceTimeViscousNegativeOneState
          ν.coeff closure.weakClosure.stateLimit
          closure.gradient_summable
          (wholePointwiseGradientDensity_ae_summable
            (sourceOwnedLocalReplayV2Duration lineage) closure.weakClosure.stateLimit
            closure.gradient_summable) time =
      _
  rw [nonlinearEq', viscousEq]

/--
Every nonzero actual replay row is the unweighted coordinate of the same
whole negative-one tangent.
-/
theorem localReplayV2ActualWaveTangent_eq_wholeNegativeOneTangent_ae
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
    ∀ᵐ time ∂(commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)),
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (localReplayV2WholeNegativeOneTangent
            closure time) wave =
        localReplayV2ActualWaveTangent
          closure wave waveNonzero time := by
  have pointwiseGradient :=
    wholePointwiseGradientDensity_ae_summable
      (sourceOwnedLocalReplayV2Duration lineage) closure.weakClosure.stateLimit
      closure.gradient_summable
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (negativeOneForcing closure)
      (wholeSpaceTimeViscousNegativeOneState
        ν.coeff closure.weakClosure.stateLimit
        closure.gradient_summable pointwiseGradient),
    negativeOneForcing_unweighted_row_ae
      closure wave waveNonzero,
    wholeSpaceTimeViscousNegativeOneState_unweighted_row_ae
      ν.coeff closure.weakClosure.stateLimit
      closure.gradient_summable pointwiseGradient wave,
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage))
      ℂ
      (localReplayV2WholeMildAssembly closure).wholePath] with
      time tangentEq nonlinearEq viscousEq pathEq
  rw [localReplayV2WholeNegativeOneTangent, tangentEq]
  change
    (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
        ((negativeOneForcing closure time) wave -
          (wholeSpaceTimeViscousNegativeOneState
            ν.coeff closure.weakClosure.stateLimit
            closure.gradient_summable pointwiseGradient time) wave) =
      _
  have nonlinearEqComplex :
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (negativeOneForcing closure time) wave =
        transverseSpaceTimeNonlinearRow
          closure.transverseLimit wave time := by
    calc
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (negativeOneForcing closure time) wave =
          (Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
            (negativeOneForcing closure time) wave := by
        ext coordinate
        simp [Complex.real_smul]
      _ = _ := nonlinearEq
  have viscousEqComplex :
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (wholeSpaceTimeViscousNegativeOneState
            ν.coeff closure.weakClosure.stateLimit
            closure.gradient_summable pointwiseGradient time) wave =
        (ν.coeff * integerWaveViscousMultiplier wave) •
          closure.weakClosure.stateLimit time wave := by
    calc
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (wholeSpaceTimeViscousNegativeOneState
            ν.coeff closure.weakClosure.stateLimit
            closure.gradient_summable pointwiseGradient time) wave =
          (Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
            (wholeSpaceTimeViscousNegativeOneState
              ν.coeff closure.weakClosure.stateLimit
              closure.gradient_summable pointwiseGradient time) wave := by
        ext coordinate
        simp [Complex.real_smul]
      _ = _ := viscousEq
  rw [smul_sub, nonlinearEqComplex, viscousEqComplex]
  unfold localReplayV2ActualWaveTangent
  rw [← localReplayV2WholeMildAssembly_toLp_eq closure,
    pathEq]

/--
The requested-time infinite closure itself generates one whole continuous
mild/Serrin receipt.  The dependent initial-state index locks the receipt
to the exact source-owned initial state.
-/
noncomputable def localReplayV2WholeContinuousMildSerrinReceipt
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay) :
    WholeContinuousMildSerrinReceipt
      ν (commonTimeReplayInitialState lineage) (sourceOwnedLocalReplayV2Duration lineage) where
  requestedTimePos :=
    durationPos
  stateLimit :=
    closure.weakClosure.stateLimit
  transverseLimit :=
    closure.transverseLimit
  stateLimit_eq_transverse :=
    closure.inclusion_eq
  wholePath :=
    (localReplayV2WholeMildAssembly closure).wholePath
  wholePath_toLp_eq_stateLimit :=
    localReplayV2WholeMildAssembly_toLp_eq closure
  wholePath_initial :=
    (localReplayV2WholeMildAssembly closure).wholePath_initial
  wholePath_zero_row :=
    fun time => by
      change
        assemblyWholeMildPath
            (localReplayV2WholeMildAssemblyInput closure)
            time 0 =
          0
      exact
        assemblyWholeMildPath_zero_row
          (localReplayV2WholeMildAssemblyInput closure) time
  transverse_fourierReality_ae :=
    localReplayV2TransverseLimit_fourierReality_ae closure
  gradient_summable :=
    closure.gradient_summable
  wholeTangent :=
    localReplayV2WholeNegativeOneTangent closure
  wholeTangent_eq_unforced_ae :=
    localReplayV2WholeNegativeOneTangent_eq_unforced_ae
      closure
  rowExtension wave waveNonzero :=
    localReplayV2ActualWaveHeatDuhamelPath closure wave
  rowExtension_on_interval wave waveNonzero time :=
    (localReplayV2WholePath_wave_eq_actualWaveHeatDuhamelPath
      closure wave waveNonzero time).symm
  rowTangent wave waveNonzero :=
    localReplayV2ActualWaveTangent
      closure wave waveNonzero
  rowTangent_eq_unforced_ae wave waveNonzero := by
    filter_upwards [
      transverseSpaceTimeNonlinearRow_coeFn
        closure.transverseLimit wave] with time nonlinearEq
    unfold localReplayV2ActualWaveTangent
    rw [nonlinearEq]
    exact congrArg
      (fun nonlinear =>
        nonlinear -
          (ν.coeff * integerWaveViscousMultiplier wave) •
            (localReplayV2WholeMildAssembly
              closure).wholePath time wave)
      (wholeStateVorticityBilinearCoefficientAt_self
        (closure.transverseLimit time).1 wave).symm
  rowTangent_eq_wholeTangent_ae wave waveNonzero :=
    localReplayV2ActualWaveTangent_eq_wholeNegativeOneTangent_ae
      closure wave waveNonzero
  rowExtension_absolutelyContinuous wave waveNonzero :=
    localReplayV2ActualWaveHeatDuhamelPath_absolutelyContinuous
      closure wave
  rowExtension_ae_hasDerivAt wave waveNonzero :=
    localReplayV2ActualWaveHeatDuhamelPath_ae_hasDerivAt
      closure wave waveNonzero
  row_mild_identity wave waveNonzero time :=
    localReplayV2WholePath_mild_identity
      closure wave waveNonzero time

/--
Source-facing compiler: the actual infinite requested-time replay first
generates its critical closure and then the complete whole mild/Serrin
receipt on that same horizon.
-/
noncomputable def generatedLocalReplayV2WholeContinuousMildSerrinReceipt
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos) :
  WholeContinuousMildSerrinReceipt
      ν (commonTimeReplayInitialState lineage) (sourceOwnedLocalReplayV2Duration lineage) :=
  localReplayV2WholeContinuousMildSerrinReceipt
    (generatedLocalReplayV2CriticalClosure replay)

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWholeContinuousMildSerrin
end NavierStokes
end SaturationMonoid
