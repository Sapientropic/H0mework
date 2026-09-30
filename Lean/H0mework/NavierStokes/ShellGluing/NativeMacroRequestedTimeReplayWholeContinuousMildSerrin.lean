import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayRealityClosure
import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayWholeContinuousMild
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
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWholeContinuousMildSerrin

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
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayCriticalClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayMildForcing
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayRealityClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWholeMildAssembly
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWholeContinuousMild
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
noncomputable def requestedTimeReplayWholeNegativeOneTangent
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
      GeneratedRequestedTimeReplayCriticalClosure replay) :
    SpaceTimeState requestedTime :=
  negativeOneForcing closure -
    wholeSpaceTimeViscousNegativeOneState
      ν.coeff closure.weakClosure.stateLimit
      closure.gradient_summable
      (wholePointwiseGradientDensity_ae_summable
        requestedTime closure.weakClosure.stateLimit
        closure.gradient_summable)

/--
The weighted requested-time tangent is represented almost everywhere by
the actual whole nonlinear-minus-viscous function.
-/
theorem requestedTimeReplayWholeNegativeOneTangent_eq_unforced_ae
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
      GeneratedRequestedTimeReplayCriticalClosure replay) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      requestedTimeReplayWholeNegativeOneTangent closure time =
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
          requestedTime closure.weakClosure.stateLimit
          closure.gradient_summable)),
    wholeSpaceTimeNonlinearNegativeOneState_coeFn
      closure.transverseLimit
      (requestedReplayTransverseGradient_summable closure)
      (criticalCoefficientEnstrophyCeiling_nonneg
        ν (1 / 2 : ℝ))
      (requestedReplayTransverseCoefficientMass_ae_le closure),
    wholeSpaceTimeViscousNegativeOneState_coeFn
      ν.coeff closure.weakClosure.stateLimit
      closure.gradient_summable
      (wholePointwiseGradientDensity_ae_summable
        requestedTime closure.weakClosure.stateLimit
        closure.gradient_summable)] with
      time tangentEq nonlinearEq viscousEq
  have nonlinearEq' :
      negativeOneForcing closure time =
        wholeSpaceTimeNonlinearNegativeOneFunction
          closure.transverseLimit time := by
    simpa only [negativeOneForcing] using nonlinearEq
  rw [requestedTimeReplayWholeNegativeOneTangent, tangentEq]
  change
    negativeOneForcing closure time -
        wholeSpaceTimeViscousNegativeOneState
          ν.coeff closure.weakClosure.stateLimit
          closure.gradient_summable
          (wholePointwiseGradientDensity_ae_summable
            requestedTime closure.weakClosure.stateLimit
            closure.gradient_summable) time =
      _
  rw [nonlinearEq', viscousEq]

/--
Every nonzero actual replay row is the unweighted coordinate of the same
whole negative-one tangent.
-/
theorem requestedTimeReplayActualWaveTangent_eq_wholeNegativeOneTangent_ae
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
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (requestedTimeReplayWholeNegativeOneTangent
            closure time) wave =
        requestedTimeReplayActualWaveTangent
          closure wave waveNonzero time := by
  have pointwiseGradient :=
    wholePointwiseGradientDensity_ae_summable
      requestedTime closure.weakClosure.stateLimit
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
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (requestedTimeReplayWholeMildAssembly closure).wholePath] with
      time tangentEq nonlinearEq viscousEq pathEq
  rw [requestedTimeReplayWholeNegativeOneTangent, tangentEq]
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
  unfold requestedTimeReplayActualWaveTangent
  rw [← requestedTimeReplayWholeMildAssembly_toLp_eq closure,
    pathEq]

/--
The requested-time infinite closure itself generates one whole continuous
mild/Serrin receipt.  The dependent initial-state index locks the receipt
to the exact source-owned initial state.
-/
noncomputable def requestedReplayWholeContinuousMildSerrinReceipt
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
      GeneratedRequestedTimeReplayCriticalClosure replay) :
    WholeContinuousMildSerrinReceipt
      ν (commonTimeReplayInitialState lineage) requestedTime where
  requestedTimePos :=
    requestedTimePos
  stateLimit :=
    closure.weakClosure.stateLimit
  transverseLimit :=
    closure.transverseLimit
  stateLimit_eq_transverse :=
    closure.inclusion_eq
  wholePath :=
    (requestedTimeReplayWholeMildAssembly closure).wholePath
  wholePath_toLp_eq_stateLimit :=
    requestedTimeReplayWholeMildAssembly_toLp_eq closure
  wholePath_initial :=
    (requestedTimeReplayWholeMildAssembly closure).wholePath_initial
  wholePath_zero_row :=
    fun time => by
      change
        assemblyWholeMildPath
            (requestedTimeReplayWholeMildAssemblyInput closure)
            time 0 =
          0
      exact
        assemblyWholeMildPath_zero_row
          (requestedTimeReplayWholeMildAssemblyInput closure) time
  transverse_fourierReality_ae :=
    requestedTimeReplayTransverseLimit_fourierReality_ae closure
  gradient_summable :=
    closure.gradient_summable
  wholeTangent :=
    requestedTimeReplayWholeNegativeOneTangent closure
  wholeTangent_eq_unforced_ae :=
    requestedTimeReplayWholeNegativeOneTangent_eq_unforced_ae
      closure
  rowExtension wave waveNonzero :=
    requestedTimeReplayActualWaveHeatDuhamelPath closure wave
  rowExtension_on_interval wave waveNonzero time :=
    (requestedTimeReplayWholePath_wave_eq_actualWaveHeatDuhamelPath
      closure wave waveNonzero time).symm
  rowTangent wave waveNonzero :=
    requestedTimeReplayActualWaveTangent
      closure wave waveNonzero
  rowTangent_eq_unforced_ae wave waveNonzero := by
    filter_upwards [
      transverseSpaceTimeNonlinearRow_coeFn
        closure.transverseLimit wave] with time nonlinearEq
    unfold requestedTimeReplayActualWaveTangent
    rw [nonlinearEq]
    exact congrArg
      (fun nonlinear =>
        nonlinear -
          (ν.coeff * integerWaveViscousMultiplier wave) •
            (requestedTimeReplayWholeMildAssembly
              closure).wholePath time wave)
      (wholeStateVorticityBilinearCoefficientAt_self
        (closure.transverseLimit time).1 wave).symm
  rowTangent_eq_wholeTangent_ae wave waveNonzero :=
    requestedTimeReplayActualWaveTangent_eq_wholeNegativeOneTangent_ae
      closure wave waveNonzero
  rowExtension_absolutelyContinuous wave waveNonzero :=
    requestedTimeReplayActualWaveHeatDuhamelPath_absolutelyContinuous
      closure wave
  rowExtension_ae_hasDerivAt wave waveNonzero :=
    requestedTimeReplayActualWaveHeatDuhamelPath_ae_hasDerivAt
      closure wave waveNonzero
  row_mild_identity wave waveNonzero time :=
    requestedTimeReplayWholePath_mild_identity
      closure wave waveNonzero time

/--
Source-facing compiler: the actual infinite requested-time replay first
generates its critical closure and then the complete whole mild/Serrin
receipt on that same horizon.
-/
noncomputable def generatedRequestedReplayWholeContinuousMildSerrinReceipt
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos) :
    WholeContinuousMildSerrinReceipt
      ν (commonTimeReplayInitialState lineage) requestedTime :=
  requestedReplayWholeContinuousMildSerrinReceipt
    (generatedRequestedTimeReplayCriticalClosure replay)

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWholeContinuousMildSerrin
end NavierStokes
end SaturationMonoid
