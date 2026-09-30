import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2Runtime
import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalBudget
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinUniqueness
import H0mework.NavierStokes.ShellSources.PointwiseMassLimit
import H0mework.NavierStokes.WholeSpace.InfiniteFixedWaveResidualSilenceMildDuhamel
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeNonlinearNegativeOne
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeViscousNegativeOne
import H0mework.NavierStokes.Energy.WholeTangentEnergyTransport

/-!
# Terminal requested-time replay as one whole mild/Serrin path

A terminal requested-time replay has already generated one actual unforced
finite Galerkin trajectory on the complete requested interval, and its
punctured full-lattice residual is silent.  This file compiles that one
same-event terminal branch into the domain-generic whole mild/Serrin
consumer; it does not introduce a target path, continuation witness, or
caller-selected support.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalTerminalWholeContinuousMildSerrin

open scoped ENNReal Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplaySource
open ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Source
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Runtime
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalBudget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPointwiseMassLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveResidualSilenceMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

/-- At zero total frequency, the finite vorticity pair contribution is
forced silent by the transverse law already carried by the actual stage.
This is a carrier identity, not an extra terminal admission condition. -/
private theorem finitePairContribution_zero_of_output_zero
    (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state)
    (pair : StretchingPair)
    (outputZero : pair.1 + pair.2 = 0) :
    finiteStateVorticityNonlinearPairContribution state pair = 0 := by
  have secondWave : pair.2 = waveNeg pair.1 := by
    have reversed : pair.2 + pair.1 = 0 := by
      simpa [add_comm] using outputZero
    exact add_eq_zero_iff_eq_neg.mp reversed
  have stateDot :
      complexWavevector pair.2 ⬝ᵥ state pair.1 = 0 := by
    rw [secondWave, complexWavevector_waveNeg]
    simpa using congrArg Neg.neg (transverse pair.1)
  have velocityDot :
      complexWavevector pair.2 ⬝ᵥ
          finiteStateVelocityCoefficient state pair.1 = 0 := by
    rw [secondWave, complexWavevector_waveNeg, neg_dotProduct]
    simpa [finiteStateVelocityCoefficient] using
      congrArg Neg.neg
        (complexWavevector_dot_biotSavartVelocityCoefficient
          pair.1 (state pair.1))
  unfold finiteStateVorticityNonlinearPairContribution
  rw [stateDot, velocityDot]
  simp

/-- The complete finite nonlinear row at the zero frequency vanishes for a
transverse state.  This closes the one coordinate deliberately excluded from
the punctured terminal residual. -/
private theorem finiteNonlinearCoefficient_zero_of_transverse
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) :
    finiteStateVorticityNonlinearCoefficientAt modes state 0 = 0 := by
  unfold finiteStateVorticityNonlinearCoefficientAt
  apply Finset.sum_eq_zero
  intro first firstMem
  apply Finset.sum_eq_zero
  intro second secondMem
  by_cases outputZero : first + second = 0
  · rw [if_pos outputZero]
    exact finitePairContribution_zero_of_output_zero state transverse
      (first, second) outputZero
  · simp [outputZero]

private theorem terminalWholeNonlinear_zero
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    {time : ℝ}
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    wholeStateVorticityNonlinearCoefficientAt
        (run.terminal.trajectory time) 0 = 0 := by
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    run.terminal.modes (run.terminal.trajectory time)
    (run.terminal.physical time timeMem).2.1]
  exact finiteNonlinearCoefficient_zero_of_transverse run.terminal.modes
    (run.terminal.trajectory time)
    (run.terminal.physical time timeMem).2.2.1

/-- The terminal's punctured closure plus the generated zero-mode law gives
the genuine full-lattice residual equation on the same actual trajectory. -/
private theorem terminalWholeResidual_zero
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    {time : ℝ}
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime)
    (wave : IntegerWavevector) :
    wholeLatticeVorticityFourierPDEResidualAt ν.coeff
      (run.terminal.trajectory time)
      (finiteStateVorticityGenerator run.terminal.modes ν.coeff
        (run.terminal.trajectory time)) wave = 0 := by
  by_cases waveZero : wave = 0
  · subst wave
    have stateZero : run.terminal.trajectory time 0 = 0 :=
      (run.terminal.physical time timeMem).2.1 0 run.terminal.zero_not_mem
    simp [wholeLatticeVorticityFourierPDEResidualAt,
      wholeLatticeVorticityFourierTangentAt,
      finiteStateVorticityGenerator_apply,
      run.terminal.zero_not_mem, stateZero,
      terminalWholeNonlinear_zero run timeMem]
  · simpa only [GeneratedRequestedTimeReplayStage.wholeSpaceTimeResidual]
      using run.puncturedResidual_zero time timeMem wave waveZero

private theorem terminalTrajectoryContinuous
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    ContinuousOn run.terminal.trajectory (Icc (0 : ℝ) requestedTime) :=
  HasDerivAt.continuousOn
    (fun time timeMem => (run.terminal.physical time timeMem).1)

private theorem terminalTrajectoryTransverse
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    ∀ time ∈ Icc (0 : ℝ) requestedTime,
      WholeStateTransverse (run.terminal.trajectory time) :=
  fun time timeMem => (run.terminal.physical time timeMem).2.2.1

private def terminalWholePath
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) requestedTime)
      ComplexVorticityHilbertState :=
  wholeTrajectoryBoundedPath requestedTime run.terminal.trajectory
    (terminalTrajectoryContinuous run)

private def terminalStateLimit
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    SpaceTimeState requestedTime :=
  wholeTrajectorySpaceTimePath requestedTime run.terminal.trajectory
    (terminalTrajectoryContinuous run)

private def terminalTransverseLimit
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    TransverseSpaceTimeState requestedTime :=
  wholeTransverseTrajectorySpaceTimePath requestedTime run.terminal.trajectory
    (terminalTrajectoryContinuous run) (terminalTrajectoryTransverse run)

private theorem terminalTransverseLimit_inclusion
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    transverseSpaceTimeInclusion requestedTime
        (terminalTransverseLimit run) =
      terminalStateLimit run :=
  transverseSpaceTimeInclusion_wholeTransverseTrajectory
    requestedTime run.terminal.trajectory
    (terminalTrajectoryContinuous run) (terminalTrajectoryTransverse run)

private theorem terminalWholePath_toLp
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    BoundedContinuousFunction.toLp 2 (commonTimeMeasure requestedTime) ℂ
        (terminalWholePath run) = terminalStateLimit run :=
  rfl

private theorem terminalWholePath_initial
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    terminalWholePath run
        ⟨0, ⟨le_rfl, durationPos.le⟩⟩ =
      commonTimeReplayInitialState lineage := by
  exact run.terminal.initial

private theorem terminalWholePath_zero_row
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    (time : Icc (0 : ℝ) requestedTime) :
    terminalWholePath run time 0 = 0 := by
  change run.terminal.trajectory time.1 0 = 0
  exact (run.terminal.physical time.1 time.2).2.1 0
    run.terminal.zero_not_mem

private theorem terminalStateLimit_zero_row
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    fixedWaveSpaceTimeRestriction requestedTime 0
        (terminalStateLimit run) = 0 := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    fixedWaveSpaceTimeRestriction_coeFn requestedTime 0
      (terminalStateLimit run),
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime) ℂ
      (terminalWholePath run),
    MeasureTheory.Lp.coeFn_zero
      ComplexCoordinateVector 2 (commonTimeMeasure requestedTime)] with
      time rowEq pathEq zeroEq
  rw [rowEq, zeroEq, ← terminalWholePath_toLp run, pathEq]
  exact terminalWholePath_zero_row run time

private theorem terminalFixedWave_zero_of_not_mem
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ run.terminal.modes) :
    fixedWaveSpaceTimeRestriction requestedTime wave
        (terminalStateLimit run) = 0 := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    fixedWaveSpaceTimeRestriction_coeFn requestedTime wave
      (terminalStateLimit run),
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime) ℂ
      (terminalWholePath run),
    MeasureTheory.Lp.coeFn_zero
      ComplexCoordinateVector 2 (commonTimeMeasure requestedTime)] with
      time rowEq pathEq zeroEq
  rw [rowEq, zeroEq, ← terminalWholePath_toLp run, pathEq]
  exact (run.terminal.physical time.1 time.2).2.1 wave waveNotMem

private theorem terminalGradientDensity_eq_zero_of_not_mem
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ run.terminal.modes) :
    wholeSpaceTimeVorticityGradientDensity requestedTime
        (terminalStateLimit run) wave = 0 := by
  unfold wholeSpaceTimeVorticityGradientDensity
  rw [terminalFixedWave_zero_of_not_mem run wave waveNotMem]
  simp

private theorem terminalStateLimit_gradient_summable
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    Summable fun wave : IntegerWavevector =>
      wholeSpaceTimeVorticityGradientDensity requestedTime
        (terminalStateLimit run) wave := by
  apply summable_of_hasFiniteSupport
  exact run.terminal.modes.finite_toSet.subset fun wave waveSupport => by
    by_contra waveNotMem
    apply waveSupport
    simp [terminalGradientDensity_eq_zero_of_not_mem
      run wave waveNotMem]

/-- The terminal owns a finite continuous trajectory on the entire requested
interval. Its bound is read from that path, without a local-duration restriction. -/
private def terminalEnstrophyCeiling
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ} {durationPos : 0 < requestedTime}
    (run : GeneratedRequestedTimeReplayV2TerminalRun lineage requestedTime durationPos) : ℝ :=
  3 * ‖terminalWholePath run‖ ^ 2

private theorem terminalEnstrophyCeiling_nonneg
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ} {durationPos : 0 < requestedTime}
    (run : GeneratedRequestedTimeReplayV2TerminalRun lineage requestedTime durationPos) :
    0 ≤ terminalEnstrophyCeiling run := by
  unfold terminalEnstrophyCeiling
  positivity

private theorem terminalStateLimit_coefficientMass_ae_le
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      wholeVorticityEuclideanMass (terminalStateLimit run time) ≤
        terminalEnstrophyCeiling run := by
  filter_upwards [
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ (terminalWholePath run)] with time pathEq
  rw [← terminalWholePath_toLp run, pathEq]
  calc
    _ ≤ 3 * ‖terminalWholePath run time‖ ^ 2 :=
      wholeVorticityEuclideanMass_le_three_mul_norm_sq _
    _ ≤ terminalEnstrophyCeiling run := by
      unfold terminalEnstrophyCeiling
      gcongr
      exact (terminalWholePath run).norm_coe_le_norm time

private theorem terminalTransverseLimit_gradient_summable
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    Summable fun wave : IntegerWavevector =>
      wholeSpaceTimeVorticityGradientDensity requestedTime
        (transverseSpaceTimeInclusion requestedTime
          (terminalTransverseLimit run)) wave := by
  rw [terminalTransverseLimit_inclusion]
  exact terminalStateLimit_gradient_summable run

private theorem terminalTransverseLimit_coefficientMass_ae_le
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      wholeVorticityEuclideanMass
          ((terminalTransverseLimit run time).1) ≤
        terminalEnstrophyCeiling run := by
  filter_upwards [
    terminalStateLimit_coefficientMass_ae_le run,
    transverseSpaceTimeInclusion_coeFn requestedTime
      (terminalTransverseLimit run)] with time massBound inclusionEq
  rw [terminalTransverseLimit_inclusion run] at inclusionEq
  rw [inclusionEq] at massBound
  exact massBound

private noncomputable def terminalNonlinearNegativeOneForcing
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    SpaceTimeState requestedTime :=
  wholeSpaceTimeNonlinearNegativeOneState
    (terminalTransverseLimit run)
    (terminalTransverseLimit_gradient_summable run)
    (terminalEnstrophyCeiling_nonneg run)
    (terminalTransverseLimit_coefficientMass_ae_le run)

private theorem terminalPointwiseGradient_ae_summable
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            (terminalStateLimit run time wave) :=
  wholePointwiseGradientDensity_ae_summable requestedTime
    (terminalStateLimit run) (terminalStateLimit_gradient_summable run)

private noncomputable def terminalWholeNegativeOneTangent
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    SpaceTimeState requestedTime :=
  terminalNonlinearNegativeOneForcing run -
    wholeSpaceTimeViscousNegativeOneState ν.coeff
      (terminalStateLimit run)
      (terminalStateLimit_gradient_summable run)
      (terminalPointwiseGradient_ae_summable run)

private theorem terminalWholeNegativeOneTangent_eq_unforced_ae
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      terminalWholeNegativeOneTangent run time =
        wholeSpaceTimeNonlinearNegativeOneFunction
          (terminalTransverseLimit run) time -
          wholeSpaceTimeViscousNegativeOneFunction ν.coeff
            (terminalStateLimit run) time := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (terminalNonlinearNegativeOneForcing run)
      (wholeSpaceTimeViscousNegativeOneState ν.coeff
        (terminalStateLimit run)
        (terminalStateLimit_gradient_summable run)
        (terminalPointwiseGradient_ae_summable run)),
    wholeSpaceTimeNonlinearNegativeOneState_coeFn
      (terminalTransverseLimit run)
      (terminalTransverseLimit_gradient_summable run)
      (terminalEnstrophyCeiling_nonneg run)
      (terminalTransverseLimit_coefficientMass_ae_le run),
    wholeSpaceTimeViscousNegativeOneState_coeFn ν.coeff
      (terminalStateLimit run)
      (terminalStateLimit_gradient_summable run)
      (terminalPointwiseGradient_ae_summable run)] with
        time tangentEq nonlinearEq viscousEq
  rw [terminalWholeNegativeOneTangent, tangentEq]
  change wholeSpaceTimeNonlinearNegativeOneState
      (terminalTransverseLimit run)
      (terminalTransverseLimit_gradient_summable run)
      (terminalEnstrophyCeiling_nonneg run)
      (terminalTransverseLimit_coefficientMass_ae_le run) time -
      wholeSpaceTimeViscousNegativeOneState ν.coeff
        (terminalStateLimit run)
        (terminalStateLimit_gradient_summable run)
        (terminalPointwiseGradient_ae_summable run) time = _
  rw [nonlinearEq, viscousEq]

/-- Every nonzero terminal row has its real unforced heat/Duhamel law on the
same requested interval.  Retained and omitted rows are consumed by the
single full-residual theorem rather than a caller-supplied coverage split. -/
private theorem terminalWholePath_wave_mild
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    terminalWholePath run time wave =
      fixedWaveHeatDuhamelValue requestedTime ν.coeff wave
        (commonTimeReplayInitialState lineage wave)
        (transverseSpaceTimeNonlinearRow
          (terminalTransverseLimit run) wave) time := by
  have mild :=
    finiteSupportWave_eq_fixedWaveHeatDuhamelValue_of_wholeResidual_zero
      run.terminal.modes wave ν.coeff requestedTime durationPos
      run.terminal.trajectory
      (fun actual actualMem => (run.terminal.physical actual actualMem).1)
      (fun actual actualMem output outputNotMem =>
        (run.terminal.physical actual actualMem).2.1 output outputNotMem)
      (terminalTrajectoryTransverse run)
      (fun actual actualMem => terminalWholeResidual_zero run actualMem wave)
      time
  change run.terminal.trajectory time.1 wave = _
  simpa only [run.terminal.initial,
    terminalTransverseLimit,
    transverseSpaceTimeNonlinearRow_wholeTransverseTrajectory] using mild

private def terminalActualWaveNonlinearExtension
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    (wave : IntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  commonTimeZeroExtension requestedTime
    (transverseSpaceTimeNonlinearRow (terminalTransverseLimit run) wave)

private theorem terminalActualWaveNonlinearExtension_intervalIntegrable
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    (wave : IntegerWavevector) :
    IntervalIntegrable (terminalActualWaveNonlinearExtension run wave)
      volume 0 requestedTime :=
  commonTimeZeroExtension_intervalIntegrable requestedTime durationPos.le
    (transverseSpaceTimeNonlinearRow (terminalTransverseLimit run) wave)

private def terminalActualWaveHeatDuhamelPath
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    (wave : IntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  heatDuhamelComplexCoordinatePath
    (commonTimeReplayInitialState lineage wave)
    (terminalActualWaveNonlinearExtension run wave)
    (ν.coeff * integerWaveViscousMultiplier wave) 0

private theorem terminalWholePath_wave_eq_actualWaveHeatDuhamelPath
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    terminalWholePath run time wave =
      terminalActualWaveHeatDuhamelPath run wave time.1 := by
  have convertedIntegral :=
    commonTime_integral_Iic_eq_intervalIntegral
      requestedTime durationPos.le time
      (fun earlier =>
        finiteStateVorticityHeatMultiplier
            ν.coeff (time.1 - earlier) wave •
          terminalActualWaveNonlinearExtension run wave earlier)
  have convertedIntegral' :
      (∫ earlier in Iic time,
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - earlier.1) wave •
            transverseSpaceTimeNonlinearRow
              (terminalTransverseLimit run) wave earlier
          ∂(commonTimeMeasure requestedTime)) =
        ∫ earlier in (0 : ℝ)..time.1,
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - earlier) wave •
            terminalActualWaveNonlinearExtension run wave earlier := by
    rw [← convertedIntegral]
    apply integral_congr_ae
    filter_upwards with earlier
    rw [terminalActualWaveNonlinearExtension,
      commonTimeZeroExtension_of_mem requestedTime
        (transverseSpaceTimeNonlinearRow
          (terminalTransverseLimit run) wave)
        earlier.1 earlier.property]
  rw [terminalWholePath_wave_mild run wave time,
    fixedWaveHeatDuhamelValue, convertedIntegral']
  unfold terminalActualWaveHeatDuhamelPath
  rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
  unfold finiteStateVorticityHeatMultiplier
  simp only [sub_zero]

private def terminalActualWaveTangent
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    (wave : IntegerWavevector) :
    Icc (0 : ℝ) requestedTime → ComplexCoordinateVector :=
  fun time =>
    transverseSpaceTimeNonlinearRow
      (terminalTransverseLimit run) wave time -
      (ν.coeff * integerWaveViscousMultiplier wave) •
        terminalWholePath run time wave

private theorem terminalActualWaveHeatDuhamelPath_absolutelyContinuous
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    (wave : IntegerWavevector) :
    AbsolutelyContinuousOnInterval
      (terminalActualWaveHeatDuhamelPath run wave) 0 requestedTime :=
  heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
    (commonTimeReplayInitialState lineage wave)
    (ν.coeff * integerWaveViscousMultiplier wave) 0
    (terminalActualWaveNonlinearExtension_intervalIntegrable run wave)
    (by simp)

private theorem terminalActualWaveHeatDuhamelPath_ae_hasDerivAt
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    (wave : IntegerWavevector) :
    ∀ᵐ actual : ℝ,
      actual ∈ uIcc (0 : ℝ) requestedTime →
        HasDerivAt (terminalActualWaveHeatDuhamelPath run wave)
          (commonTimeZeroExtension requestedTime
            (terminalActualWaveTangent run wave) actual) actual := by
  have generic := heatDuhamelComplexCoordinatePath_ae_hasDerivAt
    (commonTimeReplayInitialState lineage wave)
    (ν.coeff * integerWaveViscousMultiplier wave) 0
    (terminalActualWaveNonlinearExtension_intervalIntegrable run wave)
    (by simp)
  filter_upwards [generic] with actual genericDeriv
  intro actualMem
  have intervalMem : actual ∈ Icc (0 : ℝ) requestedTime := by
    simpa [uIcc_of_le durationPos.le] using actualMem
  have pathEq := terminalWholePath_wave_eq_actualWaveHeatDuhamelPath
    run wave ⟨actual, intervalMem⟩
  have genericAt := genericDeriv actualMem
  dsimp only [terminalActualWaveNonlinearExtension] at genericAt
  change HasDerivAt (terminalActualWaveHeatDuhamelPath run wave) _ actual
    at genericAt
  rw [commonTimeZeroExtension_of_mem requestedTime
      (transverseSpaceTimeNonlinearRow
        (terminalTransverseLimit run) wave) actual intervalMem] at genericAt
  change HasDerivAt (terminalActualWaveHeatDuhamelPath run wave)
    (commonTimeZeroExtension requestedTime
      (terminalActualWaveTangent run wave) actual) actual
  rw [commonTimeZeroExtension_of_mem requestedTime
      (terminalActualWaveTangent run wave) actual intervalMem,
    terminalActualWaveTangent, pathEq]
  exact genericAt

private theorem terminalActualWaveTangent_eq_wholeNegativeOne_ae
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (terminalWholeNegativeOneTangent run time) wave =
        terminalActualWaveTangent run wave time := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (terminalNonlinearNegativeOneForcing run)
      (wholeSpaceTimeViscousNegativeOneState ν.coeff
        (terminalStateLimit run)
        (terminalStateLimit_gradient_summable run)
        (terminalPointwiseGradient_ae_summable run)),
    wholeSpaceTimeNonlinearNegativeOneState_unweighted_row_ae
      (terminalTransverseLimit run)
      (terminalTransverseLimit_gradient_summable run)
      (terminalEnstrophyCeiling_nonneg run)
      (terminalTransverseLimit_coefficientMass_ae_le run) wave waveNonzero,
    wholeSpaceTimeViscousNegativeOneState_unweighted_row_ae ν.coeff
      (terminalStateLimit run)
      (terminalStateLimit_gradient_summable run)
      (terminalPointwiseGradient_ae_summable run) wave,
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞)) (μ := commonTimeMeasure requestedTime) ℂ
      (terminalWholePath run)] with time tangentEq nonlinearEq viscousEq pathEq
  rw [terminalWholeNegativeOneTangent, tangentEq]
  change
    (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
        ((terminalNonlinearNegativeOneForcing run time) wave -
          (wholeSpaceTimeViscousNegativeOneState ν.coeff
            (terminalStateLimit run)
            (terminalStateLimit_gradient_summable run)
            (terminalPointwiseGradient_ae_summable run) time) wave) = _
  rw [smul_sub]
  have nonlinearEqComplex :
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (terminalNonlinearNegativeOneForcing run time) wave =
        transverseSpaceTimeNonlinearRow
          (terminalTransverseLimit run) wave time := by
    calc
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (terminalNonlinearNegativeOneForcing run time) wave =
          (Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
            (terminalNonlinearNegativeOneForcing run time) wave := by
              ext coordinate
              simp [Complex.real_smul]
      _ = _ := nonlinearEq
  have viscousEqComplex :
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (wholeSpaceTimeViscousNegativeOneState ν.coeff
            (terminalStateLimit run)
            (terminalStateLimit_gradient_summable run)
            (terminalPointwiseGradient_ae_summable run) time) wave =
        (ν.coeff * integerWaveViscousMultiplier wave) •
          terminalWholePath run time wave := by
    calc
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) • _ =
          (Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) • _ := by
            ext coordinate
            simp [Complex.real_smul]
      _ = (ν.coeff * integerWaveViscousMultiplier wave) •
          terminalStateLimit run time wave :=
        viscousEq
      _ = _ := by rw [← terminalWholePath_toLp run, pathEq]
  rw [nonlinearEqComplex, viscousEqComplex]
  rfl

private theorem terminalTransverseLimit_fourierReality_ae
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      FiniteStateFourierReality ((terminalTransverseLimit run time).1) := by
  filter_upwards [
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞)) (μ := commonTimeMeasure requestedTime) ℂ
      (wholeTransverseTrajectoryBoundedPath requestedTime
        run.terminal.trajectory
        (terminalTrajectoryContinuous run)
        (terminalTrajectoryTransverse run))] with time transverseEq
  unfold terminalTransverseLimit wholeTransverseTrajectorySpaceTimePath
  rw [transverseEq]
  exact (run.terminal.physical time.1 time.2).2.2.2

/-- A terminal requested-time replay compiles to one whole continuous mild
unforced receipt.  Its only input is the source-generated terminal run; the
full residual, mass ceiling, Fourier rows, and real-line updates are all
recovered on that same carrier. -/
noncomputable def generatedReplayV2TerminalWholeContinuousMildSerrinReceipt
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {durationPos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime durationPos) :
    WholeContinuousMildSerrinReceipt ν
      (commonTimeReplayInitialState lineage) requestedTime where
  requestedTimePos := durationPos
  stateLimit := terminalStateLimit run
  transverseLimit := terminalTransverseLimit run
  stateLimit_eq_transverse := terminalTransverseLimit_inclusion run
  wholePath := terminalWholePath run
  wholePath_toLp_eq_stateLimit := terminalWholePath_toLp run
  wholePath_initial := terminalWholePath_initial run
  wholePath_zero_row := terminalWholePath_zero_row run
  transverse_fourierReality_ae := terminalTransverseLimit_fourierReality_ae run
  gradient_summable := terminalStateLimit_gradient_summable run
  wholeTangent := terminalWholeNegativeOneTangent run
  wholeTangent_eq_unforced_ae := terminalWholeNegativeOneTangent_eq_unforced_ae run
  rowExtension wave _waveNonzero := terminalActualWaveHeatDuhamelPath run wave
  rowExtension_on_interval wave _waveNonzero time :=
    (terminalWholePath_wave_eq_actualWaveHeatDuhamelPath run wave time).symm
  rowTangent wave _waveNonzero := terminalActualWaveTangent run wave
  rowTangent_eq_unforced_ae wave _waveNonzero := by
    filter_upwards [
      transverseSpaceTimeNonlinearRow_coeFn
        (terminalTransverseLimit run) wave] with time nonlinearEq
    unfold terminalActualWaveTangent
    rw [nonlinearEq]
    exact congrArg (fun nonlinear => nonlinear -
      (ν.coeff * integerWaveViscousMultiplier wave) •
        terminalWholePath run time wave)
      (wholeStateVorticityBilinearCoefficientAt_self
        ((terminalTransverseLimit run time).1) wave).symm
  rowTangent_eq_wholeTangent_ae wave waveNonzero :=
    terminalActualWaveTangent_eq_wholeNegativeOne_ae run wave waveNonzero
  rowExtension_absolutelyContinuous wave _waveNonzero :=
    terminalActualWaveHeatDuhamelPath_absolutelyContinuous run wave
  rowExtension_ae_hasDerivAt wave _waveNonzero :=
    terminalActualWaveHeatDuhamelPath_ae_hasDerivAt run wave
  row_mild_identity wave _waveNonzero time :=
    terminalWholePath_wave_mild run wave time

/-- Existing local callers retain their original source-generated interval. -/
noncomputable def generatedLocalReplayV2TerminalWholeContinuousMildSerrinReceipt
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (run : GeneratedRequestedTimeReplayV2TerminalRun
      lineage (sourceOwnedLocalReplayV2Duration lineage) durationPos) :
    WholeContinuousMildSerrinReceipt ν (commonTimeReplayInitialState lineage)
      (sourceOwnedLocalReplayV2Duration lineage) :=
  generatedReplayV2TerminalWholeContinuousMildSerrinReceipt run

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalTerminalWholeContinuousMildSerrin
end NavierStokes
end SaturationMonoid
