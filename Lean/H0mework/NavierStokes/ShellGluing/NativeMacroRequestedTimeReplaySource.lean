import H0mework.NavierStokes.ShellGluing.NativeMacroWholeSpaceTimeReplay

/-!
# Source-generated replay on an arbitrary requested time interval

The original common-time replay uses the duration of the first physical
receipt.  This module keeps the same source-owned initial state and support
grammar, but generates the finite Galerkin trajectory internally on any
caller-requested positive interval.

The caller supplies only the interval.  Trajectories, refined supports,
nonzero residual witnesses, and response branches are all generated inside
the source.  `none` has exact whole-space-time residual semantics.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplaySource

open Set
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCommonTimeExistence
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateSupportLift
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay

noncomputable section

/--
One source-generated replay stage on a caller-requested positive interval.
The trajectory is output data, never an input to the public producer.
-/
structure GeneratedRequestedTimeReplayStage
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ) where
  modes : Finset IntegerWavevector
  initialModes_subset :
    lineageReceiptModes lineage 0 ⊆ modes
  zero_not_mem : (0 : IntegerWavevector) ∉ modes
  waveNeg_mem :
    ∀ wave, wave ∈ modes → waveNeg wave ∈ modes
  trajectory : ℝ → ComplexVorticityHilbertState
  initial :
    trajectory 0 = commonTimeReplayInitialState lineage
  physical :
    ∀ time ∈ Icc (0 : ℝ) requestedTime,
      HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory time))
          time ∧
        (∀ wave, wave ∉ modes → trajectory time wave = 0) ∧
        (∀ wave,
          complexWavevector wave ⬝ᵥ trajectory time wave = 0) ∧
        FiniteStateFourierReality (trajectory time)

namespace GeneratedRequestedTimeReplayStage

/--
Internal constructor from a source-owned support.  It invokes the actual
finite Galerkin existence theorem and does not accept a trajectory.
-/
private noncomputable def ofModes
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (modes : Finset IntegerWavevector)
    (initialModesSubset :
      lineageReceiptModes lineage 0 ⊆ modes)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes) :
    GeneratedRequestedTimeReplayStage lineage requestedTime := by
  have initialSupported :
      ∀ wave, wave ∉ modes →
        commonTimeReplayInitialState lineage wave = 0 :=
    finitePhysicalState_supported_on_superSupport
      initialModesSubset
      (commonTimeReplayInitialState_supported lineage)
  have initialTransverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ
            commonTimeReplayInitialState lineage wave =
          0 := by
    intro wave _waveMem
    exact commonTimeReplayInitialState_transverse lineage wave
  have initialReality :
      FiniteStateFourierReality
        (commonTimeReplayInitialState lineage) :=
    commonTimeReplayInitialState_reality lineage
  have initialSmall :
      criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              modes (commonTimeReplayInitialState lineage) ≤
        ν.coeff ^ 2 * (2 * Real.pi) ^ 2 :=
    GeneratedCommonTimeReplayStage.replayInitialSmall_on_modes
      initialSubcritical modes
  let trajectoryResult :=
    exists_finitePhysicalTrajectory_on_Icc_of_criticalSmall
      modes zeroNotMem negClosed
      ν.coeff ν.coeff_pos
      (commonTimeReplayInitialState lineage)
      initialSupported initialTransverse initialReality
      initialSmall requestedTime requestedTimePos
  let trajectory : ℝ → ComplexVorticityHilbertState :=
    Classical.choose trajectoryResult
  have trajectorySpec :=
    Classical.choose_spec trajectoryResult
  exact
    { modes := modes
      initialModes_subset := initialModesSubset
      zero_not_mem := zeroNotMem
      waveNeg_mem := negClosed
      trajectory := trajectory
      initial := trajectorySpec.1
      physical := trajectorySpec.2 }

/-- Whole-lattice residual of the actual requested-time stage. -/
def wholeSpaceTimeResidual
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    (time : ℝ)
    (wave : IntegerWavevector) :
    ComplexCoordinateVector :=
  wholeLatticeVorticityFourierPDEResidualAt
    ν.coeff
    (stage.trajectory time)
    (finiteStateVorticityGenerator
      stage.modes ν.coeff (stage.trajectory time))
    wave

/-- Retained rows satisfy the exact whole equation throughout the interval. -/
theorem wholeSpaceTimeResidual_eq_zero_of_mem
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    {time : ℝ}
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ stage.modes) :
    wholeSpaceTimeResidual stage time wave = 0 := by
  have nonlinearEq :
      wholeStateVorticityNonlinearCoefficientAt
          (stage.trajectory time) wave =
        finiteStateVorticityNonlinearCoefficientAt
          stage.modes (stage.trajectory time) wave :=
    wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
      stage.modes (stage.trajectory time)
      (stage.physical time timeMem).2.1 wave
  simp [wholeSpaceTimeResidual,
    wholeLatticeVorticityFourierPDEResidualAt,
    wholeLatticeVorticityFourierTangentAt,
    finiteStateVorticityGenerator_apply,
    waveMem, nonlinearEq]

/-- Rows outside the finite pair-output inventory also have zero residual. -/
theorem wholeSpaceTimeResidual_eq_zero_of_not_mem_pairOutput
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    {time : ℝ}
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime)
    {wave : IntegerWavevector}
    (pairNotMem :
      wave ∉ finiteVorticityPairOutputSupport stage.modes) :
    wholeSpaceTimeResidual stage time wave = 0 := by
  by_cases waveMem : wave ∈ stage.modes
  · exact
      wholeSpaceTimeResidual_eq_zero_of_mem
        stage timeMem waveMem
  have stateZero :
      stage.trajectory time wave = 0 :=
    (stage.physical time timeMem).2.1 wave waveMem
  have nonlinearZero :
      wholeStateVorticityNonlinearCoefficientAt
          (stage.trajectory time) wave =
        0 :=
    wholeStateVorticityNonlinearCoefficientAt_eq_zero_of_supported
      stage.modes (stage.trajectory time)
      (stage.physical time timeMem).2.1
      wave pairNotMem
  simp [wholeSpaceTimeResidual,
    wholeLatticeVorticityFourierPDEResidualAt,
    wholeLatticeVorticityFourierTangentAt,
    finiteStateVorticityGenerator_apply,
    waveMem, stateZero, nonlinearZero]

/--
Actual nonzero whole-time obligations before signed closure.  The candidate
inventory is finite and generated by the current support.
-/
def rawWholeSpaceTimeMissingModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime) :
    Finset IntegerWavevector := by
  classical
  exact
    (finiteVorticityPairOutputSupport stage.modes).filter fun wave =>
      wave ≠ 0 ∧
        wave ∉ stage.modes ∧
        ∃ time ∈ Icc (0 : ℝ) requestedTime,
          wholeSpaceTimeResidual stage time wave ≠ 0

@[simp] theorem mem_rawWholeSpaceTimeMissingModes_iff
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    (wave : IntegerWavevector) :
    wave ∈ rawWholeSpaceTimeMissingModes stage ↔
      wave ∈ finiteVorticityPairOutputSupport stage.modes ∧
        wave ≠ 0 ∧
        wave ∉ stage.modes ∧
        ∃ time ∈ Icc (0 : ℝ) requestedTime,
          wholeSpaceTimeResidual stage time wave ≠ 0 := by
  simp [rawWholeSpaceTimeMissingModes]

/-- Signed closure preserves the source's Fourier symmetry. -/
def wholeSpaceTimeMissingModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime) :
    Finset IntegerWavevector :=
  rawWholeSpaceTimeMissingModes stage ∪
    (rawWholeSpaceTimeMissingModes stage).image waveNeg

theorem rawMissing_subset_missing
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime) :
    rawWholeSpaceTimeMissingModes stage ⊆
      wholeSpaceTimeMissingModes stage :=
  Finset.subset_union_left

@[simp] theorem zero_not_mem_wholeSpaceTimeMissingModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime) :
    (0 : IntegerWavevector) ∉
      wholeSpaceTimeMissingModes stage := by
  simp [wholeSpaceTimeMissingModes,
    mem_rawWholeSpaceTimeMissingModes_iff]

theorem wholeSpaceTimeMissingModes_waveNeg_mem
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ wholeSpaceTimeMissingModes stage) :
    waveNeg wave ∈ wholeSpaceTimeMissingModes stage := by
  rw [wholeSpaceTimeMissingModes] at waveMem ⊢
  rcases Finset.mem_union.mp waveMem with rawMem | imageMem
  · exact
      Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨wave, rawMem, rfl⟩)
  · rcases Finset.mem_image.mp imageMem with
      ⟨sourceWave, sourceMem, sourceEq⟩
    have waveEq : wave = waveNeg sourceWave := sourceEq.symm
    rw [waveEq, waveNeg_involutive]
    exact Finset.mem_union_left _ sourceMem

/-- The exact next support generated by the complete residual inventory. -/
def wholeSpaceTimeNextModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime) :
    Finset IntegerWavevector :=
  stage.modes ∪ wholeSpaceTimeMissingModes stage

theorem modes_subset_wholeSpaceTimeNextModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime) :
    stage.modes ⊆ wholeSpaceTimeNextModes stage :=
  Finset.subset_union_left

@[simp] theorem zero_not_mem_wholeSpaceTimeNextModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime) :
    (0 : IntegerWavevector) ∉
      wholeSpaceTimeNextModes stage := by
  simp [wholeSpaceTimeNextModes, stage.zero_not_mem]

theorem wholeSpaceTimeNextModes_waveNeg_mem
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ wholeSpaceTimeNextModes stage) :
    waveNeg wave ∈ wholeSpaceTimeNextModes stage := by
  rw [wholeSpaceTimeNextModes] at waveMem ⊢
  rcases Finset.mem_union.mp waveMem with modeMem | missingMem
  · exact
      Finset.mem_union_left _
        (stage.waveNeg_mem wave modeMem)
  · exact
      Finset.mem_union_right _
        (wholeSpaceTimeMissingModes_waveNeg_mem stage missingMem)

theorem wholeSpaceTimeMissingModes_not_mem_modes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ wholeSpaceTimeMissingModes stage) :
    wave ∉ stage.modes := by
  rw [wholeSpaceTimeMissingModes] at waveMem
  rcases Finset.mem_union.mp waveMem with rawMem | imageMem
  · exact
      (mem_rawWholeSpaceTimeMissingModes_iff
        stage wave).mp rawMem |>.2.2.1
  · rcases Finset.mem_image.mp imageMem with
      ⟨sourceWave, sourceMem, sourceEq⟩
    intro waveInModes
    have sourceInModes : sourceWave ∈ stage.modes := by
      have negatedInModes :
          waveNeg (waveNeg sourceWave) ∈ stage.modes :=
        stage.waveNeg_mem _ (sourceEq ▸ waveInModes)
      simpa using negatedInModes
    exact
      (mem_rawWholeSpaceTimeMissingModes_iff
        stage sourceWave).mp sourceMem |>.2.2.1 sourceInModes

/--
The raw inventory is empty exactly when every nonzero whole-space-time
residual row vanishes throughout the requested interval.
-/
theorem rawWholeSpaceTimeMissingModes_eq_empty_iff_puncturedResidual_zero
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime) :
    rawWholeSpaceTimeMissingModes stage = ∅ ↔
      ∀ time ∈ Icc (0 : ℝ) requestedTime,
        ∀ wave : IntegerWavevector,
          wave ≠ 0 →
            wholeSpaceTimeResidual stage time wave = 0 := by
  constructor
  · intro missingEmpty time timeMem wave waveNonzero
    by_cases waveMem : wave ∈ stage.modes
    · exact
        wholeSpaceTimeResidual_eq_zero_of_mem
          stage timeMem waveMem
    by_cases pairMem :
        wave ∈ finiteVorticityPairOutputSupport stage.modes
    · by_contra residualNonzero
      have missingMem :
          wave ∈ rawWholeSpaceTimeMissingModes stage :=
        (mem_rawWholeSpaceTimeMissingModes_iff
          stage wave).mpr
            ⟨pairMem, waveNonzero, waveMem,
              ⟨time, timeMem, residualNonzero⟩⟩
      rw [missingEmpty] at missingMem
      simp at missingMem
    · exact
        wholeSpaceTimeResidual_eq_zero_of_not_mem_pairOutput
          stage timeMem pairMem
  · intro residualZero
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro wave missingMem
    rcases
        (mem_rawWholeSpaceTimeMissingModes_iff
          stage wave).mp missingMem with
      ⟨_pairMem, waveNonzero, _waveNotMem,
        time, timeMem, residualNonzero⟩
    exact
      residualNonzero
        (residualZero time timeMem wave waveNonzero)

theorem modes_ssubset_wholeSpaceTimeNextModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    (missingNonempty :
      (rawWholeSpaceTimeMissingModes stage).Nonempty) :
    stage.modes ⊂ wholeSpaceTimeNextModes stage := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨modes_subset_wholeSpaceTimeNextModes stage, ?_⟩
  rcases missingNonempty with ⟨wave, waveMem⟩
  intro modesEq
  have waveInNext :
      wave ∈ wholeSpaceTimeNextModes stage :=
    Finset.mem_union_right _
      (rawMissing_subset_missing stage waveMem)
  have waveInModes : wave ∈ stage.modes := by
    rw [modesEq]
    exact waveInNext
  exact
    (wholeSpaceTimeMissingModes_not_mem_modes
      stage (rawMissing_subset_missing stage waveMem))
      waveInModes

/--
Generate the exact next requested-time stage from the current full-time
residual.  The physical initial state and time interval remain fixed.
-/
noncomputable def wholeSpaceTimeNext
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTimePos : 0 < requestedTime) :
    GeneratedRequestedTimeReplayStage lineage requestedTime :=
  ofModes lineage initialSubcritical requestedTime requestedTimePos
    (wholeSpaceTimeNextModes stage)
    (stage.initialModes_subset.trans
      (modes_subset_wholeSpaceTimeNextModes stage))
    (zero_not_mem_wholeSpaceTimeNextModes stage)
    (fun _wave waveMem =>
      wholeSpaceTimeNextModes_waveNeg_mem stage waveMem)

@[simp] theorem wholeSpaceTimeNext_modes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTimePos : 0 < requestedTime) :
    (wholeSpaceTimeNext
      stage initialSubcritical requestedTimePos).modes =
      wholeSpaceTimeNextModes stage := by
  simp [wholeSpaceTimeNext, ofModes]

end GeneratedRequestedTimeReplayStage

/--
The initial requested-time stage is generated from the first actual source
support and the shared source-owned physical initial state.
-/
noncomputable def initialRequestedTimeReplayStage
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) :
    GeneratedRequestedTimeReplayStage lineage requestedTime :=
  GeneratedRequestedTimeReplayStage.ofModes
    lineage initialSubcritical requestedTime requestedTimePos
    (lineageReceiptModes lineage 0)
    Finset.Subset.rfl
    (by
      unfold lineageReceiptModes
      exact zero_not_mem_generatedSupport _)
    (by
      intro wave waveMem
      unfold lineageReceiptModes at waveMem ⊢
      exact generatedSupport_waveNeg_mem _ waveMem)

@[simp] theorem initialRequestedTimeReplayStage_modes
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) :
    (initialRequestedTimeReplayStage
      lineage initialSubcritical requestedTime requestedTimePos).modes =
      lineageReceiptModes lineage 0 := by
  simp [initialRequestedTimeReplayStage,
    GeneratedRequestedTimeReplayStage.ofModes]

/--
The initial producer supplies the full actual unforced physical law on the
requested interval.
-/
theorem initialRequestedTimeReplayStage_physical
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) :
    ∀ time ∈ Icc (0 : ℝ) requestedTime,
      HasDerivAt
          (initialRequestedTimeReplayStage
            lineage initialSubcritical requestedTime
            requestedTimePos).trajectory
          (finiteStateVorticityGenerator
            (initialRequestedTimeReplayStage
              lineage initialSubcritical requestedTime
              requestedTimePos).modes
            ν.coeff
            ((initialRequestedTimeReplayStage
              lineage initialSubcritical requestedTime
              requestedTimePos).trajectory time))
          time ∧
        (∀ wave,
          wave ∉
              (initialRequestedTimeReplayStage
                lineage initialSubcritical requestedTime
                requestedTimePos).modes →
            (initialRequestedTimeReplayStage
              lineage initialSubcritical requestedTime
              requestedTimePos).trajectory time wave = 0) ∧
        (∀ wave,
          complexWavevector wave ⬝ᵥ
              (initialRequestedTimeReplayStage
                lineage initialSubcritical requestedTime
                requestedTimePos).trajectory time wave =
            0) ∧
        FiniteStateFourierReality
          ((initialRequestedTimeReplayStage
            lineage initialSubcritical requestedTime
            requestedTimePos).trajectory time) :=
  (initialRequestedTimeReplayStage
    lineage initialSubcritical requestedTime requestedTimePos).physical

/-- One native requested-time residual refinement edge. -/
inductive NativeRequestedTimeReplayStep
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) :
    GeneratedRequestedTimeReplayStage lineage requestedTime →
      GeneratedRequestedTimeReplayStage lineage requestedTime → Type
  | expand
      (current :
        GeneratedRequestedTimeReplayStage lineage requestedTime)
      (missingNonempty :
        (GeneratedRequestedTimeReplayStage.rawWholeSpaceTimeMissingModes
          current).Nonempty) :
      NativeRequestedTimeReplayStep
        lineage initialSubcritical requestedTime requestedTimePos
        current
        (GeneratedRequestedTimeReplayStage.wholeSpaceTimeNext
          current initialSubcritical requestedTimePos)

/--
The source-owned requested-time responder.  No trajectory, support, row,
time witness, or branch is supplied by the caller.
-/
noncomputable def generatedRequestedTimeReplayRespond
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (current :
      GeneratedRequestedTimeReplayStage lineage requestedTime) :
    Option
      (Response
        (NativeRequestedTimeReplayStep
          lineage initialSubcritical requestedTime requestedTimePos)
        current) :=
  if missingNonempty :
      (GeneratedRequestedTimeReplayStage.rawWholeSpaceTimeMissingModes
        current).Nonempty then
    some
      ⟨GeneratedRequestedTimeReplayStage.wholeSpaceTimeNext
          current initialSubcritical requestedTimePos,
        .expand current missingNonempty⟩
  else
    none

/--
`none` is exactly punctured whole-space-time residual silence on the
requested interval.
-/
theorem generatedRequestedTimeReplayRespond_eq_none_iff_puncturedResidual_zero
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (current :
      GeneratedRequestedTimeReplayStage lineage requestedTime) :
    generatedRequestedTimeReplayRespond
        lineage initialSubcritical requestedTime
        requestedTimePos current =
      none ↔
        ∀ time ∈ Icc (0 : ℝ) requestedTime,
          ∀ wave : IntegerWavevector,
            wave ≠ 0 →
              GeneratedRequestedTimeReplayStage.wholeSpaceTimeResidual
                current time wave = 0 := by
  constructor
  · intro stopped
    have missingEmpty :
        GeneratedRequestedTimeReplayStage.rawWholeSpaceTimeMissingModes
            current =
          ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro missingNonempty
      simp [generatedRequestedTimeReplayRespond,
        missingNonempty] at stopped
    exact
      (GeneratedRequestedTimeReplayStage.rawWholeSpaceTimeMissingModes_eq_empty_iff_puncturedResidual_zero
        current).mp missingEmpty
  · intro residualClosed
    have missingEmpty :
        GeneratedRequestedTimeReplayStage.rawWholeSpaceTimeMissingModes
            current =
          ∅ :=
      (GeneratedRequestedTimeReplayStage.rawWholeSpaceTimeMissingModes_eq_empty_iff_puncturedResidual_zero
        current).mpr residualClosed
    have missingNotNonempty :
        ¬ (GeneratedRequestedTimeReplayStage.rawWholeSpaceTimeMissingModes
          current).Nonempty := by
      simp [missingEmpty]
    simp [generatedRequestedTimeReplayRespond,
      missingNotNonempty]

namespace NativeRequestedTimeReplayStep

/-- Every generated requested-time residual edge strictly enlarges support. -/
theorem modes_ssubset
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {current next :
      GeneratedRequestedTimeReplayStage lineage requestedTime}
    (step :
      NativeRequestedTimeReplayStep
        lineage initialSubcritical requestedTime requestedTimePos
        current next) :
    current.modes ⊂ next.modes := by
  cases step with
  | expand missingNonempty =>
      rw [GeneratedRequestedTimeReplayStage.wholeSpaceTimeNext_modes]
      exact
        GeneratedRequestedTimeReplayStage.modes_ssubset_wholeSpaceTimeNextModes
          current missingNonempty

end NativeRequestedTimeReplayStep

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplaySource
end NavierStokes
end SaturationMonoid
