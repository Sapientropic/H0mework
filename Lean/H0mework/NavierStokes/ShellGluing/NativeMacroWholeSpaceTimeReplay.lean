import H0mework.NavierStokes.ShellGluing.NativeMacroWholeResidualCommonTimeReplay
import H0mework.NavierStokes.GeneratedPaths.InfiniteNonlinearNegativeOneTimeBudget

/-!
# Whole-space-time residual replay

Endpoint residual silence can miss an obligation which is nonzero in the
interior of the same actual unforced time window.  The native replay is
therefore lifted from an endpoint row to the complete finite
`time × Fourier-row` residual carrier.

For one replay support `S`, every possible nonlinear residual row lies in
the finite pair-output inventory `S + S`.  The source filters that finite
inventory by the actual proposition

```text
∃ t ∈ [0,T], wholeResidual(t, k) ≠ 0
```

and closes the result under wave negation.  A nonempty inventory generates a
strict support expansion and another actual unforced common-time replay from
the same physical initial state.  `none` is now equivalent to vanishing of
the whole residual at every nonzero row and every time in the interval.

No time, wave, cutoff, nonzero witness, branch, target, or closure
certificate is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeSpaceTimeReplay

open Set
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCommonTimeExistence
open
  ThreeDimensionalVorticityCoefficientFinitePhysicalStateSupportLift
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
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
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay.GeneratedCommonTimeReplayStage

noncomputable section

namespace GeneratedCommonTimeReplayStage

/-- Whole-lattice residual of the actual replay at one physical time. -/
def wholeSpaceTimeResidual
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
    (time : ℝ)
    (wave : IntegerWavevector) :
    ComplexCoordinateVector :=
  wholeLatticeVorticityFourierPDEResidualAt
    ν.coeff
    (stage.trajectory time)
    (finiteStateVorticityGenerator
      stage.modes ν.coeff (stage.trajectory time))
    wave

/-- A retained row has no whole-space residual at any actual time. -/
theorem wholeSpaceTimeResidual_eq_zero_of_mem
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
    {time : ℝ}
    (timeMem :
      time ∈ Icc (0 : ℝ) (commonTimeReplayDuration lineage))
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

/--
Outside both the retained support and its finite pair-output inventory, the
whole-space residual is forced to zero.
-/
theorem wholeSpaceTimeResidual_eq_zero_of_not_mem_pairOutput
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
    {time : ℝ}
    (timeMem :
      time ∈ Icc (0 : ℝ) (commonTimeReplayDuration lineage))
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
Actual nonzero whole-time obligations before signed closure.  The finite
candidate inventory is generated by the current support itself.
-/
def rawWholeSpaceTimeMissingModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    Finset IntegerWavevector := by
  classical
  exact
    (finiteVorticityPairOutputSupport stage.modes).filter fun wave =>
      wave ≠ 0 ∧
        wave ∉ stage.modes ∧
        ∃ time ∈
            Icc (0 : ℝ) (commonTimeReplayDuration lineage),
          wholeSpaceTimeResidual stage time wave ≠ 0

@[simp] theorem mem_rawWholeSpaceTimeMissingModes_iff
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
    (wave : IntegerWavevector) :
    wave ∈ rawWholeSpaceTimeMissingModes stage ↔
      wave ∈ finiteVorticityPairOutputSupport stage.modes ∧
        wave ≠ 0 ∧
        wave ∉ stage.modes ∧
        ∃ time ∈
            Icc (0 : ℝ) (commonTimeReplayDuration lineage),
          wholeSpaceTimeResidual stage time wave ≠ 0 := by
  simp [rawWholeSpaceTimeMissingModes]

/--
Signed source-owned closure of every actual whole-time residual row.
Closing the finite inventory under wave negation avoids imposing residual
reality as a premise of the update.
-/
def wholeSpaceTimeMissingModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    Finset IntegerWavevector :=
  rawWholeSpaceTimeMissingModes stage ∪
    (rawWholeSpaceTimeMissingModes stage).image waveNeg

theorem rawMissing_subset_missing
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    rawWholeSpaceTimeMissingModes stage ⊆
      wholeSpaceTimeMissingModes stage :=
  Finset.subset_union_left

@[simp] theorem zero_not_mem_wholeSpaceTimeMissingModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    (0 : IntegerWavevector) ∉
      wholeSpaceTimeMissingModes stage := by
  simp [wholeSpaceTimeMissingModes,
    mem_rawWholeSpaceTimeMissingModes_iff]

theorem wholeSpaceTimeMissingModes_waveNeg_mem
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
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

/-- Next support generated by the complete whole-time residual inventory. -/
def wholeSpaceTimeNextModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    Finset IntegerWavevector :=
  stage.modes ∪ wholeSpaceTimeMissingModes stage

theorem modes_subset_wholeSpaceTimeNextModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    stage.modes ⊆ wholeSpaceTimeNextModes stage :=
  Finset.subset_union_left

@[simp] theorem zero_not_mem_wholeSpaceTimeNextModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    (0 : IntegerWavevector) ∉
      wholeSpaceTimeNextModes stage := by
  simp [wholeSpaceTimeNextModes, stage.zero_not_mem]

theorem wholeSpaceTimeNextModes_waveNeg_mem
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
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

/--
Every signed missing mode remains outside the current support.  The
wave-negated half cannot silently return to the current support because that
support is itself closed under wave negation.
-/
theorem wholeSpaceTimeMissingModes_not_mem_modes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
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

@[simp] theorem wholeSpaceTimeMissingModes_eq_empty_iff_raw
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    wholeSpaceTimeMissingModes stage = ∅ ↔
      rawWholeSpaceTimeMissingModes stage = ∅ := by
  simp [wholeSpaceTimeMissingModes]

/--
The finite source-owned inventory is empty exactly when the actual unforced
trajectory has zero whole-lattice residual at every nonzero Fourier row and
every physical time of the common interval.
-/
theorem rawWholeSpaceTimeMissingModes_eq_empty_iff_puncturedResidual_zero
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    rawWholeSpaceTimeMissingModes stage = ∅ ↔
      ∀ time ∈
          Icc (0 : ℝ) (commonTimeReplayDuration lineage),
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

/-- Signed closure has the same exact punctured-space terminal semantics. -/
theorem wholeSpaceTimeMissingModes_eq_empty_iff_puncturedResidual_zero
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    wholeSpaceTimeMissingModes stage = ∅ ↔
      ∀ time ∈
          Icc (0 : ℝ) (commonTimeReplayDuration lineage),
        ∀ wave : IntegerWavevector,
          wave ≠ 0 →
            wholeSpaceTimeResidual stage time wave = 0 := by
  rw [wholeSpaceTimeMissingModes_eq_empty_iff_raw,
    rawWholeSpaceTimeMissingModes_eq_empty_iff_puncturedResidual_zero]

/--
An actual nonzero residual witness strictly enlarges the source-owned support.
The witness is carried by the raw inventory; signed closure only preserves
the source symmetry.
-/
theorem modes_ssubset_wholeSpaceTimeNextModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
    (missingNonempty :
      (rawWholeSpaceTimeMissingModes stage).Nonempty) :
    stage.modes ⊂ wholeSpaceTimeNextModes stage := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨modes_subset_wholeSpaceTimeNextModes stage, ?_⟩
  rcases missingNonempty with ⟨wave, waveMem⟩
  intro modesEq
  have waveInNext :
      wave ∈ wholeSpaceTimeNextModes stage := by
    exact
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
The complete space-time residual itself generates the next actual unforced
common-time macro stage.  Only the support is refined; the physical initial
state, viscosity, and physical time window remain fixed by the source.
-/
noncomputable def wholeSpaceTimeNext
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) :
    GeneratedCommonTimeReplayStage lineage := by
  let modes := wholeSpaceTimeNextModes stage
  have initialModesSubset :
      lineageReceiptModes lineage 0 ⊆ modes :=
    stage.initialModes_subset.trans
      (modes_subset_wholeSpaceTimeNextModes stage)
  have zeroNotMem :
      (0 : IntegerWavevector) ∉ modes :=
    zero_not_mem_wholeSpaceTimeNextModes stage
  have negClosed :
      ∀ wave, wave ∈ modes →
        waveNeg wave ∈ modes :=
    by
      intro wave waveMem
      exact
        wholeSpaceTimeNextModes_waveNeg_mem stage waveMem
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
    replayInitialSmall_on_modes
      initialSubcritical modes
  let trajectoryResult :=
    exists_finitePhysicalTrajectory_on_Icc_of_criticalSmall
      modes zeroNotMem negClosed
      ν.coeff ν.coeff_pos
      (commonTimeReplayInitialState lineage)
      initialSupported initialTransverse initialReality
      initialSmall
      (commonTimeReplayDuration lineage)
      (commonTimeReplayDuration_pos lineage)
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

@[simp] theorem wholeSpaceTimeNext_modes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) :
    (wholeSpaceTimeNext stage initialSubcritical).modes =
      wholeSpaceTimeNextModes stage := by
  simp [wholeSpaceTimeNext]

end GeneratedCommonTimeReplayStage

/--
One native complete-space-time residual replay edge.  Its payload carries
the source-generated nonzero residual inventory which caused the exact
support refinement.
-/
inductive NativeWholeSpaceTimeReplayStep
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) :
    GeneratedCommonTimeReplayStage lineage →
      GeneratedCommonTimeReplayStage lineage → Type
  | expand
      (current : GeneratedCommonTimeReplayStage lineage)
      (missingNonempty :
        (GeneratedCommonTimeReplayStage.rawWholeSpaceTimeMissingModes
          current).Nonempty) :
      NativeWholeSpaceTimeReplayStep lineage initialSubcritical
        current
        (GeneratedCommonTimeReplayStage.wholeSpaceTimeNext
          current initialSubcritical)

/--
The actual whole-space-time residual responder.  No time, row, support,
branch, or nonzero witness is selected by the caller.
-/
noncomputable def generatedWholeSpaceTimeReplayRespond
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (current : GeneratedCommonTimeReplayStage lineage) :
    Option
      (Response
        (NativeWholeSpaceTimeReplayStep
          lineage initialSubcritical)
        current) :=
  if missingNonempty :
      (GeneratedCommonTimeReplayStage.rawWholeSpaceTimeMissingModes
        current).Nonempty then
    some
      ⟨GeneratedCommonTimeReplayStage.wholeSpaceTimeNext
          current initialSubcritical,
        .expand current missingNonempty⟩
  else
    none

/--
`none` has exact full-time semantics: every nonzero Fourier row of the
actual trajectory satisfies the whole unforced equation throughout the
common physical interval.
-/
theorem generatedWholeSpaceTimeReplayRespond_eq_none_iff_puncturedResidual_zero
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (current : GeneratedCommonTimeReplayStage lineage) :
    generatedWholeSpaceTimeReplayRespond
        lineage initialSubcritical current =
      none ↔
        ∀ time ∈
            Icc (0 : ℝ) (commonTimeReplayDuration lineage),
          ∀ wave : IntegerWavevector,
            wave ≠ 0 →
              GeneratedCommonTimeReplayStage.wholeSpaceTimeResidual
                current time wave = 0 := by
  constructor
  · intro stopped
    have missingEmpty :
        GeneratedCommonTimeReplayStage.rawWholeSpaceTimeMissingModes
            current =
          ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro missingNonempty
      simp [generatedWholeSpaceTimeReplayRespond,
        missingNonempty] at stopped
    exact
      (GeneratedCommonTimeReplayStage.rawWholeSpaceTimeMissingModes_eq_empty_iff_puncturedResidual_zero
        current).mp missingEmpty
  · intro residualClosed
    have missingEmpty :
        GeneratedCommonTimeReplayStage.rawWholeSpaceTimeMissingModes
            current =
          ∅ :=
      (GeneratedCommonTimeReplayStage.rawWholeSpaceTimeMissingModes_eq_empty_iff_puncturedResidual_zero
        current).mpr residualClosed
    have missingNotNonempty :
        ¬ (GeneratedCommonTimeReplayStage.rawWholeSpaceTimeMissingModes
          current).Nonempty := by
      simp [missingEmpty]
    simp [generatedWholeSpaceTimeReplayRespond,
      missingNotNonempty]

namespace NativeWholeSpaceTimeReplayStep

/-- Every generated space-time residual edge strictly enlarges its support. -/
theorem modes_ssubset
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {current next : GeneratedCommonTimeReplayStage lineage}
    (step :
      NativeWholeSpaceTimeReplayStep
        lineage initialSubcritical current next) :
    current.modes ⊂ next.modes := by
  cases step with
  | expand missingNonempty =>
      rw [GeneratedCommonTimeReplayStage.wholeSpaceTimeNext_modes]
      exact
        GeneratedCommonTimeReplayStage.modes_ssubset_wholeSpaceTimeNextModes
          current missingNonempty

end NativeWholeSpaceTimeReplayStep

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeSpaceTimeReplay
end NavierStokes
end SaturationMonoid
