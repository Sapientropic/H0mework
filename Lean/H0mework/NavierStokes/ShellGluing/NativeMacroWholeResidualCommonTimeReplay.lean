import H0mework.NavierStokes.ShellGluing.NativeMacroWholeResidualCriticalLineage
import H0mework.NavierStokes.InitialData.FinitePhysicalStateSupportLift
import H0mework.NavierStokes.Galerkin.CommonTimeExistence
import H0mework.NavierStokes.ShellSources.InfiniteLineageHilbertCompletion

/-!
# Source-owned common-time replay of the native whole residual

The forward native macro runtime evolves its physical endpoint in time.  A
whole-PDE limit consumer instead needs all support refinements replayed from
one physical initial state on one physical time interval.  This module
generates that refinement from the existing source law.

The first replay stage is the actual initial native macro receipt.  At every
later stage:

```text
same initial physical state
→ actual unforced Galerkin trajectory on the same positive interval
→ actual endpoint whole residual
→ endpoint source computes its missing nonlinear support
→ complete missing-support write becomes the next replay support.
```

The support, endpoint state, residual, next support, trajectory, and common
time are all generated.  No cutoff, target support, trajectory, convergence
certificate, critical margin, branch, or nonzero witness is supplied by a
caller.  The public producer internally exhausts the fixed half-critical
crossing before constructing the replay lineage.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay

open scoped BigOperators

open Set
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCommonTimeExistence
open
  ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open
  ThreeDimensionalVorticityCoefficientFinitePhysicalStateSupportLift
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedWholeCarrierCompiler
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open
  ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget

noncomputable section

/-- The single physical state from which every replay stage starts. -/
def commonTimeReplayInitialState
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    ComplexVorticityHilbertState :=
  (lineage.physicalReceipt 0).trajectory 0

/-- The source-owned positive interval shared by every replay stage. -/
def commonTimeReplayDuration
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) : ℝ :=
  (lineage.physicalReceipt 0).duration

theorem commonTimeReplayDuration_pos
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    0 < commonTimeReplayDuration lineage :=
  (lineage.physicalReceipt 0).duration_pos

theorem commonTimeReplayInitialState_supported
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    ∀ wave,
      wave ∉ lineageReceiptModes lineage 0 →
        commonTimeReplayInitialState lineage wave = 0 := by
  intro wave waveNotMem
  have zeroMem :
      (0 : ℝ) ∈
        Icc (0 : ℝ) (lineage.physicalReceipt 0).duration :=
    ⟨le_rfl, (lineage.physicalReceipt 0).duration_pos.le⟩
  simpa [commonTimeReplayInitialState, lineageReceiptModes] using
    ((lineage.physicalReceipt 0).physical 0 zeroMem).2.1
      wave waveNotMem

theorem commonTimeReplayInitialState_transverse
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    ∀ wave,
      complexWavevector wave ⬝ᵥ
          commonTimeReplayInitialState lineage wave =
        0 := by
  intro wave
  have zeroMem :
      (0 : ℝ) ∈
        Icc (0 : ℝ) (lineage.physicalReceipt 0).duration :=
    ⟨le_rfl, (lineage.physicalReceipt 0).duration_pos.le⟩
  exact
    ((lineage.physicalReceipt 0).physical 0 zeroMem).2.2.1 wave

theorem commonTimeReplayInitialState_reality
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    FiniteStateFourierReality
      (commonTimeReplayInitialState lineage) := by
  have zeroMem :
      (0 : ℝ) ∈
        Icc (0 : ℝ) (lineage.physicalReceipt 0).duration :=
    ⟨le_rfl, (lineage.physicalReceipt 0).duration_pos.le⟩
  exact
    ((lineage.physicalReceipt 0).physical 0 zeroMem).2.2.2

/--
One common-time replay stage.  Its support contains the first actual replay
support, while its trajectory starts from the exact same physical state and
solves the unforced Galerkin law on the exact same positive interval.
-/
structure GeneratedCommonTimeReplayStage
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) where
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
    ∀ time ∈ Icc (0 : ℝ) (commonTimeReplayDuration lineage),
      HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory time))
          time ∧
        (∀ wave, wave ∉ modes → trajectory time wave = 0) ∧
        (∀ wave,
          complexWavevector wave ⬝ᵥ trajectory time wave = 0) ∧
        FiniteStateFourierReality (trajectory time)

namespace GeneratedCommonTimeReplayStage

/-- Endpoint state of one actual common-time replay. -/
def endpoint
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    ComplexVorticityHilbertState :=
  stage.trajectory (commonTimeReplayDuration lineage)

/--
Primitive endpoint source used to read the actual replay residual.  It owns
exactly the current replay support.
-/
def endpointSource
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    RawVorticityFourierSource :=
  rawSourceOfFiniteVorticityState stage.modes stage.endpoint

theorem endpointSource_generatedSupport
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    generatedSupport stage.endpointSource = stage.modes := by
  exact
    rawSourceOfFiniteVorticityState_generatedSupport
      stage.modes stage.zero_not_mem stage.waveNeg_mem stage.endpoint

theorem endpointSource_generatedState
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    generatedComplexVorticityState
        stage.endpointSource
        (generatedSupport stage.endpointSource) =
      stage.endpoint := by
  have endpointMem :
      commonTimeReplayDuration lineage ∈
        Icc (0 : ℝ) (commonTimeReplayDuration lineage) :=
    ⟨commonTimeReplayDuration_pos lineage |>.le, le_rfl⟩
  have endpointPhysical :=
    stage.physical (commonTimeReplayDuration lineage) endpointMem
  exact
    generatedComplexVorticityState_rawSourceOfFinitePhysicalState
      stage.modes stage.zero_not_mem stage.waveNeg_mem
      stage.endpoint endpointPhysical.2.1
      (fun wave waveMem => endpointPhysical.2.2.1 wave)
      endpointPhysical.2.2.2

/-- Whole-lattice PDE residual at the actual replay endpoint. -/
def endpointWholeResidual
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    IntegerWavevector → ComplexCoordinateVector :=
  wholeLatticeVorticityFourierPDEResidualAt
    ν.coeff
    stage.endpoint
    (finiteStateVorticityGenerator
      stage.modes ν.coeff stage.endpoint)

/--
Every endpoint missing row is an exact nonzero coordinate of the actual
whole-PDE residual.
-/
theorem endpointWholeResidual_missing_eq_neg_generated
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedMissingNonlinearModes stage.endpointSource) :
    stage.endpointWholeResidual output =
      -generatedVorticityNonlinearCoefficientAt
        stage.endpointSource output := by
  unfold endpointWholeResidual
  rw [← stage.endpointSource_generatedSupport,
    ← stage.endpointSource_generatedState]
  exact
    currentFullPDEResidual_missing_eq_neg_generated
      stage.endpointSource ν.coeff outputMem

theorem endpointWholeResidual_missing_ne_zero
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedMissingNonlinearModes stage.endpointSource) :
    stage.endpointWholeResidual output ≠ 0 := by
  unfold endpointWholeResidual
  rw [← stage.endpointSource_generatedSupport,
    ← stage.endpointSource_generatedState]
  exact
    currentFullPDEResidual_missing_ne_zero
      stage.endpointSource ν.coeff outputMem

/--
Faithful endpoint residual silence is exactly closure of the replay's
source-computed missing inventory.
-/
theorem endpointWholeResidual_eq_zero_iff_missing_eq_empty
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    stage.endpointWholeResidual = 0 ↔
      generatedMissingNonlinearModes stage.endpointSource = ∅ := by
  constructor
  · intro residualZero
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro output outputMem
    have rowZero :
        stage.endpointWholeResidual output = 0 :=
      congrFun residualZero output
    exact
      stage.endpointWholeResidual_missing_ne_zero outputMem
        rowZero
  · intro missingClosed
    have modesEq :
        generatedCompleteNonlinearGalerkinModes stage.endpointSource =
          generatedSupport stage.endpointSource := by
      simp [generatedCompleteNonlinearGalerkinModes, missingClosed]
    have completeZero :=
      completeGalerkinWholeLatticePDEResidual_eq_zero
        stage.endpointSource ν.coeff
    unfold endpointWholeResidual
    rw [← stage.endpointSource_generatedSupport,
      ← stage.endpointSource_generatedState,
      ← generatedCompleteNonlinearInitialState_eq_currentPhysicalState,
      ← modesEq]
    exact completeZero

/-- The next support is computed from the actual replay endpoint residual. -/
def nextModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    Finset IntegerWavevector :=
  generatedCompleteNonlinearGalerkinModes stage.endpointSource

theorem modes_subset_nextModes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    stage.modes ⊆ stage.nextModes := by
  rw [← stage.endpointSource_generatedSupport]
  exact
    generatedSupport_subset_completeNonlinearGalerkinModes
      stage.endpointSource

theorem nextModes_eq_modes_union_missing
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage) :
    stage.nextModes =
      stage.modes ∪
        generatedMissingNonlinearModes stage.endpointSource := by
  unfold nextModes generatedCompleteNonlinearGalerkinModes
  rw [stage.endpointSource_generatedSupport]

theorem replayInitialSmall_on_modes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (modes : Finset IntegerWavevector) :
    criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (commonTimeReplayInitialState lineage) ≤
      ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
  have baseCritical :
      criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (lineageReceiptModes lineage 0)
              (commonTimeReplayInitialState lineage) ≤
        (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
    simpa [lineageHalfCriticalCrossing,
      commonTimeReplayInitialState] using
      le_of_not_gt initialSubcritical
  have enstrophyLe :
      finiteStateVorticityCoefficientEnstrophy
          modes (commonTimeReplayInitialState lineage) ≤
        finiteStateVorticityCoefficientEnstrophy
          (lineageReceiptModes lineage 0)
          (commonTimeReplayInitialState lineage) :=
    finiteStateVorticityCoefficientEnstrophy_le_of_supported
      modes (lineageReceiptModes lineage 0)
      (commonTimeReplayInitialState lineage)
      (commonTimeReplayInitialState_supported lineage)
  calc
    criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (commonTimeReplayInitialState lineage) ≤
        criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            (lineageReceiptModes lineage 0)
            (commonTimeReplayInitialState lineage) :=
      mul_le_mul_of_nonneg_left enstrophyLe
        criticalEnstrophyLatticeConstant_nonneg
    _ ≤
        (1 / 2 : ℝ) * ν.coeff ^ 2 *
          (2 * Real.pi) ^ 2 :=
      baseCritical
    _ ≤ ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
      have productNonnegative :
          0 ≤ ν.coeff ^ 2 * (2 * Real.pi) ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      nlinarith

/--
Generate the next common-time replay directly from the endpoint residual
support while resetting only the physical initial state to the one fixed
source-owned initial state.
-/
noncomputable def next
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) :
    GeneratedCommonTimeReplayStage lineage := by
  let modes := stage.nextModes
  have initialModesSubset :
      lineageReceiptModes lineage 0 ⊆ modes :=
    stage.initialModes_subset.trans stage.modes_subset_nextModes
  have zeroNotMem :
      (0 : IntegerWavevector) ∉ modes := by
    exact
      zero_not_mem_completeNonlinearGalerkinModes
        stage.endpointSource
  have negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes := by
    intro wave waveMem
    exact
      (mem_completeNonlinearGalerkinModes_waveNeg_iff
        stage.endpointSource wave).mpr waveMem
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
    intro wave waveMem
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

@[simp] theorem next_modes
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage : GeneratedCommonTimeReplayStage lineage)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) :
    (stage.next initialSubcritical).modes =
      stage.nextModes := by
  simp [next]

end GeneratedCommonTimeReplayStage

/-- The first replay is the actual first native macro receipt. -/
def initialCommonTimeReplayStage
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    GeneratedCommonTimeReplayStage lineage where
  modes := lineageReceiptModes lineage 0
  initialModes_subset := Finset.Subset.rfl
  zero_not_mem := by
    unfold lineageReceiptModes
    exact zero_not_mem_generatedSupport _
  waveNeg_mem := by
    intro wave waveMem
    unfold lineageReceiptModes at waveMem ⊢
    exact generatedSupport_waveNeg_mem _ waveMem
  trajectory := (lineage.physicalReceipt 0).trajectory
  initial := rfl
  physical := by
    intro time timeMem
    simpa [lineageReceiptModes, commonTimeReplayDuration] using
      (lineage.physicalReceipt 0).physical time
        (by simpa [commonTimeReplayDuration] using timeMem)

/--
One native common-time refinement edge.  It exists only when the endpoint
missing inventory is nonempty; terminal residual closure therefore cannot
be turned into a silent self-loop.
-/
inductive NativeCommonTimeReplayStep
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) :
    GeneratedCommonTimeReplayStage lineage →
      GeneratedCommonTimeReplayStage lineage → Type
  | expand
      (current : GeneratedCommonTimeReplayStage lineage)
      (missingNonempty :
        (generatedMissingNonlinearModes
          current.endpointSource).Nonempty) :
      NativeCommonTimeReplayStep lineage initialSubcritical
        current (current.next initialSubcritical)

/--
Source-owned replay responder.  `none` is faithful endpoint residual
closure; `some` contains the exact next common-time replay stage.
-/
noncomputable def generatedCommonTimeReplayRespond
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (current : GeneratedCommonTimeReplayStage lineage) :
    Option
      (Response
        (NativeCommonTimeReplayStep lineage initialSubcritical)
        current) :=
  if missingNonempty :
      (generatedMissingNonlinearModes
        current.endpointSource).Nonempty then
    some
      ⟨current.next initialSubcritical,
        .expand current missingNonempty⟩
  else
    none

theorem generatedCommonTimeReplayRespond_eq_none_iff_residual_eq_zero
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (current : GeneratedCommonTimeReplayStage lineage) :
    generatedCommonTimeReplayRespond
        lineage initialSubcritical current =
      none ↔
        current.endpointWholeResidual = 0 := by
  by_cases missingNonempty :
      (generatedMissingNonlinearModes
        current.endpointSource).Nonempty
  · have residualNonzero :
        current.endpointWholeResidual ≠ 0 := by
      intro residualZero
      have missingClosed :=
        (current.endpointWholeResidual_eq_zero_iff_missing_eq_empty).mp
          residualZero
      simp [missingClosed] at missingNonempty
    simp [generatedCommonTimeReplayRespond,
      missingNonempty, residualNonzero]
  · have missingClosed :
        generatedMissingNonlinearModes
            current.endpointSource =
          ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp missingNonempty
    have residualZero :
        current.endpointWholeResidual = 0 :=
      current.endpointWholeResidual_eq_zero_iff_missing_eq_empty.mpr
        missingClosed
    simp [generatedCommonTimeReplayRespond,
      missingNonempty, residualZero]

namespace NativeCommonTimeReplayStep

/-- Every successful replay edge strictly enlarges the source-owned support. -/
theorem modes_ssubset
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {current next : GeneratedCommonTimeReplayStage lineage}
    (step :
      NativeCommonTimeReplayStep
        lineage initialSubcritical current next) :
    current.modes ⊂ next.modes := by
  cases step with
  | expand missingNonempty =>
      rw [GeneratedCommonTimeReplayStage.next_modes]
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨current.modes_subset_nextModes, ?_⟩
      intro modesEq
      rcases missingNonempty with ⟨output, outputMem⟩
      have outputNext : output ∈ current.nextModes := by
        rw [current.nextModes_eq_modes_union_missing]
        exact Finset.mem_union_right _ outputMem
      have outputCurrent : output ∈ current.modes := by
        rw [modesEq]
        exact outputNext
      have outputNotCurrent : output ∉ current.modes := by
        have outputNotSupport :=
          ((mem_generatedMissingNonlinearModes_iff
            current.endpointSource output).mp outputMem).2
        rwa [current.endpointSource_generatedSupport]
          at outputNotSupport
      exact outputNotCurrent outputCurrent

end NativeCommonTimeReplayStep

/-! ## Maximal terminal-or-infinite replay runtime -/

structure GeneratedCommonTimeReplayTerminalRun
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) where
  terminal : GeneratedCommonTimeReplayStage lineage
  arrival :
    NativeReachable
      (initialCommonTimeReplayStage lineage)
      (generatedCommonTimeReplayRespond
        lineage initialSubcritical)
      terminal
  stopped :
    generatedCommonTimeReplayRespond
        lineage initialSubcritical terminal =
      none

theorem GeneratedCommonTimeReplayTerminalRun.residual_eq_zero
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    (run :
      GeneratedCommonTimeReplayTerminalRun
        lineage initialSubcritical) :
    run.terminal.endpointWholeResidual = 0 :=
  (generatedCommonTimeReplayRespond_eq_none_iff_residual_eq_zero
    lineage initialSubcritical run.terminal).mp run.stopped

private theorem exists_forcedCommonTimeReplayResponse
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (noTerminal :
      ¬ Nonempty
        (GeneratedCommonTimeReplayTerminalRun
          lineage initialSubcritical))
    (node :
      Σ current : GeneratedCommonTimeReplayStage lineage,
        NativeReachable
          (initialCommonTimeReplayStage lineage)
          (generatedCommonTimeReplayRespond
            lineage initialSubcritical)
          current) :
    ∃ response :
        Response
          (NativeCommonTimeReplayStep
            lineage initialSubcritical)
          node.1,
      generatedCommonTimeReplayRespond
          lineage initialSubcritical node.1 =
        some response := by
  cases generated :
      generatedCommonTimeReplayRespond
        lineage initialSubcritical node.1 with
  | none =>
      exact False.elim <|
        noTerminal <|
          ⟨{ terminal := node.1
             arrival := node.2
             stopped := generated }⟩
  | some response =>
      exact ⟨response, rfl⟩

private noncomputable def forcedCommonTimeReplayResponse
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (noTerminal :
      ¬ Nonempty
        (GeneratedCommonTimeReplayTerminalRun
          lineage initialSubcritical))
    (node :
      Σ current : GeneratedCommonTimeReplayStage lineage,
        NativeReachable
          (initialCommonTimeReplayStage lineage)
          (generatedCommonTimeReplayRespond
            lineage initialSubcritical)
          current) :
    Response
      (NativeCommonTimeReplayStep lineage initialSubcritical)
      node.1 :=
  Classical.choose <|
    exists_forcedCommonTimeReplayResponse
      lineage initialSubcritical noTerminal node

private theorem forcedCommonTimeReplayResponse_generated
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (noTerminal :
      ¬ Nonempty
        (GeneratedCommonTimeReplayTerminalRun
          lineage initialSubcritical))
    (node :
      Σ current : GeneratedCommonTimeReplayStage lineage,
        NativeReachable
          (initialCommonTimeReplayStage lineage)
          (generatedCommonTimeReplayRespond
            lineage initialSubcritical)
          current) :
    generatedCommonTimeReplayRespond
        lineage initialSubcritical node.1 =
      some
        (forcedCommonTimeReplayResponse
          lineage initialSubcritical noTerminal node) :=
  Classical.choose_spec <|
    exists_forcedCommonTimeReplayResponse
      lineage initialSubcritical noTerminal node

private noncomputable def infiniteCommonTimeReplayReachableRun
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (noTerminal :
      ¬ Nonempty
        (GeneratedCommonTimeReplayTerminalRun
          lineage initialSubcritical)) :
    ℕ →
      Σ current : GeneratedCommonTimeReplayStage lineage,
        NativeReachable
          (initialCommonTimeReplayStage lineage)
          (generatedCommonTimeReplayRespond
            lineage initialSubcritical)
          current
  | 0 =>
      ⟨initialCommonTimeReplayStage lineage,
        NativeReachable.initial⟩
  | index + 1 =>
      let node :=
        infiniteCommonTimeReplayReachableRun
          lineage initialSubcritical noTerminal index
      let response :=
        forcedCommonTimeReplayResponse
          lineage initialSubcritical noTerminal node
      ⟨response.1,
        NativeReachable.step node.2
          (forcedCommonTimeReplayResponse_generated
            lineage initialSubcritical noTerminal node)⟩

structure GeneratedCommonTimeReplayInfiniteLineage
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) where
  current : ℕ → GeneratedCommonTimeReplayStage lineage
  step :
    ∀ index : ℕ,
      NativeCommonTimeReplayStep lineage initialSubcritical
        (current index) (current (index + 1))
  generated :
    ∀ index : ℕ,
      generatedCommonTimeReplayRespond
          lineage initialSubcritical (current index) =
        some ⟨current (index + 1), step index⟩

private noncomputable def infiniteCommonTimeReplayLineageOfNoTerminal
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (noTerminal :
      ¬ Nonempty
        (GeneratedCommonTimeReplayTerminalRun
          lineage initialSubcritical)) :
    GeneratedCommonTimeReplayInfiniteLineage
      lineage initialSubcritical where
  current index :=
    (infiniteCommonTimeReplayReachableRun
      lineage initialSubcritical noTerminal index).1
  step index :=
    (forcedCommonTimeReplayResponse
      lineage initialSubcritical noTerminal
      (infiniteCommonTimeReplayReachableRun
        lineage initialSubcritical noTerminal index)).2
  generated index :=
    forcedCommonTimeReplayResponse_generated
      lineage initialSubcritical noTerminal
      (infiniteCommonTimeReplayReachableRun
        lineage initialSubcritical noTerminal index)

@[simp] theorem infiniteCommonTimeReplayLineageOfNoTerminal_current_zero
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (noTerminal :
      ¬ Nonempty
        (GeneratedCommonTimeReplayTerminalRun
          lineage initialSubcritical)) :
    (infiniteCommonTimeReplayLineageOfNoTerminal
      lineage initialSubcritical noTerminal).current 0 =
        initialCommonTimeReplayStage lineage :=
  rfl

namespace GeneratedCommonTimeReplayInfiniteLineage

theorem modes_strictMono
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    (replay :
      GeneratedCommonTimeReplayInfiniteLineage
        lineage initialSubcritical) :
    StrictMono (fun index => (replay.current index).modes) := by
  apply strictMono_nat_of_lt_succ
  intro index
  exact (replay.step index).modes_ssubset

theorem residual_ne_zero
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    (replay :
      GeneratedCommonTimeReplayInfiniteLineage
        lineage initialSubcritical)
    (index : ℕ) :
    (replay.current index).endpointWholeResidual ≠ 0 := by
  intro residualZero
  have stopped :=
    (generatedCommonTimeReplayRespond_eq_none_iff_residual_eq_zero
      lineage initialSubcritical (replay.current index)).mpr
      residualZero
  rw [replay.generated index] at stopped
  contradiction

end GeneratedCommonTimeReplayInfiniteLineage

inductive GeneratedCommonTimeReplaySubcriticalDisposition
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) : Type
  | terminal
      (run :
        GeneratedCommonTimeReplayTerminalRun
          lineage initialSubcritical)
  | infinite
      (replay :
        GeneratedCommonTimeReplayInfiniteLineage
          lineage initialSubcritical)
      (startsAtInitial :
        replay.current 0 =
          initialCommonTimeReplayStage lineage)

noncomputable def generatedCommonTimeReplaySubcriticalDisposition
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) :
    GeneratedCommonTimeReplaySubcriticalDisposition
      lineage initialSubcritical := by
  by_cases terminalExists :
      Nonempty
        (GeneratedCommonTimeReplayTerminalRun
          lineage initialSubcritical)
  · exact .terminal (Classical.choice terminalExists)
  · exact
      .infinite
        (infiniteCommonTimeReplayLineageOfNoTerminal
          lineage initialSubcritical terminalExists)
        (infiniteCommonTimeReplayLineageOfNoTerminal_current_zero
          lineage initialSubcritical terminalExists)

/--
Final Type-valued source disposition.  A fixed half-critical crossing,
faithful endpoint residual closure after a finite source-owned replay path,
and a genuine infinite strictly refining common-time replay lineage are the
only outcomes.
-/
inductive GeneratedWholeResidualCommonTimeReplayDisposition
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) : Type
  | halfCritical
      (crossing : lineageHalfCriticalCrossing lineage 0)
  | terminal
      (initialSubcritical :
        ¬ lineageHalfCriticalCrossing lineage 0)
      (run :
        GeneratedCommonTimeReplayTerminalRun
          lineage initialSubcritical)
  | infinite
      (initialSubcritical :
        ¬ lineageHalfCriticalCrossing lineage 0)
      (replay :
        GeneratedCommonTimeReplayInfiniteLineage
          lineage initialSubcritical)
      (startsAtInitial :
        replay.current 0 =
          initialCommonTimeReplayStage lineage)

/--
The native whole-residual lineage itself generates the exhaustive
half-critical / terminal replay / infinite replay outcome.  No branch or
runtime certificate appears in the producer mouth.
-/
noncomputable def generatedWholeResidualCommonTimeReplayDisposition
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    GeneratedWholeResidualCommonTimeReplayDisposition lineage := by
  by_cases crossing :
      lineageHalfCriticalCrossing lineage 0
  · exact .halfCritical crossing
  · cases
      generatedCommonTimeReplaySubcriticalDisposition
        lineage crossing with
    | terminal run =>
        exact .terminal crossing run
    | infinite replay startsAtInitial =>
        exact .infinite crossing replay startsAtInitial

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay
end NavierStokes
end SaturationMonoid
