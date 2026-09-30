import H0mework.NavierStokes.Restart.GlobalPhysicalResidualNativeRedirect

/-!
# The endpoint-written responsibility is the active global physical residual process

The endpoint macro does not merely archive its aligned component/kinetic
tail.  Its kinetic coordinate has a concrete weighted Biot--Savart image,
and that image is exactly the global physical residual tail on the identical
macro stage.  Literal shift and the uniquely forced residual trace commute
with this map.

Each nonzero adjacent forced trace is then consumed before quotient.  Its two
selected contacts determine one exact finite native segment; common endpoint
cancellation identifies the negative trace with that segment's collective
unforced velocity write.  The same segment internally selects a changed
native edge, its canonical complement no-silence witness, and the existing
tangent/pair/heat native exhaustion.

The source-facing theorem takes only an actual infinite endpoint lineage and
one stage.  It retains the existing unforced physical macro successor and
generates the complete zero-or-native disposition for every update of the
written residual process.  No branch, residual value, segment, edge, output,
pair, time, faithfulness law, or settlement witness is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open Filter Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHeatCommutatorNativeVelocityPairRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomNativeCausalRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCollectiveCausalGapWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomComplementNoSilentWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomQuadraticBoundaryCocycle
open AffineRelaxation
open ResidualProjection

noncomputable section

/-! ## Concrete morphism from the written aligned carrier -/

/-- Forget only the component-occurrence coordinate and apply the already
generated complete weighted Biot--Savart morphism to every kinetic row. -/
def wholeRestartAlignedResponsibilityToVelocityResidualTail :
    WholeRestartEndpointAlignedResponsibilityTail →ₗ[ℂ]
      WholeRestartEndpointVelocityResidualTail where
  toFun residual offset :=
    wholeRestartKineticToVelocityCLM (residual offset).2
  map_add' left right := by
    funext offset
    change
      wholeRestartKineticToVelocityCLM
          ((left offset).2 + (right offset).2) =
        wholeRestartKineticToVelocityCLM (left offset).2 +
          wholeRestartKineticToVelocityCLM (right offset).2
    exact map_add wholeRestartKineticToVelocityCLM _ _
  map_smul' scalar residual := by
    funext offset
    change
      wholeRestartKineticToVelocityCLM
          (scalar • (residual offset).2) =
        scalar • wholeRestartKineticToVelocityCLM (residual offset).2
    exact map_smul wholeRestartKineticToVelocityCLM scalar _

/-- The concrete aligned-to-physical map commutes with literal selected
occurrence shift on arbitrary whole responsibility tails. -/
theorem wholeRestartAlignedResponsibilityToVelocityResidualTail_keep_commutes
    (residual : WholeRestartEndpointAlignedResponsibilityTail) :
    wholeRestartAlignedResponsibilityToVelocityResidualTail
        (wholeRestartEndpointAlignedResponsibilityTailKeep residual) =
      wholeRestartEndpointVelocityResidualTailKeep
        (wholeRestartAlignedResponsibilityToVelocityResidualTail residual) := by
  rfl

/-- Hence the uniquely forced complement of the two keeps commutes as well. -/
theorem wholeRestartAlignedResponsibilityToVelocityResidualTail_trace_commutes
    (residual : WholeRestartEndpointAlignedResponsibilityTail) :
    wholeRestartAlignedResponsibilityToVelocityResidualTail
        (linearResidualTrace
          wholeRestartEndpointAlignedResponsibilityTailKeep residual) =
      linearResidualTrace
        wholeRestartEndpointVelocityResidualTailKeep
        (wholeRestartAlignedResponsibilityToVelocityResidualTail residual) := by
  funext offset
  exact map_sub wholeRestartKineticToVelocityCLM _ _

/-- The source-generated aligned process has the literal additive path
state.  This identifies every later active tail with an iterate of the tail
written at the endpoint event. -/
@[simp] theorem
    generatedWholeRestartEndpointAlignedResponsibilityEffectiveProcess_pathState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index steps : ℕ) :
    (generatedWholeRestartEndpointAlignedResponsibilityEffectiveProcess
      initial elapsedBounded).pathState index steps = index + steps := by
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
      rw [EffectiveResidualProcess.pathState_succ, inductionHypothesis]
      rfl

/-- On the actual source-selected lineage, the entire aligned responsibility
tail maps to the physical endpoint residual tail at the same index. -/
theorem wholeRestartAlignedResponsibilityToVelocityResidualTail_generated
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    wholeRestartAlignedResponsibilityToVelocityResidualTail
        (wholeRestartEndpointAlignedResponsibilityTail
          initial elapsedBounded index) =
      wholeRestartEndpointVelocityResidualTail
        initial elapsedBounded index := by
  funext offset
  exact wholeRestartKineticToVelocityCLM_alignedResidual
    initial elapsedBounded (index + offset)

/-- The endpoint macro's written ledger is exactly the initial physical
residual tail, not a parallel diagnostic record. -/
theorem wholeRestartEndpointAlignedMacro_writtenToVelocityResidualTail
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartAlignedResponsibilityToVelocityResidualTail
        (wholeRestartEndpointAlignedMacroTraceLedger initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead)) =
      wholeRestartEndpointVelocityResidualTail
        initial elapsedBounded 0 := by
  funext index
  change
    wholeRestartKineticToVelocityCLM
        ((wholeRestartEndpointAlignedMacroTraceLedger
          initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate
            accumulationRead)) index).2 =
      wholeRestartEndpointVelocityResidual
        initial elapsedBounded (0 + index)
  rw [wholeRestartEndpointAlignedMacro_writtenKinetic]
  simpa only [Nat.zero_add] using
    (wholeRestartKineticToVelocityCLM_alignedResidual
      initial elapsedBounded index)

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- At a global macro stage, the exact aligned ledger written by that event
maps to the initial state of the already generated global physical residual
process. -/
theorem globalStagePhysicalResidualTail_eq_writtenAlignedResponsibility
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) :
    wholeRestartAlignedResponsibilityToVelocityResidualTail
        (wholeRestartEndpointAlignedMacroTraceLedger
          (lineage.current stage)
          (lineage.step stage).elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead)) =
      globalStagePhysicalResidualTail lineage stage 0 := by
  rw [wholeRestartEndpointAlignedMacro_writtenToVelocityResidualTail]
  funext index
  change
    wholeRestartEndpointVelocityResidual
        (lineage.current stage)
        (lineage.step stage).elapsedBounded (0 + index) =
      lineage.globalStagePhysicalResidual stage (0 + index)
  exact
    (lineage.globalStagePhysicalResidual_eq_endpointVelocityResidual
      stage (0 + index)).symm

/-- Every active iterate of the endpoint-written aligned process maps to the
identically indexed state of the global physical residual process. -/
theorem globalStagePhysicalResidualProcess_eq_writtenAlignedProcess
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) :
    wholeRestartAlignedResponsibilityToVelocityResidualTail
        ((generatedWholeRestartEndpointAlignedResponsibilityEffectiveProcess
          (lineage.current stage)
          (lineage.step stage).elapsedBounded).residual
          ((generatedWholeRestartEndpointAlignedResponsibilityEffectiveProcess
            (lineage.current stage)
            (lineage.step stage).elapsedBounded).pathState 0 index)) =
      (generatedGlobalStagePhysicalResidualEffectiveProcess
        lineage stage).residual index := by
  rw [
    generatedWholeRestartEndpointAlignedResponsibilityEffectiveProcess_pathState]
  simp only [Nat.zero_add]
  change
    wholeRestartAlignedResponsibilityToVelocityResidualTail
        (wholeRestartEndpointAlignedResponsibilityTail
          (lineage.current stage)
          (lineage.step stage).elapsedBounded index) =
      globalStagePhysicalResidualTail lineage stage index
  rw [
    wholeRestartAlignedResponsibilityToVelocityResidualTail_generated]
  funext offset
  exact
    (lineage.globalStagePhysicalResidual_eq_endpointVelocityResidual
      stage (index + offset)).symm

/-! ## Every adjacent forced trace is an exact native segment write -/

/-- One shift trace of the global physical residual is the negative
collective unforced write between the two adjacent source-selected contacts.
The sign is forced by `old residual = new residual + trace`. -/
theorem globalStagePhysicalResidualTrace_eq_neg_collectiveWrite
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) :
    let endpointReceipt :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        (lineage.current stage)
        (lineage.step stage).elapsedBounded).family.endpointReceipt
    let segmentStart := endpointReceipt.subsequence index
    let segmentFinish := endpointReceipt.subsequence (index + 1)
    let segmentSteps := segmentFinish - segmentStart
    linearResidualTrace
        wholeRestartEndpointVelocityResidualTailKeep
        (globalStagePhysicalResidualTail lineage stage index) 0 =
      -wholeRestartCollectiveCausalVelocityWrite
        (lineage.current stage) segmentStart segmentSteps := by
  dsimp only
  let endpointReceipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      (lineage.current stage)
      (lineage.step stage).elapsedBounded).family.endpointReceipt
  let segmentStart := endpointReceipt.subsequence index
  let segmentFinish := endpointReceipt.subsequence (index + 1)
  let segmentSteps := segmentFinish - segmentStart
  have segmentStartLtFinish : segmentStart < segmentFinish := by
    exact endpointReceipt.subsequence_strictMono (by omega)
  have segmentFinishEq :
      segmentStart + segmentSteps = segmentFinish := by
    dsimp only [segmentSteps]
    omega
  rw [wholeRestartCollectiveCausalVelocityWrite_eq_gap, segmentFinishEq]
  change
    lineage.globalStagePhysicalResidual stage index -
        lineage.globalStagePhysicalResidual stage (index + 1) =
      -(wholeRestartContactVelocityState
          (lineage.current stage) segmentFinish -
        wholeRestartContactVelocityState
          (lineage.current stage) segmentStart)
  rw [lineage.globalStagePhysicalResidual_eq_endpointVelocityResidual,
    lineage.globalStagePhysicalResidual_eq_endpointVelocityResidual]
  change
    (wholeRestartContactVelocityState
          (lineage.current stage) segmentStart -
        endpointReceipt.velocityEndpoint) -
      (wholeRestartContactVelocityState
          (lineage.current stage) segmentFinish -
        endpointReceipt.velocityEndpoint) =
      -(wholeRestartContactVelocityState
          (lineage.current stage) segmentFinish -
        wholeRestartContactVelocityState
          (lineage.current stage) segmentStart)
  abel

/-- The same forced trace can be computed before projection in the active
aligned process written by the endpoint macro. -/
theorem globalStagePhysicalResidualTrace_eq_writtenAlignedTraceImage
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) :
    wholeRestartAlignedResponsibilityToVelocityResidualTail
        (linearResidualTrace
          wholeRestartEndpointAlignedResponsibilityTailKeep
          ((generatedWholeRestartEndpointAlignedResponsibilityEffectiveProcess
            (lineage.current stage)
            (lineage.step stage).elapsedBounded).residual
            ((generatedWholeRestartEndpointAlignedResponsibilityEffectiveProcess
              (lineage.current stage)
              (lineage.step stage).elapsedBounded).pathState 0 index))) =
      linearResidualTrace
        wholeRestartEndpointVelocityResidualTailKeep
        ((generatedGlobalStagePhysicalResidualEffectiveProcess
          lineage stage).residual index) := by
  rw [
    wholeRestartAlignedResponsibilityToVelocityResidualTail_trace_commutes]
  congr 1
  exact
    lineage.globalStagePhysicalResidualProcess_eq_writtenAlignedProcess
      stage index

/-- A nonzero adjacent forced trace together with the exact native segment
and the same-edge pre-quotient settlement generated inside that segment. -/
structure GlobalStagePhysicalResidualAdjacentNativeRedirect
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage residualIndex : ℕ) where
  segmentStart : ℕ
  segmentSteps : ℕ
  segmentSteps_pos : 0 < segmentSteps
  segmentStart_eq_selectedContact :
    segmentStart =
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        (lineage.current stage)
        (lineage.step stage).elapsedBounded).family.endpointReceipt.subsequence
          residualIndex
  segmentFinish_eq_selectedContact :
    segmentStart + segmentSteps =
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        (lineage.current stage)
        (lineage.step stage).elapsedBounded).family.endpointReceipt.subsequence
          (residualIndex + 1)
  forcedTrace_eq_neg_collectiveWrite :
    linearResidualTrace
        wholeRestartEndpointVelocityResidualTailKeep
        (globalStagePhysicalResidualTail
          lineage stage residualIndex) 0 =
      -wholeRestartCollectiveCausalVelocityWrite
        (lineage.current stage) segmentStart segmentSteps
  forcedTrace_ne_zero :
    linearResidualTrace
        wholeRestartEndpointVelocityResidualTailKeep
        (globalStagePhysicalResidualTail
          lineage stage residualIndex) 0 ≠ 0
  nativeEdgeIndex : ℕ
  segmentStart_le_nativeEdgeIndex :
    segmentStart ≤ nativeEdgeIndex
  nativeEdgeIndex_lt_segmentFinish :
    nativeEdgeIndex < segmentStart + segmentSteps
  nativeWrite_ne_zero :
    wholeRestartNativeCausalVelocityWrite
      (lineage.current stage) nativeEdgeIndex ≠ 0
  nativeRun_succ :
    run (lineage.current stage) (nativeEdgeIndex + 1) =
      (run (lineage.current stage) nativeEdgeIndex).next
  nativeTime_pos :
    0 <
      (run
        (lineage.current stage)
        nativeEdgeIndex).nextContact.time.1
  complementOutput : IntegerWavevector
  complementOutput_ne_zero : complementOutput ≠ 0
  complementOutputIncrement_ne_zero :
    (run
        (lineage.current stage)
        nativeEdgeIndex).nextContact.physicalState complementOutput -
      (run
        (lineage.current stage)
        nativeEdgeIndex).contact.physicalState complementOutput ≠ 0
  complementRegistration_injective :
    Function.Injective
      (wholeRestartActualOutputEdgeRegistration
        (lineage.current stage) nativeEdgeIndex complementOutput)
  complementJointSilent_false :
    ¬ wholeRestartActualOutputCausalJointSilent
      (lineage.current stage) nativeEdgeIndex complementOutput
  energyPayingWave : NonzeroIntegerWavevector
  energyPayingRow_negative :
    RCLike.re (inner ℂ
      (wholeRestartContactVelocityState
        (lineage.current stage) nativeEdgeIndex energyPayingWave)
      (euclideanCoordinateRow
        (biotSavartVelocityCoefficient energyPayingWave.1
          (wholeRestartCausalTangentGain
                (lineage.current stage)
                nativeEdgeIndex energyPayingWave.1 •
              wholeRestartCrossingUnforcedTangentRow
                (lineage.current stage)
                nativeEdgeIndex energyPayingWave.1 +
            ∑' first : IntegerWavevector,
              wholeRestartPairDuhamelInnovationOccurrence
                (lineage.current stage)
                nativeEdgeIndex energyPayingWave.1 first)))) < 0
  nativeExhaustion :
    ((∃ tangentNonzero :
            wholeRestartCrossingUnforcedTangentRow
              (lineage.current stage) nativeEdgeIndex ≠ 0,
        ∃ localTime : ℝ,
          0 < localTime ∧
            localTime <
              (run
                (lineage.current stage)
                nativeEdgeIndex).nextContact.time.1 ∧
            localTime *
                  (wholeRestartCrossingContinuousUnforcedTangentDensity
                    (lineage.current stage)
                    nativeEdgeIndex tangentNonzero 0 / 2) ≤
                ∫ time in (0 : ℝ)..localTime,
                  wholeRestartCrossingContinuousUnforcedTangentDensity
                    (lineage.current stage)
                    nativeEdgeIndex tangentNonzero time ∧
            0 <
              ∫ time in (0 : ℝ)..localTime,
                wholeRestartCrossingContinuousUnforcedTangentDensity
                  (lineage.current stage)
                  nativeEdgeIndex tangentNonzero time ∧
            (∫ time in (0 : ℝ)..localTime,
                wholeRestartCrossingContinuousUnforcedTangentDensity
                  (lineage.current stage)
                  nativeEdgeIndex tangentNonzero time) ≤
              ‖(run
                (lineage.current stage)
                nativeEdgeIndex).nextContact.prefixReceipt.wholeTangent‖ ^ 2) ∨
      ∃ first : IntegerWavevector,
        wholeRestartPairDuhamelInnovationOccurrence
              (lineage.current stage)
              nativeEdgeIndex energyPayingWave.1 first ≠ 0 ∧
          (wholeRestartNextPairOccurrence
                (lineage.current stage)
                nativeEdgeIndex energyPayingWave.1 first ≠ 0 ∨
            ∃ time :
                Icc (0 : ℝ)
                  (run
                    (lineage.current stage)
                    nativeEdgeIndex).nextContact.time.1,
              wholeRestartPairOccurrenceTrace
                (lineage.current stage)
                nativeEdgeIndex energyPayingWave.1 first time ≠ 0) ∧
          (wholeRestartVelocityTriadHeatCommutatorTrace
                (lineage.current stage)
                nativeEdgeIndex first (energyPayingWave.1 - first) = 0 ∨
            ∃ time :
                Icc (0 : ℝ)
                  (run
                    (lineage.current stage)
                    nativeEdgeIndex).nextContact.time.1,
              actualWholeVelocityBilinearEnergyOccurrence
                  (run
                    (lineage.current stage)
                    nativeEdgeIndex).nextContact.prefixReceipt
                  first (energyPayingWave.1 - first) time ≠ 0 ∧
                actualWholeContinuousVelocityPairVector
                    (run
                      (lineage.current stage)
                      nativeEdgeIndex).nextContact.prefixReceipt
                    first (energyPayingWave.1 - first) time ≠ 0 ∧
                (wholeRestartNextVelocityPairOccurrence
                      (lineage.current stage)
                      nativeEdgeIndex first (energyPayingWave.1 - first) ≠ 0 ∨
                  (linearResidualTrace
                      wholeRestartSplicedVelocityPairOccurrenceTailKeep
                      (wholeRestartSplicedVelocityPairOccurrenceTail
                        (lineage.current stage)
                        nativeEdgeIndex time 0) 0)
                        first (energyPayingWave.1 - first) ≠ 0) ∧
                run (lineage.current stage) (nativeEdgeIndex + 1) =
                  (run
                    (lineage.current stage)
                    nativeEdgeIndex).next))

/-- A nonzero adjacent forced trace internally generates its exact
same-segment native redirect.  All edge-level witnesses are selected from
the two contacts already fixed by this residual update. -/
theorem
    globalStagePhysicalResidualTrace_ne_zero_generates_adjacentNativeRedirect
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ)
    (traceNonzero :
      linearResidualTrace
          wholeRestartEndpointVelocityResidualTailKeep
          (globalStagePhysicalResidualTail lineage stage index) 0 ≠ 0) :
    Nonempty
      (GlobalStagePhysicalResidualAdjacentNativeRedirect
        lineage stage index) := by
  let endpointReceipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      (lineage.current stage)
      (lineage.step stage).elapsedBounded).family.endpointReceipt
  let segmentStart := endpointReceipt.subsequence index
  let segmentFinish := endpointReceipt.subsequence (index + 1)
  let segmentSteps := segmentFinish - segmentStart
  have segmentStartLtFinish : segmentStart < segmentFinish := by
    exact endpointReceipt.subsequence_strictMono (by omega)
  have segmentStepsPos : 0 < segmentSteps := by
    dsimp only [segmentSteps]
    omega
  have segmentFinishEq :
      segmentStart + segmentSteps = segmentFinish := by
    dsimp only [segmentSteps]
    omega
  have traceEq :
      linearResidualTrace
          wholeRestartEndpointVelocityResidualTailKeep
          (globalStagePhysicalResidualTail lineage stage index) 0 =
        -wholeRestartCollectiveCausalVelocityWrite
          (lineage.current stage) segmentStart segmentSteps := by
    exact lineage.globalStagePhysicalResidualTrace_eq_neg_collectiveWrite
      stage index
  have collectiveNonzero :
      wholeRestartCollectiveCausalVelocityWrite
        (lineage.current stage) segmentStart segmentSteps ≠ 0 := by
    intro collectiveZero
    apply traceNonzero
    rw [traceEq, collectiveZero, neg_zero]
  have segmentEndpointNe :
      wholeRestartContactVelocityState
          (lineage.current stage) segmentStart ≠
        wholeRestartContactVelocityState
          (lineage.current stage) segmentFinish := by
    intro endpointEq
    apply collectiveNonzero
    rw [wholeRestartCollectiveCausalVelocityWrite_eq_gap,
      segmentFinishEq, endpointEq, sub_self]
  obtain
      ⟨nativeEdgeIndex, startLeEdge, edgeLtFinish, edgeChange⟩ :=
    exists_adjacent_native_change_of_endpoint_change
      (wholeRestartContactVelocityState (lineage.current stage))
      segmentStartLtFinish segmentEndpointNe
  have nativeWriteNe :
      wholeRestartNativeCausalVelocityWrite
        (lineage.current stage) nativeEdgeIndex ≠ 0 := by
    rw [wholeRestartNativeCausalVelocityWrite_eq_adjacent]
    exact sub_ne_zero.mpr edgeChange.symm
  have nativeStateNe :
      (run
          (lineage.current stage)
          nativeEdgeIndex).nextContact.physicalState ≠
        (run
          (lineage.current stage)
          nativeEdgeIndex).contact.physicalState := by
    intro nativeStateEq
    apply edgeChange
    unfold wholeRestartContactVelocityState
    rw [run_succ]
    change
      puncturedWholeVelocityEuclideanState
          (run
            (lineage.current stage)
            nativeEdgeIndex).contact.physicalState =
        puncturedWholeVelocityEuclideanState
          (run
            (lineage.current stage)
            nativeEdgeIndex).nextContact.physicalState
    rw [nativeStateEq]
  obtain
      ⟨complementOutput, complementOutputNonzero,
        complementIncrementNonzero, _causalSplit, _causalResponsibility⟩ :=
    nativePhysicalChange_generates_causalResponsibility
      (lineage.current stage) nativeEdgeIndex nativeStateNe
  have registrationInjective :=
    wholeRestartActualOutputEdgeRegistration_injective_of_increment_ne_zero
      (lineage.current stage) nativeEdgeIndex complementOutput
      complementIncrementNonzero
  have noJointSilence :=
    wholeRestartActualOutputIncrement_ne_zero_excludes_causalJointSilent
      (lineage.current stage) nativeEdgeIndex complementOutput
      complementOutputNonzero complementIncrementNonzero
  obtain ⟨energyPayingWave, energyPayingNegative, nativeExhaustion⟩ :=
    wholeRestartNativeCausalVelocityWrite_ne_zero_generates_energyPaying_nativeExhaustion
      (lineage.current stage) nativeEdgeIndex nativeWriteNe
  exact
    ⟨{ segmentStart := segmentStart
       segmentSteps := segmentSteps
       segmentSteps_pos := segmentStepsPos
       segmentStart_eq_selectedContact := rfl
       segmentFinish_eq_selectedContact := segmentFinishEq
       forcedTrace_eq_neg_collectiveWrite := traceEq
       forcedTrace_ne_zero := traceNonzero
       nativeEdgeIndex := nativeEdgeIndex
       segmentStart_le_nativeEdgeIndex := startLeEdge
       nativeEdgeIndex_lt_segmentFinish := by
         simpa only [segmentFinishEq] using edgeLtFinish
       nativeWrite_ne_zero := nativeWriteNe
       nativeRun_succ := rfl
       nativeTime_pos :=
         (run
           (lineage.current stage)
           nativeEdgeIndex).nextContact.time_pos
       complementOutput := complementOutput
       complementOutput_ne_zero := complementOutputNonzero
       complementOutputIncrement_ne_zero := complementIncrementNonzero
       complementRegistration_injective := registrationInjective
       complementJointSilent_false := noJointSilence
       energyPayingWave := energyPayingWave
       energyPayingRow_negative := energyPayingNegative
       nativeExhaustion := nativeExhaustion }⟩

/-- Total source-owned disposition of every adjacent update in the written
physical residual process: faithful zero at the complete physical carrier,
or an exact same-segment native redirect with no silent component sink. -/
theorem
    globalStagePhysicalResidualTrace_generates_zero_or_adjacentNativeRedirect
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) :
    linearResidualTrace
          wholeRestartEndpointVelocityResidualTailKeep
          (globalStagePhysicalResidualTail lineage stage index) 0 = 0 ∨
      Nonempty
        (GlobalStagePhysicalResidualAdjacentNativeRedirect
          lineage stage index) := by
  by_cases traceZero :
      linearResidualTrace
          wholeRestartEndpointVelocityResidualTailKeep
          (globalStagePhysicalResidualTail lineage stage index) 0 = 0
  · exact Or.inl traceZero
  · exact Or.inr
      (lineage.globalStagePhysicalResidualTrace_ne_zero_generates_adjacentNativeRedirect
        stage index traceZero)

/-- A positive cofinal residual segment cannot hide its change in a finite
sum: one adjacent update inside the same residual-index interval is nonzero,
and therefore generates the adjacent native redirect above. -/
theorem
    GlobalStagePhysicalResidualSameSegmentNativeRedirect.generates_adjacent
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage requestedStart : ℕ}
    (receipt :
      GlobalStagePhysicalResidualSameSegmentNativeRedirect
        lineage stage requestedStart) :
    ∃ residualIndex : ℕ,
      requestedStart ≤ residualIndex ∧
        residualIndex < receipt.laterResidualIndex ∧
        Nonempty
          (GlobalStagePhysicalResidualAdjacentNativeRedirect
            lineage stage residualIndex) := by
  have collectiveNonzero :
      wholeRestartCollectiveCausalVelocityWrite
        (lineage.current stage) receipt.segmentStart receipt.segmentSteps ≠
          0 := by
    intro collectiveZero
    have lower := receipt.defect_half_lt_collectiveWrite_norm_sq
    rw [collectiveZero, norm_zero] at lower
    norm_num at lower
    linarith [receipt.defectPositive]
  have residualDifferenceNonzero :
      lineage.globalStagePhysicalResidual
            stage receipt.laterResidualIndex -
          lineage.globalStagePhysicalResidual
            stage receipt.earlierResidualIndex ≠ 0 := by
    rw [receipt.residualDifference_eq_collectiveWrite]
    exact collectiveNonzero
  have residualEndpointsNe :
      lineage.globalStagePhysicalResidual
          stage receipt.earlierResidualIndex ≠
        lineage.globalStagePhysicalResidual
          stage receipt.laterResidualIndex :=
    (sub_ne_zero.mp residualDifferenceNonzero).symm
  obtain
      ⟨residualIndex, earlierLeIndex, indexLtLater, adjacentChange⟩ :=
    exists_adjacent_native_change_of_endpoint_change
      (lineage.globalStagePhysicalResidual stage)
      receipt.earlierResidualIndex_lt_laterResidualIndex
      residualEndpointsNe
  have traceNonzero :
      linearResidualTrace
          wholeRestartEndpointVelocityResidualTailKeep
          (globalStagePhysicalResidualTail
            lineage stage residualIndex) 0 ≠ 0 := by
    change
      lineage.globalStagePhysicalResidual stage residualIndex -
          lineage.globalStagePhysicalResidual stage (residualIndex + 1) ≠ 0
    exact sub_ne_zero.mpr adjacentChange
  exact
    ⟨residualIndex,
      receipt.requestedStart_le_earlierResidualIndex.trans earlierLeIndex,
      indexLtLater,
      lineage.globalStagePhysicalResidualTrace_ne_zero_generates_adjacentNativeRedirect
        stage residualIndex traceNonzero⟩

/-- Total stage disposition on the active written process.  The zero atom
closes, while the positive branch source-generates cofinally many nonzero
adjacent physical traces and their exact native settlements. -/
theorem
    globalStagePhysicalResidual_generates_zero_or_cofinal_adjacentNativeRedirect
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) :
    infiniteEndpointMacroStageKineticDefect lineage stage = 0 ∨
      ∀ requestedStart : ℕ,
        ∃ residualIndex : ℕ,
          requestedStart ≤ residualIndex ∧
            Nonempty
              (GlobalStagePhysicalResidualAdjacentNativeRedirect
                lineage stage residualIndex) := by
  rcases
      (lineage.globalStagePhysicalResidual_generates_zero_or_sameSegment_nativeRedirect
        stage).2 with
    defectZero | cofinalSegment
  · exact Or.inl defectZero
  · right
    intro requestedStart
    obtain ⟨segmentReceipt⟩ := cofinalSegment requestedStart
    obtain
        ⟨residualIndex, requestedLeIndex, _indexLtLater,
          adjacentReceipt⟩ :=
      segmentReceipt.generates_adjacent
    exact ⟨residualIndex, requestedLeIndex, adjacentReceipt⟩

/-- One source-facing endpoint stage now writes its existing unforced
physical successor and, in that identical event, starts the active global
physical residual process.  Every iterate and forced trace is the concrete
image of the endpoint-written aligned carrier; every nonzero adjacent trace
immediately enters its exact native complement/tangent/pair/heat settlement.

The final zero/positive atom split is also selected by the same stage, so no
caller-supplied branch or nonzero witness remains in the public mouth. -/
theorem
    globalStageAlignedMacroWrite_generates_activePhysicalResidualSettlement
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) :
    (wholeRestartEndpointAlignedMacroFrame
        (lineage.current stage)
        (lineage.step stage).elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 =
        lineage.current (stage + 1) ∧
      wholeRestartAlignedResponsibilityToVelocityResidualTail
          (wholeRestartEndpointAlignedMacroTraceLedger
            (lineage.current stage)
            (lineage.step stage).elapsedBounded
            (wholeRestartEndpointComponentMacroUpdate accumulationRead)) =
        (generatedGlobalStagePhysicalResidualEffectiveProcess
          lineage stage).residual 0 ∧
      (∀ index : ℕ,
        wholeRestartAlignedResponsibilityToVelocityResidualTail
            ((generatedWholeRestartEndpointAlignedResponsibilityEffectiveProcess
              (lineage.current stage)
              (lineage.step stage).elapsedBounded).residual
              ((generatedWholeRestartEndpointAlignedResponsibilityEffectiveProcess
                (lineage.current stage)
                (lineage.step stage).elapsedBounded).pathState 0 index)) =
          (generatedGlobalStagePhysicalResidualEffectiveProcess
            lineage stage).residual index ∧
        wholeRestartAlignedResponsibilityToVelocityResidualTail
            (linearResidualTrace
              wholeRestartEndpointAlignedResponsibilityTailKeep
              ((generatedWholeRestartEndpointAlignedResponsibilityEffectiveProcess
                (lineage.current stage)
                (lineage.step stage).elapsedBounded).residual
                ((generatedWholeRestartEndpointAlignedResponsibilityEffectiveProcess
                  (lineage.current stage)
                  (lineage.step stage).elapsedBounded).pathState 0 index))) =
          linearResidualTrace
            wholeRestartEndpointVelocityResidualTailKeep
            ((generatedGlobalStagePhysicalResidualEffectiveProcess
              lineage stage).residual index)) ∧
      (∀ index : ℕ,
        linearResidualTrace
              wholeRestartEndpointVelocityResidualTailKeep
              (globalStagePhysicalResidualTail lineage stage index) 0 = 0 ∨
          Nonempty
            (GlobalStagePhysicalResidualAdjacentNativeRedirect
              lineage stage index)) ∧
      (infiniteEndpointMacroStageKineticDefect lineage stage = 0 ∨
        ∀ requestedStart : ℕ,
          ∃ residualIndex : ℕ,
            requestedStart ≤ residualIndex ∧
              Nonempty
                (GlobalStagePhysicalResidualAdjacentNativeRedirect
                  lineage stage residualIndex)) := by
  refine ⟨(lineage.step stage).next_eq_alignedMacroPhysical.symm, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa only [
      generatedGlobalStagePhysicalResidualEffectiveProcess] using
      lineage.globalStagePhysicalResidualTail_eq_writtenAlignedResponsibility
        stage
  refine ⟨?_, ?_⟩
  · intro index
    exact
      ⟨lineage.globalStagePhysicalResidualProcess_eq_writtenAlignedProcess
          stage index,
        lineage.globalStagePhysicalResidualTrace_eq_writtenAlignedTraceImage
          stage index⟩
  refine ⟨?_, ?_⟩
  · intro index
    exact
      lineage.globalStagePhysicalResidualTrace_generates_zero_or_adjacentNativeRedirect
        stage index
  exact
    lineage.globalStagePhysicalResidual_generates_zero_or_cofinal_adjacentNativeRedirect
      stage

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
