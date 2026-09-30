import H0mework.NavierStokes.VelocityEndpoint.GlobalPhysicalResidualTransport
import H0mework.NavierStokes.EndpointWork.QuadraticBoundaryCocycle

/-!
# Native redirect of the global physical endpoint residual

The global physical residual is the difference between one actual
source-selected contact and the generated velocity endpoint at the same
macro-stage accumulation time.  Two occurrences therefore have a common
endpoint.  Subtracting them cancels that endpoint exactly and leaves the
collective physical write on the intervening finite native path.

This module consumes that equality before any Fourier quotient.  A positive
stage defect generates two separated residual occurrences, the exact actual
segment between their contacts, a changed native edge inside that segment,
the same-edge canonical complement no-silence witness, and the existing
energy-paying tangent/pair/heat native exhaustion.

The public theorem has no defect branch, residual endpoints, finite segment,
edge, output, Fourier wave, pair, time, or settlement premise.  All of them
are generated from one actual macro stage.
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
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
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
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCofinalPhysicalSeparation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCollectiveCausalGapWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomComplementNoSilentWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomQuadraticBoundaryCocycle
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointCofinalPairDuhamelMacroWrite
open AffineRelaxation

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- One source-generated positive global residual segment, together with a
changed native edge selected inside that exact segment and the existing
same-edge componentwise native exhaustion. -/
structure GlobalStagePhysicalResidualSameSegmentNativeRedirect
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage requestedStart : ℕ) where
  defectPositive :
    0 < infiniteEndpointMacroStageKineticDefect lineage stage
  earlierResidualIndex : ℕ
  laterResidualIndex : ℕ
  requestedStart_le_earlierResidualIndex :
    requestedStart ≤ earlierResidualIndex
  earlierResidualIndex_lt_laterResidualIndex :
    earlierResidualIndex < laterResidualIndex
  segmentStart : ℕ
  segmentSteps : ℕ
  requestedStart_le_segmentStart :
    requestedStart ≤ segmentStart
  segmentSteps_pos : 0 < segmentSteps
  segmentStart_eq_selectedContact :
    segmentStart =
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        (lineage.current stage)
        (lineage.step stage).elapsedBounded).family.endpointReceipt.subsequence
          earlierResidualIndex
  segmentFinish_eq_selectedContact :
    segmentStart + segmentSteps =
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        (lineage.current stage)
        (lineage.step stage).elapsedBounded).family.endpointReceipt.subsequence
          laterResidualIndex
  residualDifference_eq_collectiveWrite :
    lineage.globalStagePhysicalResidual stage laterResidualIndex -
        lineage.globalStagePhysicalResidual stage earlierResidualIndex =
      wholeRestartCollectiveCausalVelocityWrite
        (lineage.current stage) segmentStart segmentSteps
  defect_half_lt_collectiveWrite_norm_sq :
    infiniteEndpointMacroStageKineticDefect lineage stage / 2 <
      ‖wholeRestartCollectiveCausalVelocityWrite
        (lineage.current stage) segmentStart segmentSteps‖ ^ 2
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

/-- A positive stage's complete global physical residual generates, after
every requested native index, a finite residual difference whose common
endpoint cancels to the exact collective actual write.  A changed edge is
then selected inside that same segment and consumed by complement
no-silence and the energy-paying tangent/pair/heat native exhaustion. -/
theorem globalStagePhysicalResidual_pos_generates_sameSegment_nativeRedirect
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ)
    (defectPositive :
      0 < infiniteEndpointMacroStageKineticDefect lineage stage)
    (requestedStart : ℕ) :
    Nonempty
      (GlobalStagePhysicalResidualSameSegmentNativeRedirect
        lineage stage requestedStart) := by
  let step := lineage.step stage
  let endpointReceipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      (lineage.current stage) step.elapsedBounded).family.endpointReceipt
  have weakTendstoZero :
      ∀ test : WholeRestartVelocityEndpointState,
        Tendsto
          (fun index =>
            inner ℂ
              (lineage.globalStagePhysicalResidual stage index)
              test)
          atTop (nhds 0) := by
    intro test
    simpa only [
      lineage.globalStagePhysicalResidual_eq_endpointVelocityResidual] using
      (wholeRestartEndpointVelocityResidual_weak_tendsto_zero
        step.elapsedBounded test)
  obtain
      ⟨earlierResidualIndex, laterResidualIndex,
        requestedLeEarlier, earlierLtLater, residualSeparation⟩ :=
    weaklyNull_normSq_tendsto_positive_generates_cofinal_separation
      (lineage.globalStagePhysicalResidual stage)
      (infiniteEndpointMacroStageKineticDefect lineage stage)
      defectPositive weakTendstoZero
      (lineage.globalStagePhysicalResidual_norm_sq_tendsto_stageDefect stage)
      requestedStart
  let segmentStart := endpointReceipt.subsequence earlierResidualIndex
  let segmentFinish := endpointReceipt.subsequence laterResidualIndex
  let segmentSteps := segmentFinish - segmentStart
  have segmentStartLtFinish : segmentStart < segmentFinish := by
    exact endpointReceipt.subsequence_strictMono earlierLtLater
  have segmentStepsPos : 0 < segmentSteps := by
    dsimp only [segmentSteps]
    omega
  have segmentFinishEq :
      segmentStart + segmentSteps = segmentFinish := by
    dsimp only [segmentSteps]
    omega
  have requestedLeSegmentStart :
      requestedStart ≤ segmentStart := by
    exact requestedLeEarlier.trans
      (endpointReceipt.subsequence_strictMono.id_le earlierResidualIndex)
  have residualDifferenceEq :
      lineage.globalStagePhysicalResidual stage laterResidualIndex -
          lineage.globalStagePhysicalResidual stage earlierResidualIndex =
        wholeRestartContactVelocityState
            (lineage.current stage) segmentFinish -
          wholeRestartContactVelocityState
            (lineage.current stage) segmentStart := by
    rw [lineage.globalStagePhysicalResidual_eq_endpointVelocityResidual,
      lineage.globalStagePhysicalResidual_eq_endpointVelocityResidual]
    change
      (wholeRestartContactVelocityState
            (lineage.current stage) segmentFinish -
          endpointReceipt.velocityEndpoint) -
        (wholeRestartContactVelocityState
            (lineage.current stage) segmentStart -
          endpointReceipt.velocityEndpoint) =
      wholeRestartContactVelocityState
            (lineage.current stage) segmentFinish -
        wholeRestartContactVelocityState
          (lineage.current stage) segmentStart
    abel
  have residualDifferenceEqCollective :
      lineage.globalStagePhysicalResidual stage laterResidualIndex -
          lineage.globalStagePhysicalResidual stage earlierResidualIndex =
        wholeRestartCollectiveCausalVelocityWrite
          (lineage.current stage) segmentStart segmentSteps := by
    rw [wholeRestartCollectiveCausalVelocityWrite_eq_gap, segmentFinishEq]
    exact residualDifferenceEq
  have collectiveLower :
      infiniteEndpointMacroStageKineticDefect lineage stage / 2 <
        ‖wholeRestartCollectiveCausalVelocityWrite
          (lineage.current stage) segmentStart segmentSteps‖ ^ 2 := by
    rw [← residualDifferenceEqCollective]
    exact residualSeparation
  have residualDifferenceNe :
      lineage.globalStagePhysicalResidual stage laterResidualIndex -
          lineage.globalStagePhysicalResidual stage earlierResidualIndex ≠
        0 := by
    intro differenceZero
    rw [differenceZero, norm_zero] at residualSeparation
    norm_num at residualSeparation
    linarith
  have segmentEndpointNe :
      wholeRestartContactVelocityState
          (lineage.current stage) segmentStart ≠
        wholeRestartContactVelocityState
          (lineage.current stage) segmentFinish := by
    intro endpointEq
    apply residualDifferenceNe
    rw [residualDifferenceEq, endpointEq, sub_self]
  obtain ⟨nativeEdgeIndex, startLeEdge, edgeLtFinish, edgeChange⟩ :=
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
    ⟨{ defectPositive := defectPositive
       earlierResidualIndex := earlierResidualIndex
       laterResidualIndex := laterResidualIndex
       requestedStart_le_earlierResidualIndex := requestedLeEarlier
       earlierResidualIndex_lt_laterResidualIndex := earlierLtLater
       segmentStart := segmentStart
       segmentSteps := segmentSteps
       requestedStart_le_segmentStart := requestedLeSegmentStart
       segmentSteps_pos := segmentStepsPos
       segmentStart_eq_selectedContact := rfl
       segmentFinish_eq_selectedContact := segmentFinishEq
       residualDifference_eq_collectiveWrite :=
         residualDifferenceEqCollective
       defect_half_lt_collectiveWrite_norm_sq := collectiveLower
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

/-- Source-facing global physical residual disposition.  One actual macro
stage writes its physical successor and internally selects either the zero
defect branch or, after every requested native index, an exact residual
segment with a same-segment complement no-silent tangent/pair/heat redirect.
-/
theorem globalStagePhysicalResidual_generates_zero_or_sameSegment_nativeRedirect
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) :
    (wholeRestartEndpointCausalMacroFrame
        (lineage.current stage)
        (lineage.step stage).elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 =
        lineage.current (stage + 1) ∧
      (infiniteEndpointMacroStageKineticDefect lineage stage = 0 ∨
        ∀ requestedStart : ℕ,
          Nonempty
            (GlobalStagePhysicalResidualSameSegmentNativeRedirect
              lineage stage requestedStart)) := by
  have macroWrite :=
    (wholeRestartEndpointMacroStep_generates_zero_or_complementNoSilent_nativeWholeWrite
      (lineage.step stage)).1
  refine ⟨macroWrite, ?_⟩
  let endpointReceipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      (lineage.current stage)
      (lineage.step stage).elapsedBounded).family.endpointReceipt
  rcases endpointReceipt.kineticReceipt.defect_disposition with
    defectPositive | defectZero
  · right
    have stageDefectPositive :
        0 < infiniteEndpointMacroStageKineticDefect lineage stage := by
      simpa only [infiniteEndpointMacroStageKineticDefect,
        endpointReceipt] using defectPositive
    intro requestedStart
    exact
      lineage.globalStagePhysicalResidual_pos_generates_sameSegment_nativeRedirect
        stage stageDefectPositive requestedStart
  · left
    simpa only [infiniteEndpointMacroStageKineticDefect,
      endpointReceipt] using defectZero.1

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
