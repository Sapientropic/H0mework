import H0mework.NavierStokes.EndpointSettlement.SourceSelfPairScalePrefixSettlement

/-!
# Whole-carrier physical scale feedback of the reduced-core annulus

The annular branch already generates positive whole annular enstrophy and an
actual same-receipt viscous charge.  This module keeps that responsibility on
the complete physical state carrier and follows the authoritative
whole-restart run itself.

The actual run defines a shift residual process.  At the exact gap between
adjacent source-generated scale occurrences, the whole annular projection
therefore survives in the next physical state or leaves a nonzero projected
whole-state trace.  The process path trace itself supplies the exact finite
telescope, so no coordinatewise annular ledger is introduced.

No physical state, radius, horizon, branch, trace, nonzero witness, target
solution, or continuation witness is supplied by the caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open scoped BigOperators

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingWholeSourceGluingLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartComponentGluingResidualNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairOccurrenceGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairVisibleSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelExactHeadroom
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairDuhamelSourceGluingCompiler
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairGluingNativeCocycle
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ResidualProjection
open AffineRelaxation

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- Future actual physical vorticity states from one native whole-restart
index. -/
abbrev WholeRestartPhysicalVorticityTail :=
  ℕ → ComplexVorticityHilbertState

/-- Shift to the next already generated physical contact. -/
def wholeRestartPhysicalVorticityTailKeep :
    WholeRestartPhysicalVorticityTail →ₗ[ℂ]
      WholeRestartPhysicalVorticityTail where
  toFun residual offset := residual (offset + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual physical-state tail on the authoritative native run. -/
def wholeRestartPhysicalVorticityTail
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (base stage : ℕ) : WholeRestartPhysicalVorticityTail :=
  fun offset =>
    (run initial (base + stage + offset)).contact.physicalState

/-- One actual native update is literally the shift keep on the complete
physical coefficient carrier. -/
theorem wholeRestartPhysicalVorticityTail_transport
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (base stage : ℕ) :
    wholeRestartPhysicalVorticityTail initial base (stage + 1) =
      wholeRestartPhysicalVorticityTailKeep
        (wholeRestartPhysicalVorticityTail initial base stage) := by
  funext offset
  change
    (run initial (base + (stage + 1) + offset)).contact.physicalState =
      (run initial (base + stage + (offset + 1))).contact.physicalState
  have indexEq :
      base + (stage + 1) + offset =
        base + stage + (offset + 1) := by
    omega
  rw [indexEq]

/-- Effective residual process of the actual whole physical state tail. -/
def generatedWholeRestartPhysicalVorticityEffectiveProcess
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (base : ℕ) :
    EffectiveResidualProcess ℂ WholeRestartPhysicalVorticityTail ℕ where
  target := 0
  keep := wholeRestartPhysicalVorticityTailKeep
  residual := wholeRestartPhysicalVorticityTail initial base
  update := Nat.succ
  residual_transport_law :=
    wholeRestartPhysicalVorticityTail_transport initial base

@[simp] theorem
    generatedWholeRestartPhysicalVorticityEffectiveProcess_pathState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (base stage steps : ℕ) :
    (generatedWholeRestartPhysicalVorticityEffectiveProcess
      initial base).pathState stage steps =
        stage + steps := by
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
      rw [EffectiveResidualProcess.pathState_succ,
        inductionHypothesis]
      rfl

/-- Finite-path residual conservation on the complete physical coefficient
carrier. -/
theorem wholeRestartPhysicalVorticity_path_split
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (base steps : ℕ) :
    (run initial base).contact.physicalState =
      (run initial (base + steps)).contact.physicalState +
        ((generatedWholeRestartPhysicalVorticityEffectiveProcess
          initial base).pathTrace 0 steps) 0 := by
  have split :=
    (generatedWholeRestartPhysicalVorticityEffectiveProcess
      initial base).pathTrace_split 0 steps
  rw [generatedWholeRestartPhysicalVorticityEffectiveProcess_pathState]
    at split
  simpa [generatedWholeRestartPhysicalVorticityEffectiveProcess,
    wholeRestartPhysicalVorticityTail] using congrFun split 0

/-- Adjacent generated scale contacts cannot have the same whole physical
state.  The next requested radius is the previous least crossing radius.  If
the two states agreed, that radius would already be above the half-critical
threshold for the next contact, contradicting the next least core's strict
escape beyond it. -/
theorem
    WholeRestartReducedCoreScaleLineage.adjacentPhysicalState_ne
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    (run initial
        (scale.absoluteOccurrence step)).contact.physicalState ≠
      (run initial
        (scale.absoluteOccurrence (step + 1))).contact.physicalState := by
  intro stateEq
  have currentCrossed :=
    wholeRestartCrossingFiniteCoreRadius_crossed
      (run initial (scale.start step))
      (scale.relativeIndex step) (scale.crossed step)
  have nextMinimal :=
    wholeRestartCrossingFiniteCoreRadius_minimal
      (run initial (scale.start (step + 1)))
      (scale.relativeIndex (step + 1)) (scale.crossed (step + 1))
      (scale.coreEscapes (step + 1))
  rw [scale.actualCurrent step] at currentCrossed
  rw [scale.actualCurrent (step + 1)] at nextMinimal
  rw [scale.requestedRadius_succ_eq_coreRadius step] at nextMinimal
  unfold wholeRestartCrossingFiniteCoreModes at currentCrossed
  unfold WholeRestartReducedCoreScaleLineage.absoluteOccurrence at stateEq
  rw [stateEq] at currentCrossed
  linarith

/-- Exact complete physical-state trace between adjacent source-generated
scale occurrences. -/
def WholeRestartReducedCoreScaleLineage.annularPhysicalGapTrace
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) : ComplexVorticityHilbertState :=
  ((generatedWholeRestartPhysicalVorticityEffectiveProcess
    initial (scale.absoluteOccurrence step)).pathTrace
      0 (scale.nextScaleGap step)) 0

/-- Adjacent actual physical states and their forced trace form one exact
whole-carrier split. -/
theorem
    WholeRestartReducedCoreScaleLineage.annularPhysical_nextScale_split
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    (run initial
        (scale.absoluteOccurrence step)).contact.physicalState =
      (run initial
        (scale.absoluteOccurrence (step + 1))).contact.physicalState +
        scale.annularPhysicalGapTrace step := by
  have split :=
    wholeRestartPhysicalVorticity_path_split
      initial (scale.absoluteOccurrence step) (scale.nextScaleGap step)
  rw [scale.absoluteOccurrence_add_nextScaleGap step] at split
  exact split

/-- The forced whole-state trace between adjacent generated scale contacts is
always nonzero.  Least-core growth already excludes equal endpoints, so this
does not require choosing an annular coordinate or a downstream observer. -/
theorem
    WholeRestartReducedCoreScaleLineage.annularPhysicalGapTrace_ne_zero
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    scale.annularPhysicalGapTrace step ≠ 0 := by
  intro gapZero
  apply scale.adjacentPhysicalState_ne step
  have split := scale.annularPhysical_nextScale_split step
  rw [gapZero, add_zero] at split
  exact split

/-- Positive whole annular mass makes the actual sharp annular projection
nonzero before any coefficient readout. -/
theorem
    WholeRestartReducedCoreScaleLineage.annularPhysicalProjection_current_ne_zero
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    complexSharpSupportProjection
        (scale.annularModes step)
        (run initial
          (scale.absoluteOccurrence step)).contact.physicalState ≠ 0 := by
  intro projectionZero
  have massPos := scale.annularCoefficientMass_pos step
  have massZero : scale.annularCoefficientMass step = 0 := by
    unfold WholeRestartReducedCoreScaleLineage.annularCoefficientMass
    rw [← finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection]
    rw [projectionZero]
    unfold finiteStateVorticityCoefficientEnstrophy
    apply Finset.sum_eq_zero
    intro output outputMem
    exact (complexCoordinateVectorNormSq_eq_zero_iff 0).2 rfl
  exact (ne_of_gt massPos) massZero

/-- The adjacent whole-state split commutes with the actual annular
projection. -/
theorem
    WholeRestartReducedCoreScaleLineage.annularPhysicalProjection_nextScale_split
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    complexSharpSupportProjection
        (scale.annularModes step)
        (run initial
          (scale.absoluteOccurrence step)).contact.physicalState =
      complexSharpSupportProjection
          (scale.annularModes step)
          (run initial
            (scale.absoluteOccurrence (step + 1))).contact.physicalState +
        complexSharpSupportProjection
          (scale.annularModes step)
          (scale.annularPhysicalGapTrace step) := by
  ext output coordinate
  by_cases outputMem : output ∈ scale.annularModes step
  · simpa [complexSharpSupportProjection_apply, outputMem] using
      congrArg
        (fun state : ComplexVorticityHilbertState =>
          state output coordinate)
        (scale.annularPhysical_nextScale_split step)
  · simp [complexSharpSupportProjection_apply, outputMem]

/-- Whole annular responsibility cannot disappear across the actual adjacent
update: either the next physical carrier still sees it, or the unique
whole-state complement is nonzero on the same annulus. -/
theorem
    WholeRestartReducedCoreScaleLineage.annularWhole_nextScaleNoSilentWrite
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    complexSharpSupportProjection
          (scale.annularModes step)
          (run initial
            (scale.absoluteOccurrence step)).contact.physicalState ≠ 0 ∧
      (complexSharpSupportProjection
            (scale.annularModes step)
            (run initial
              (scale.absoluteOccurrence (step + 1))).contact.physicalState ≠ 0 ∨
        complexSharpSupportProjection
            (scale.annularModes step)
            (scale.annularPhysicalGapTrace step) ≠ 0) := by
  have currentNonzero :=
    scale.annularPhysicalProjection_current_ne_zero step
  refine ⟨currentNonzero, ?_⟩
  by_cases nextNonzero :
      complexSharpSupportProjection
          (scale.annularModes step)
          (run initial
            (scale.absoluteOccurrence (step + 1))).contact.physicalState ≠ 0
  · exact Or.inl nextNonzero
  · right
    intro traceZero
    apply currentNonzero
    have split :=
      scale.annularPhysicalProjection_nextScale_split step
    rw [not_ne_iff.mp nextNonzero, traceZero, zero_add] at split
    exact split

/-- Source-facing total reduced-core node write.  Both complete carriers
perform their exact adjacent split on the same authoritative run.  The
source itself then chooses either positive whole annular mass with its actual
kinetic charge and whole-projection feedback, or the already settled positive
pair responsibility with its physical/spliced/gap/gluing destination. -/
theorem
    WholeRestartReducedCoreScaleLineage.node_reducedCorePhysicalPairWholeWrite
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ) :
    let tail := run initial (scale.start step)
    let index := scale.relativeIndex step
    let crossed := scale.crossed step
    run tail (wholeRestartComponentGluingNativeUpdate index) =
        (run tail index).next ∧
      wholeRestartComponentGluingResidualTail tail (index + 1) =
        wholeRestartComponentGluingResidualTailKeep
          (wholeRestartComponentGluingResidualTail tail index) ∧
      (run initial
          (scale.absoluteOccurrence step)).contact.physicalState =
        (run initial
          (scale.absoluteOccurrence (step + 1))).contact.physicalState +
          scale.annularPhysicalGapTrace step ∧
      wholeRestartPairDuhamelTable
            initial (scale.absoluteOccurrence step) =
        wholeRestartPairDuhamelTable
            initial (scale.absoluteOccurrence (step + 1)) +
          scale.sourcePairDuhamelGapTrace step ∧
      ((((∃ actual : Ioo (0 : ℝ) (run tail index).nextContact.time.1,
          let initialMass :=
            finiteStateVorticityCoefficientEnstrophy
              (scale.annularModes step)
              (run tail index).contact.physicalState
          let charge := ν.coeff * actual.1 * initialMass
          0 < charge ∧
            charge ≤
              wholeRestartNextKineticDissipationPayment tail index ∧
            (2 * Real.pi) ^ 2 *
                  ((scale.requestedRadius step + 1 : ℕ) : ℝ) ^ 2 *
                  charge <
              initialMass -
                finiteStateVorticityCoefficientEnstrophy
                  (scale.annularModes step)
                  ((run tail index).nextContact.prefixReceipt.wholePath
                    ⟨actual.1, actual.2.1.le, actual.2.2.le⟩)) ∧
          0 < scale.annularCoefficientMass step ∧
          complexSharpSupportProjection
                (scale.annularModes step)
                (run initial
                  (scale.absoluteOccurrence step)).contact.physicalState ≠ 0 ∧
          (complexSharpSupportProjection
                (scale.annularModes step)
                (run initial
                  (scale.absoluteOccurrence
                    (step + 1))).contact.physicalState ≠ 0 ∨
            complexSharpSupportProjection
                (scale.annularModes step)
                (scale.annularPhysicalGapTrace step) ≠ 0)) ∨
        ∃ output ∈ scale.sourceSelfPairOutputSupport step,
          ∃ first ∈ scale.sourceSelfPairFiber step output,
            output ≠ 0 ∧
              0 <
                wholeRestartCrossingSourceSelfVisibleSquareRow
                  tail index crossed output ∧
              (canonicalHalfCriticalComponentCount ν
                    (wholeRestartCrossingFiniteCoreState
                      tail index crossed) : ℝ) *
                  wholeRestartCrossingSourceSelfVisibleSquareRow
                    tail index crossed output ≤
                ν.coeff * (2 * Real.pi) ^ 2 *
                  wholeStateVorticityGradientMass
                    (wholeRestartCrossingFiniteCoreState
                      tail index crossed) ∧
              0 < scale.sourcePairDuhamelRateQuantum
                    elapsedBounded step output first ∧
              wholeRestartCrossingFiniteComponentSelfPairOccurrence
                    tail index crossed output first =
                ((canonicalHalfCriticalComponentCount ν
                    (wholeRestartCrossingFiniteCoreState
                      tail index crossed) : ℝ)⁻¹ : ℂ) •
                  finiteStateVorticityNonlinearPairContribution
                    (wholeRestartCrossingFiniteCoreState
                      tail index crossed)
                    (first, output - first) ∧
              scale.sourcePairDuhamelNextScaleWholeWriteAt
                elapsedBounded step output first)) := by
  dsimp only
  have pairWrite :=
    scale.node_pairDuhamelNextScaleWholeWrite elapsedBounded step
  dsimp only at pairWrite
  have physicalSplit :=
    scale.annularPhysical_nextScale_split step
  rcases pairWrite with
    ⟨updateEq, residualEq, pairSplit, annular | pair⟩
  · have annularNoSilent :=
      scale.annularWhole_nextScaleNoSilentWrite step
    exact
      ⟨updateEq, residualEq, physicalSplit, pairSplit,
        Or.inl
          ⟨annular, scale.annularCoefficientMass_pos step,
            annularNoSilent.1, annularNoSilent.2⟩⟩
  · exact
      ⟨updateEq, residualEq, physicalSplit, pairSplit,
        Or.inr pair⟩

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
