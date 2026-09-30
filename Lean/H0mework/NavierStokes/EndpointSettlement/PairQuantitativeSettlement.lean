import H0mework.NavierStokes.EndpointSettlement.NativeQuantitativeDisposition
import H0mework.NavierStokes.Crossing.PairDuhamelSourceGluingCompiler

/-!
# Quantitative pair settlement on the reduced-core scale lineage

A nonzero primitive source-self pair occurrence is transported through the
same actual causal heat receipt before pair aggregation.  The exact
reciprocal-count occurrence therefore has only two quantitative outcomes:

* its visible aggregation pays the existing exact causal square, or a
  concrete aggregation-kernel component persists in the native pair-Duhamel
  future/path trace;
* cancellation against the complete gluing integral exposes a concrete time
  slice whose gluing occurrence enters the existing native cocycle.

The source-selected reduced-core node then consumes this theorem without
accepting a branch, output, pair, time, count, nonzero witness, or target
state from the caller.
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
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartComponentGluingResidualNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairOccurrenceGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelExactHeadroom
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairDuhamelSourceGluingCompiler
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairGluingNativeCocycle
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairVisibleSquareLedger

noncomputable section

/-- The exact physical/kernel/native alternatives which consume one
source-generated pair occurrence before aggregation. -/
def wholeRestartGeneratedCrossingPairQuantitativeSettlement
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output first : IntegerWavevector) : Prop :=
    (0 <
        ‖wholeRestartNonlinearRegenerationState
            initial index output‖ ^ 2 /
          (run initial index).nextContact.time.1 ∧
      ‖wholeRestartNonlinearRegenerationState
            initial index output‖ ^ 2 /
          (run initial index).nextContact.time.1 ≤
        wholeRestartExactCausalNonlinearSquareRow
          initial index output) ∨
      (∃ component : IntegerWavevector,
        (∑' other : IntegerWavevector,
          wholeRestartPairDuhamelOccurrence
            initial index output other) = 0 ∧
        wholeRestartPairDuhamelOccurrence
            initial index output component ≠ 0 ∧
        ∀ horizon : ℕ,
          wholeRestartPairDuhamelPathTable
                initial index horizon output component ≠ 0 ∨
            ((generatedWholeRestartPairDuhamelEffectiveProcess
                initial index).pathTrace 0 horizon)
              0 output component ≠ 0) ∨
      ∃ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
        wholeRestartPairOccurrenceTrace
            initial index output first time ≠ 0 ∨
          wholeRestartCrossingSourceSelfPairUpdate
              initial index
                (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                  initial elapsedBounded index)
                (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                  initial elapsedBounded (index + 1))
              output first ≠ 0 ∨
            wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
              initial (index + 1)
                (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                  initial elapsedBounded (index + 1))
              output first
                ⟨0, ⟨le_rfl,
                  (run initial (index + 1)).nextContact.time_pos.le⟩⟩ ≠ 0

/-- A nonzero primitive source-self pair occurrence is consumed before the
pair quotient.  Its causal image either enters the exact physical square
payment, persists componentwise in the pair-Duhamel residual process, or
exposes a concrete complete-gluing occurrence for native redirect. -/
theorem
    wholeRestartGeneratedCrossingFiniteComponentSelfPairOccurrence_quantitativeSettlement
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output first : IntegerWavevector)
    (outputNonzero : output ≠ 0)
    (selfPairNonzero :
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
          initial index
            (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
              initial elapsedBounded index)
          output first ≠ 0) :
    wholeRestartGeneratedCrossingPairQuantitativeSettlement
      initial elapsedBounded index output first := by
  unfold wholeRestartGeneratedCrossingPairQuantitativeSettlement
  let crossed :=
    elapsedTime_bddAbove_forces_every_halfCriticalCrossing
      initial elapsedBounded index
  let nextCrossed :=
    elapsedTime_bddAbove_forces_every_halfCriticalCrossing
      initial elapsedBounded (index + 1)
  have sourceDuhamelNonzero :
      wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
          initial elapsedBounded index output first ≠ 0 := by
    rw [
      wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence_eq_gain
        initial elapsedBounded index ⟨output, outputNonzero⟩ first]
    exact
      smul_ne_zero
        (ne_of_gt
          (wholeRestartCausalTangentGain_pos
            initial index output outputNonzero))
        selfPairNonzero
  by_cases actualDuhamelNonzero :
      wholeRestartPairDuhamelOccurrence
        initial index output first ≠ 0
  · have keepNonzero :
        wholeRestartPairDuhamelPathTable
          initial index 0 output first ≠ 0 := by
      simpa [wholeRestartPairDuhamelPathTable,
        wholeRestartPairDuhamelTable] using actualDuhamelNonzero
    rcases
        wholeRestartPairDuhamelKeep_positiveExactPayment_or_kernelTransport
          initial index 0 output first outputNonzero keepNonzero with
      visiblePayment | kernelTransport
    · left
      simpa using visiblePayment
    · exact Or.inr (Or.inl (by simpa using kernelTransport))
  · right
    right
    have gluingDuhamelNonzero :
        wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
          initial elapsedBounded index output first ≠ 0 := by
      intro gluingDuhamelZero
      apply sourceDuhamelNonzero
      have split :=
        wholeRestartPairDuhamelOccurrence_eq_boundedElapsedCrossingSourceSelf_add_completeGluing
          initial elapsedBounded index output first
      rw [not_ne_iff.mp actualDuhamelNonzero, gluingDuhamelZero] at split
      simpa using split.symm
    have existsGluingTime :
        ∃ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
          wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
            initial index crossed output first time ≠ 0 := by
      by_contra noGluingTime
      push Not at noGluingTime
      apply gluingDuhamelNonzero
      unfold
        wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
      simp [noGluingTime]
    obtain ⟨time, gluingNonzero⟩ := existsGluingTime
    refine ⟨time, ?_⟩
    simpa [crossed, nextCrossed] using
      wholeRestartCrossingCompleteOutgoingPairGluing_ne_zero_redirect
        initial index crossed nextCrossed output first time
        gluingNonzero

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- Every node of the source-generated reduced-core scale lineage performs
the native whole-current write and residual transport, then internally
selects its quantitative settlement.  A zero whole nonlinear row produces
the strict annular kinetic charge.  A nonzero row produces a concrete
reciprocal-count pair occurrence and consumes it, before aggregation, in
the causal visible/kernel/native settlement. -/
theorem WholeRestartReducedCoreScaleLineage.node_pairQuantitativeSettlement
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ) :
    let tail := run initial (scale.start step)
    let index := scale.relativeIndex step
    let crossed := scale.crossed step
    let tailElapsedBounded :
        BddAbove (Set.range (elapsedTime tail)) :=
      elapsedTime_run_bddAbove initial elapsedBounded (scale.start step)
    run tail (wholeRestartComponentGluingNativeUpdate index) =
        (run tail index).next ∧
      wholeRestartComponentGluingResidualTail tail (index + 1) =
        wholeRestartComponentGluingResidualTailKeep
          (wholeRestartComponentGluingResidualTail tail index) ∧
      ((∃ actual : Ioo (0 : ℝ) (run tail index).nextContact.time.1,
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
                    ⟨actual.1, actual.2.1.le, actual.2.2.le⟩)) ∨
        ∃ output first : IntegerWavevector,
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
            0 <
              ‖wholeRestartCrossingFiniteComponentSelfPairOccurrence
                  tail index crossed output first‖ ^ 2 ∧
            wholeRestartCrossingFiniteComponentSelfPairOccurrence
                  tail index crossed output first =
              ((canonicalHalfCriticalComponentCount ν
                  (wholeRestartCrossingFiniteCoreState
                    tail index crossed) : ℝ)⁻¹ : ℂ) •
                finiteStateVorticityNonlinearPairContribution
                  (wholeRestartCrossingFiniteCoreState
                    tail index crossed)
                  (first, output - first) ∧
            wholeRestartGeneratedCrossingPairQuantitativeSettlement
              tail tailElapsedBounded index output first) := by
  dsimp only
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  let crossed := scale.crossed step
  let tailElapsedBounded :
      BddAbove (Set.range (elapsedTime tail)) :=
    elapsedTime_run_bddAbove initial elapsedBounded (scale.start step)
  have generated :=
    scale.node_nativeQuantitativeDisposition elapsedBounded step
  dsimp only at generated
  rcases generated with
    ⟨updateEq, residualEq, annular | pair⟩
  · refine ⟨updateEq, residualEq, Or.inl ?_⟩
    rcases annular with
      ⟨_annularMassPos, _annularFrequency, actual,
        chargePos, chargeLe, _weightedDrop, radiusDrop⟩
    exact ⟨actual, chargePos, chargeLe, radiusDrop⟩
  · refine ⟨updateEq, residualEq, Or.inr ?_⟩
    rcases pair with
      ⟨output, first, outputNonzero, _sourceOutputNonzero,
        outputSquarePos, outputSquareCountLe, selfPairNonzero,
        selfPairSquarePos, selfPairEq, _pointwiseDisposition⟩
    let generatedCrossed :
        wholeRestartHalfCriticalCrossed tail index :=
      elapsedTime_bddAbove_forces_every_halfCriticalCrossing
        tail tailElapsedBounded index
    have crossedEq : generatedCrossed = crossed :=
      Subsingleton.elim _ _
    have generatedSelfPairNonzero :
        wholeRestartCrossingFiniteComponentSelfPairOccurrence
            tail index generatedCrossed output first ≠ 0 := by
      simpa [crossedEq] using selfPairNonzero
    have settlement :=
      wholeRestartGeneratedCrossingFiniteComponentSelfPairOccurrence_quantitativeSettlement
        tail tailElapsedBounded index output first outputNonzero
        generatedSelfPairNonzero
    exact
      ⟨output, first, outputNonzero, outputSquarePos,
        outputSquareCountLe, selfPairSquarePos, selfPairEq, settlement⟩

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
