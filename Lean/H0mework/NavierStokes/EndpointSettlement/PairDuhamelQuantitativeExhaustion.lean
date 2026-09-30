import H0mework.NavierStokes.EndpointSettlement.PairQuantitativeSettlement

/-!
# Pair-Duhamel quantitative exhaustion at a reduced-core scale node

The source-selected primitive `output × first` occurrence is now consumed on
that exact coordinate, before input-pair aggregation.  Its causal source-self
Duhamel square is positive.  A source-generated quarter of that same square
is retained by the actual pair-Duhamel occurrence, or by the complete-gluing
Duhamel occurrence; the latter exposes a nonzero pointwise gluing occurrence
and enters the native adjacent-source/gluing cocycle.

This is not a provenance-memory norm.  All three quantities are Fourier
vectors produced by the same actual unforced receipt and have identical
units.  No branch, output, pair, time, quantum, or redirect is supplied by
the caller.
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

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- Every source-generated reduced-core node performs its actual update and
residual keep.  The nonzero branch then keeps a fixed fraction of the same
primitive pair-Duhamel square in the actual pair coordinate or redirects the
same coordinate through complete gluing. -/
theorem
    WholeRestartReducedCoreScaleLineage.node_pairDuhamelQuantitativeExhaustion
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
            let sourceSquare :=
              ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
                tail tailElapsedBounded index output first‖ ^ 2
            let sourceRateQuantum :=
              (sourceSquare / 16) /
                (run tail index).nextContact.time.1
            0 < sourceRateQuantum ∧
              (sourceRateQuantum ≤
                  wholeRestartExactCausalNonlinearSquareRow
                    tail index output ∨
                (sourceSquare / 4 ≤
                    ‖wholeRestartPairDuhamelOccurrence
                      tail index output first‖ ^ 2 ∧
                  ∀ steps : ℕ,
                    wholeRestartPairDuhamelPathTable
                          tail index steps output first ≠ 0 ∨
                      ((generatedWholeRestartPairDuhamelEffectiveProcess
                          tail index).pathTrace 0 steps)
                        0 output first ≠ 0) ∨
                ∃ time :
                    Icc (0 : ℝ) (run tail index).nextContact.time.1,
                  sourceSquare / 4 ≤
                      ‖wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
                        tail tailElapsedBounded index output first‖ ^ 2 ∧
                    wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
                        tail index
                          (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                            tail tailElapsedBounded index)
                        output first time ≠ 0 ∧
                      (wholeRestartPairOccurrenceTrace
                          tail index output first time ≠ 0 ∨
                        wholeRestartCrossingSourceSelfPairUpdate
                            tail index
                              (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                                tail tailElapsedBounded index)
                              (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                                tail tailElapsedBounded (index + 1))
                            output first ≠ 0 ∨
                          wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
                            tail (index + 1)
                              (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                                tail tailElapsedBounded (index + 1))
                            output first
                              ⟨0, ⟨le_rfl,
                                (run tail
                                  (index + 1)).nextContact.time_pos.le⟩⟩ ≠ 0))) := by
  dsimp only
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  let crossed := scale.crossed step
  let tailElapsedBounded :
      BddAbove (Set.range (elapsedTime tail)) :=
    elapsedTime_run_bddAbove initial elapsedBounded (scale.start step)
  have generated :=
    scale.node_pairQuantitativeSettlement elapsedBounded step
  dsimp only at generated
  rcases generated with
    ⟨updateEq, residualEq, annular | pair⟩
  · exact ⟨updateEq, residualEq, Or.inl annular⟩
  · rcases pair with
      ⟨output, first, outputNonzero, outputSquarePos,
        outputSquareCountLe, selfPairSquarePos, selfPairEq,
        _settlement⟩
    let generatedCrossed :
        wholeRestartHalfCriticalCrossed tail index :=
      elapsedTime_bddAbove_forces_every_halfCriticalCrossing
        tail tailElapsedBounded index
    have crossedEq : generatedCrossed = crossed :=
      Subsingleton.elim _ _
    have generatedSelfPairNonzero :
        wholeRestartCrossingFiniteComponentSelfPairOccurrence
            tail index generatedCrossed output first ≠ 0 := by
      intro selfPairZero
      have scalePairZero :
          wholeRestartCrossingFiniteComponentSelfPairOccurrence
              tail index crossed output first = 0 := by
        simpa [crossedEq] using selfPairZero
      rw [scalePairZero] at selfPairSquarePos
      simp at selfPairSquarePos
    have exhaustion :=
      wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamel_quantitativeVisibleOrNativeExhaustion
        tail tailElapsedBounded index output first outputNonzero
        generatedSelfPairNonzero
    exact
      ⟨updateEq, residualEq, Or.inr
        ⟨output, first, outputNonzero, outputSquarePos,
          outputSquareCountLe, selfPairSquarePos, selfPairEq,
          exhaustion.1, exhaustion.2⟩⟩

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
