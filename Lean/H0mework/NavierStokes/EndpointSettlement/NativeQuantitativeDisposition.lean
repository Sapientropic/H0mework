import H0mework.NavierStokes.EndpointSettlement.AnnularResponsibility
import H0mework.NavierStokes.Crossing.HighFrequencyAggregateCharge
import H0mework.NavierStokes.Crossing.PairVisibleSquareLedger

/-!
# Native quantitative disposition at a reduced-core scale node

At every generated reduced-core node, the actual whole nonlinearity itself
selects the quantitative responsibility.

* If it vanishes, the least-radius annulus generates a nonzero high-frequency
  physical row and the same unforced receipt writes a strictly positive
  viscous kinetic charge.
* If it does not vanish, the exact reciprocal forcing identifies the
  primitive source-self `H⁻¹` state.  That state internally selects a strictly
  positive spectral-heat output square with its count-weighted physical
  bound and a concrete positive input-pair occurrence square.  The latter is
  exactly the reciprocal-count copy of the finite-core pair.  Failure of the
  same actual pair readout is redirected by the existing native gluing
  cocycle.

No branch, output, input pair, radius, time, charge, or nonzero witness is
accepted from the caller.
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
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingSelfForcingReduction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingWholeSourceGluingLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartComponentGluingResidualNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyKineticCharge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateCharge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairOccurrenceGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairGluingNativeCocycle
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairVisibleSquareLedger

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- One actual reduced-core scale node generates either a high-frequency
physical kinetic charge or a positive output-indexed pair square with a
concrete occurrence and its native no-silent disposition. -/
theorem WholeRestartReducedCoreScaleLineage.node_nativeQuantitativeDisposition
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ) :
    let tail := run initial (scale.start step)
    let index := scale.relativeIndex step
    let crossed := scale.crossed step
    let zeroTime :
        Icc (0 : ℝ) (run tail index).nextContact.time.1 :=
      ⟨0, ⟨le_rfl, (run tail index).nextContact.time_pos.le⟩⟩
    let nextCrossed :
        wholeRestartHalfCriticalCrossed tail (index + 1) :=
      elapsedTime_bddAbove_forces_every_halfCriticalCrossing
        tail
        (elapsedTime_run_bddAbove initial elapsedBounded
          (scale.start step))
        (index + 1)
    run tail (wholeRestartComponentGluingNativeUpdate index) =
        (run tail index).next ∧
      wholeRestartComponentGluingResidualTail tail (index + 1) =
        wholeRestartComponentGluingResidualTailKeep
          (wholeRestartComponentGluingResidualTail tail index) ∧
      ((0 <
          finiteStateVorticityCoefficientEnstrophy
            (scale.annularModes step)
            (run tail index).contact.physicalState ∧
        (∀ output ∈ scale.annularModes step,
          scale.requestedRadius step <
            integerWaveCoordinateRadius output) ∧
        ∃ actual : Ioo (0 : ℝ) (run tail index).nextContact.time.1,
            let initialMass :=
              finiteStateVorticityCoefficientEnstrophy
                (scale.annularModes step)
                (run tail index).contact.physicalState
            let weightedInitialMass :=
              ∑ output ∈ scale.annularModes step,
                integerWaveViscousMultiplier output *
                  complexCoordinateAmplitudeSq
                    ((run tail index).contact.physicalState output)
            let charge := ν.coeff * actual.1 * initialMass
            0 < charge ∧
              charge ≤
                wholeRestartNextKineticDissipationPayment tail index ∧
              ν.coeff * actual.1 * weightedInitialMass <
                initialMass -
                  finiteStateVorticityCoefficientEnstrophy
                    (scale.annularModes step)
                    ((run tail index).nextContact.prefixReceipt.wholePath
                      ⟨actual.1, actual.2.1.le,
                        actual.2.2.le⟩) ∧
              (2 * Real.pi) ^ 2 *
                    ((scale.requestedRadius step + 1 : ℕ) : ℝ) ^ 2 *
                    charge <
                initialMass -
                  finiteStateVorticityCoefficientEnstrophy
                    (scale.annularModes step)
                    ((run tail index).nextContact.prefixReceipt.wholePath
                      ⟨actual.1, actual.2.1.le,
                        actual.2.2.le⟩)) ∨
      (∃ output first : IntegerWavevector,
        output ≠ 0 ∧
          wholeRestartCrossingFiniteComponentSelfNegativeOneState
                tail index crossed output ≠ 0 ∧
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
          wholeRestartCrossingFiniteComponentSelfPairOccurrence
                tail index crossed output first ≠ 0 ∧
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
          (actualWholeContinuousPairVector
                (run tail index).nextContact.prefixReceipt
                output first zeroTime ≠ 0 ∨
            wholeRestartPairOccurrenceTrace
                tail index output first zeroTime ≠ 0 ∨
            wholeRestartCrossingSourceSelfPairUpdate
                tail index crossed nextCrossed output first ≠ 0 ∨
            wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
                tail (index + 1) nextCrossed output first
                ⟨0, ⟨le_rfl,
                  (run tail (index + 1)).nextContact.time_pos.le⟩⟩ ≠ 0))) := by
  dsimp only
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  let crossed := scale.crossed step
  let wholeNegativeOne :=
    wholeStateVorticityNonlinearNegativeOneState
      (run tail index).contact.physicalState
      (run tail index).contact.transverse
      (run tail index).contact.gradient_summable
  refine
    ⟨wholeRestartComponentGluingNativeUpdate_physical tail index,
      wholeRestartComponentGluingResidual_transport tail index, ?_⟩
  by_cases wholeZero : wholeNegativeOne = 0
  · left
    have annularMassPos :
        0 <
          finiteStateVorticityCoefficientEnstrophy
            (scale.annularModes step)
            (run tail index).contact.physicalState := by
      have generated := scale.annularCoefficientMass_pos step
      unfold WholeRestartReducedCoreScaleLineage.annularCoefficientMass
        WholeRestartReducedCoreScaleLineage.absoluteOccurrence
        at generated
      rw [← scale.actualCurrent step] at generated
      simpa [tail, index] using generated
    have annularFrequency :
        ∀ output ∈ scale.annularModes step,
          scale.requestedRadius step <
            integerWaveCoordinateRadius output :=
      fun output outputMem =>
        scale.annularMode_frequency_gt step outputMem
    have modesNonzero :
        ∀ output ∈ scale.annularModes step, output ≠ 0 :=
      fun output outputMem =>
        scale.annularMode_ne_zero step outputMem
    have nonlinearRowsZero :
        ∀ output ∈ scale.annularModes step,
          wholeStateVorticityNonlinearCoefficientAt
            (run tail index).contact.physicalState output = 0 := by
      intro output outputMem
      exact
        wholeStateVorticityNonlinearCoefficientAt_eq_zero_of_negativeOneState_eq_zero
          (run tail index).contact.physicalState
          (run tail index).contact.transverse
          (run tail index).contact.gradient_summable
          wholeZero output (modesNonzero output outputMem)
    have weightedLower :
        (2 * Real.pi) ^ 2 *
              ((scale.requestedRadius step + 1 : ℕ) : ℝ) ^ 2 *
              finiteStateVorticityCoefficientEnstrophy
                (scale.annularModes step)
                (run tail index).contact.physicalState ≤
          ∑ output ∈ scale.annularModes step,
            integerWaveViscousMultiplier output *
              complexCoordinateAmplitudeSq
                ((run tail index).contact.physicalState output) := by
      have generated :=
        scale.requestedFrequencySq_mul_annularMass_le_weighted step
      unfold WholeRestartReducedCoreScaleLineage.annularCoefficientMass
        WholeRestartReducedCoreScaleLineage.absoluteOccurrence
        at generated
      rw [← scale.actualCurrent step] at generated
      simpa [tail, index] using generated
    obtain ⟨actual, chargePos, chargeLe, weightedDrop⟩ :=
      wholeRestartActualWholeFiniteAmplitudeSq_generates_aggregateKineticCharge_of_nonlinearRows_zero
        tail index (scale.annularModes step)
        nonlinearRowsZero modesNonzero annularMassPos
    refine ⟨annularMassPos, annularFrequency, actual, ?_⟩
    refine ⟨chargePos, chargeLe, weightedDrop, ?_⟩
    calc
      (2 * Real.pi) ^ 2 *
            ((scale.requestedRadius step + 1 : ℕ) : ℝ) ^ 2 *
            (ν.coeff * actual.1 *
              finiteStateVorticityCoefficientEnstrophy
                (scale.annularModes step)
                (run tail index).contact.physicalState) =
          ν.coeff * actual.1 *
            ((2 * Real.pi) ^ 2 *
              ((scale.requestedRadius step + 1 : ℕ) : ℝ) ^ 2 *
              finiteStateVorticityCoefficientEnstrophy
                (scale.annularModes step)
                (run tail index).contact.physicalState) := by
        ring
      _ ≤
          ν.coeff * actual.1 *
            (∑ output ∈ scale.annularModes step,
              integerWaveViscousMultiplier output *
                complexCoordinateAmplitudeSq
                  ((run tail index).contact.physicalState output)) :=
        mul_le_mul_of_nonneg_left weightedLower
          (mul_nonneg ν.coeff_pos.le actual.2.1.le)
      _ <
          finiteStateVorticityCoefficientEnstrophy
              (scale.annularModes step)
              (run tail index).contact.physicalState -
            finiteStateVorticityCoefficientEnstrophy
              (scale.annularModes step)
              ((run tail index).nextContact.prefixReceipt.wholePath
                ⟨actual.1, actual.2.1.le, actual.2.2.le⟩) :=
        weightedDrop
  · right
    let sourceSelfNegativeOne :=
      wholeRestartCrossingFiniteComponentSelfNegativeOneState
        tail index crossed
    have wholeEqSourceSelf :
        wholeNegativeOne = sourceSelfNegativeOne := by
      calc
        wholeNegativeOne =
            ((canonicalHalfCriticalComponentCount ν
                (wholeRestartCrossingFiniteCoreState
                  tail index crossed) : ℝ)⁻¹ : ℂ) •
              wholeRestartCrossingFiniteCoreNegativeOneState
                tail index crossed := by
          simpa [tail, index, crossed, wholeNegativeOne] using
            scale.reducedForcing step
        _ = sourceSelfNegativeOne := by
          simpa [sourceSelfNegativeOne] using
            (wholeRestartCrossingFiniteComponentSelfNegativeOneState_eq_core_smul
              tail index crossed).symm
    have sourceSelfNonzero : sourceSelfNegativeOne ≠ 0 := by
      intro sourceSelfZero
      exact wholeZero (wholeEqSourceSelf.trans sourceSelfZero)
    obtain
      ⟨output, outputNonzero, sourceOutputNonzero, outputSquarePos⟩ :=
        wholeRestartCrossingSourceSelfVisibleSquare_generates_positive_outputRow
          tail index crossed sourceSelfNonzero
    have sourceSelfRowNonzero :
        wholeRestartCrossingFiniteComponentSelfRow
          tail index crossed output ≠ 0 := by
      intro sourceSelfRowZero
      apply sourceOutputNonzero
      rw [wholeRestartCrossingFiniteComponentSelfNegativeOneState_apply,
        if_neg outputNonzero, sourceSelfRowZero]
      simp
    have existsFirst :
        ∃ first : IntegerWavevector,
          wholeRestartCrossingFiniteComponentSelfPairOccurrence
            tail index crossed output first ≠ 0 := by
      by_contra noFirst
      push Not at noFirst
      apply sourceSelfRowNonzero
      rw [←
        tsum_wholeRestartCrossingFiniteComponentSelfPairOccurrence_eq
          tail index crossed output]
      simp [noFirst]
    obtain ⟨first, selfPairNonzero⟩ := existsFirst
    have outputSquareLePayment :
        wholeRestartCrossingSourceSelfVisibleSquareRow
              tail index crossed output ≤
          wholeRestartCrossingSourceSelfVisibleSquarePayment
            tail index crossed := by
      unfold wholeRestartCrossingSourceSelfVisibleSquarePayment
      exact
        (summable_wholeRestartCrossingSourceSelfVisibleSquareRow
          tail index crossed).le_tsum output
            (fun other _otherNe =>
              wholeRestartCrossingSourceSelfVisibleSquareRow_nonneg
                tail index crossed other)
    have countNonneg :
        0 ≤
          (canonicalHalfCriticalComponentCount ν
            (wholeRestartCrossingFiniteCoreState
              tail index crossed) : ℝ) := by
      positivity
    have outputSquareCountLe :
        (canonicalHalfCriticalComponentCount ν
              (wholeRestartCrossingFiniteCoreState
                tail index crossed) : ℝ) *
            wholeRestartCrossingSourceSelfVisibleSquareRow
              tail index crossed output ≤
          ν.coeff * (2 * Real.pi) ^ 2 *
            wholeStateVorticityGradientMass
              (wholeRestartCrossingFiniteCoreState
                tail index crossed) := by
      calc
        (canonicalHalfCriticalComponentCount ν
              (wholeRestartCrossingFiniteCoreState
                tail index crossed) : ℝ) *
            wholeRestartCrossingSourceSelfVisibleSquareRow
              tail index crossed output ≤
          (canonicalHalfCriticalComponentCount ν
              (wholeRestartCrossingFiniteCoreState
                tail index crossed) : ℝ) *
            wholeRestartCrossingSourceSelfVisibleSquarePayment
              tail index crossed :=
          mul_le_mul_of_nonneg_left outputSquareLePayment countNonneg
        _ ≤
          ν.coeff * (2 * Real.pi) ^ 2 *
            wholeStateVorticityGradientMass
              (wholeRestartCrossingFiniteCoreState
                tail index crossed) :=
          wholeRestartCrossing_componentCount_mul_sourceSelfVisibleSquarePayment_le_gradient
            tail index crossed
    have selfPairSquarePos :
        0 <
          ‖wholeRestartCrossingFiniteComponentSelfPairOccurrence
              tail index crossed output first‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr selfPairNonzero)
    have selfPairEq :
        wholeRestartCrossingFiniteComponentSelfPairOccurrence
              tail index crossed output first =
          ((canonicalHalfCriticalComponentCount ν
              (wholeRestartCrossingFiniteCoreState
                tail index crossed) : ℝ)⁻¹ : ℂ) •
            finiteStateVorticityNonlinearPairContribution
              (wholeRestartCrossingFiniteCoreState
                tail index crossed)
              (first, output - first) :=
      wholeRestartCrossingFiniteComponentSelfPairOccurrence_eq_core_smul
        tail index crossed output first
    refine
      ⟨output, first, outputNonzero, sourceOutputNonzero,
        outputSquarePos, outputSquareCountLe, selfPairNonzero,
        selfPairSquarePos, selfPairEq, ?_⟩
    let zeroTime :
        Icc (0 : ℝ) (run tail index).nextContact.time.1 :=
      ⟨0, ⟨le_rfl, (run tail index).nextContact.time_pos.le⟩⟩
    by_cases actualNonzero :
        actualWholeContinuousPairVector
          (run tail index).nextContact.prefixReceipt
          output first zeroTime ≠ 0
    · exact Or.inl actualNonzero
    right
    have completeGluingNonzero :
        wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
          tail index crossed output first zeroTime ≠ 0 := by
      intro completeGluingZero
      apply selfPairNonzero
      have split :=
        actualWholeContinuousPairVector_eq_crossingSourceSelf_add_completeGluing
          tail index crossed output first zeroTime
      rw [not_ne_iff.mp actualNonzero, completeGluingZero] at split
      simpa using split.symm
    let tailElapsedBounded :
        BddAbove (Set.range (elapsedTime tail)) :=
      elapsedTime_run_bddAbove initial elapsedBounded (scale.start step)
    let nextCrossed :
        wholeRestartHalfCriticalCrossed tail (index + 1) :=
      elapsedTime_bddAbove_forces_every_halfCriticalCrossing
        tail tailElapsedBounded (index + 1)
    exact
      wholeRestartCrossingCompleteOutgoingPairGluing_ne_zero_redirect
        tail index crossed nextCrossed output first zeroTime
        completeGluingNonzero

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
