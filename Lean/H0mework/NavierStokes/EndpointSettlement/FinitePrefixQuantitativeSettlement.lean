import H0mework.NavierStokes.EndpointSettlement.PairQuantitativeSettlement

/-!
# Finite-prefix quantitative settlement on the reduced-core scale lineage

The source-generated node disposition is aggregated before any pair or time
quotient.  For every finite prefix the source itself selects a nonnegative
kinetic charge at each node: the annular branch retains its actual positive
charge, while the pair branch writes zero into the kinetic coordinate and
retains the complete causal visible/kernel/native settlement.

Strict absolute occurrences inject these charges into the authoritative
whole-run kinetic telescope.  Hence no restart chart can pay one annular
responsibility twice.  No branch, charge, output, pair, time, path, budget,
or target state is accepted from the caller.
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
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
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
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartComponentGluingResidualNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairOccurrenceGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairVisibleSquareLedger

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- One source-generated finite scale prefix carries its actual update and
keep law at every node.  Its annular kinetic charges are selected internally,
and their total is paid once by the initial whole kinetic mass; every
zero-charge node retains the full reciprocal pair settlement. -/
theorem
    WholeRestartReducedCoreScaleLineage.finitePrefix_pairQuantitativeSettlement
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (length : ℕ) :
    ∃ kineticCharge : ℕ → ℝ,
      (∀ step < length,
        let tail := run initial (scale.start step)
        let index := scale.relativeIndex step
        let crossed := scale.crossed step
        let tailElapsedBounded :
            BddAbove (Set.range (elapsedTime tail)) :=
          elapsedTime_run_bddAbove
            initial elapsedBounded (scale.start step)
        run tail (wholeRestartComponentGluingNativeUpdate index) =
            (run tail index).next ∧
          wholeRestartComponentGluingResidualTail tail (index + 1) =
            wholeRestartComponentGluingResidualTailKeep
              (wholeRestartComponentGluingResidualTail tail index) ∧
          0 ≤ kineticCharge step ∧
          ((0 < kineticCharge step ∧
            kineticCharge step ≤
              wholeRestartNextKineticDissipationPayment
                initial (scale.absoluteOccurrence step) ∧
            ∃ actual :
                Ioo (0 : ℝ) (run tail index).nextContact.time.1,
              let initialMass :=
                finiteStateVorticityCoefficientEnstrophy
                  (scale.annularModes step)
                  (run tail index).contact.physicalState
              kineticCharge step =
                  ν.coeff * actual.1 * initialMass ∧
                (2 * Real.pi) ^ 2 *
                      ((scale.requestedRadius step + 1 : ℕ) : ℝ) ^ 2 *
                      kineticCharge step <
                  initialMass -
                    finiteStateVorticityCoefficientEnstrophy
                      (scale.annularModes step)
                      ((run tail index).nextContact.prefixReceipt.wholePath
                        ⟨actual.1, actual.2.1.le, actual.2.2.le⟩)) ∨
          (kineticCharge step = 0 ∧
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
                  tail tailElapsedBounded index output first))) ∧
      (∑ step ∈ Finset.range length, kineticCharge step) ≤
        puncturedWholeVorticityKineticMass
          initial.contact.physicalState := by
  have perStep :
      ∀ step : ℕ,
        ∃ charge : ℝ,
          let tail := run initial (scale.start step)
          let index := scale.relativeIndex step
          let crossed := scale.crossed step
          let tailElapsedBounded :
              BddAbove (Set.range (elapsedTime tail)) :=
            elapsedTime_run_bddAbove
              initial elapsedBounded (scale.start step)
          run tail (wholeRestartComponentGluingNativeUpdate index) =
              (run tail index).next ∧
            wholeRestartComponentGluingResidualTail tail (index + 1) =
              wholeRestartComponentGluingResidualTailKeep
                (wholeRestartComponentGluingResidualTail tail index) ∧
            0 ≤ charge ∧
            ((0 < charge ∧
              charge ≤
                wholeRestartNextKineticDissipationPayment
                  initial (scale.absoluteOccurrence step) ∧
              ∃ actual :
                  Ioo (0 : ℝ) (run tail index).nextContact.time.1,
                let initialMass :=
                  finiteStateVorticityCoefficientEnstrophy
                    (scale.annularModes step)
                    (run tail index).contact.physicalState
                charge = ν.coeff * actual.1 * initialMass ∧
                  (2 * Real.pi) ^ 2 *
                        ((scale.requestedRadius step + 1 : ℕ) : ℝ) ^ 2 *
                        charge <
                    initialMass -
                      finiteStateVorticityCoefficientEnstrophy
                        (scale.annularModes step)
                        ((run tail index).nextContact.prefixReceipt.wholePath
                          ⟨actual.1, actual.2.1.le, actual.2.2.le⟩)) ∨
            (charge = 0 ∧
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
                    tail tailElapsedBounded index output first)) := by
    intro step
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
    · rcases annular with
        ⟨actual, chargePos, chargeLe, radiusDrop⟩
      let initialMass :=
        finiteStateVorticityCoefficientEnstrophy
          (scale.annularModes step)
          (run tail index).contact.physicalState
      have paymentEq :
          wholeRestartNextKineticDissipationPayment tail index =
            wholeRestartNextKineticDissipationPayment
              initial (scale.absoluteOccurrence step) := by
        unfold wholeRestartNextKineticDissipationPayment
        rw [run_run]
        rfl
      refine
        ⟨ν.coeff * actual.1 * initialMass,
          updateEq, residualEq, chargePos.le, Or.inl ?_⟩
      exact
        ⟨chargePos, paymentEq ▸ chargeLe, actual, rfl, radiusDrop⟩
    · rcases pair with
        ⟨output, first, outputNonzero, outputSquarePos,
          outputSquareCountLe, selfPairSquarePos, selfPairEq,
          settlement⟩
      exact
        ⟨0, updateEq, residualEq, le_rfl, Or.inr
          ⟨rfl, output, first, outputNonzero, outputSquarePos,
            outputSquareCountLe, selfPairSquarePos, selfPairEq,
            settlement⟩⟩
  let kineticCharge : ℕ → ℝ :=
    fun step => Classical.choose (perStep step)
  have kineticChargeSpec :
      ∀ step : ℕ,
        let tail := run initial (scale.start step)
        let index := scale.relativeIndex step
        let crossed := scale.crossed step
        let tailElapsedBounded :
            BddAbove (Set.range (elapsedTime tail)) :=
          elapsedTime_run_bddAbove
            initial elapsedBounded (scale.start step)
        run tail (wholeRestartComponentGluingNativeUpdate index) =
            (run tail index).next ∧
          wholeRestartComponentGluingResidualTail tail (index + 1) =
            wholeRestartComponentGluingResidualTailKeep
              (wholeRestartComponentGluingResidualTail tail index) ∧
          0 ≤ kineticCharge step ∧
          ((0 < kineticCharge step ∧
            kineticCharge step ≤
              wholeRestartNextKineticDissipationPayment
                initial (scale.absoluteOccurrence step) ∧
            ∃ actual :
                Ioo (0 : ℝ) (run tail index).nextContact.time.1,
              let initialMass :=
                finiteStateVorticityCoefficientEnstrophy
                  (scale.annularModes step)
                  (run tail index).contact.physicalState
              kineticCharge step =
                  ν.coeff * actual.1 * initialMass ∧
                (2 * Real.pi) ^ 2 *
                      ((scale.requestedRadius step + 1 : ℕ) : ℝ) ^ 2 *
                      kineticCharge step <
                  initialMass -
                    finiteStateVorticityCoefficientEnstrophy
                      (scale.annularModes step)
                      ((run tail index).nextContact.prefixReceipt.wholePath
                        ⟨actual.1, actual.2.1.le, actual.2.2.le⟩)) ∨
          (kineticCharge step = 0 ∧
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
                  tail tailElapsedBounded index output first)) :=
    fun step => Classical.choose_spec (perStep step)
  refine ⟨kineticCharge, ?_, ?_⟩
  · intro step _stepMem
    exact kineticChargeSpec step
  · have chargeLe :
        ∀ step : ℕ,
          kineticCharge step ≤
            wholeRestartNextKineticDissipationPayment
              initial (scale.absoluteOccurrence step) := by
      intro step
      rcases (kineticChargeSpec step).2.2.2 with annular | pair
      · exact annular.2.1
      · rw [pair.1]
        exact
          wholeRestartNextKineticDissipationPayment_nonneg
            initial (scale.absoluteOccurrence step)
    calc
      (∑ step ∈ Finset.range length, kineticCharge step) ≤
          ∑ step ∈ Finset.range length,
            wholeRestartNextKineticDissipationPayment
              initial (scale.absoluteOccurrence step) :=
        Finset.sum_le_sum fun step _stepMem => chargeLe step
      _ =
          ∑ occurrence ∈
              (Finset.range length).image scale.absoluteOccurrence,
            wholeRestartNextKineticDissipationPayment
              initial occurrence := by
        rw [Finset.sum_image]
        intro left _leftMem right _rightMem occurrenceEq
        exact scale.absoluteOccurrence_strict.injective occurrenceEq
      _ ≤
          wholeRestartAccumulatedKineticDissipationPayment
            initial (scale.absoluteOccurrence length) := by
        unfold wholeRestartAccumulatedKineticDissipationPayment
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro occurrence occurrenceMem
          rw [Finset.mem_image] at occurrenceMem
          obtain ⟨step, stepMem, rfl⟩ := occurrenceMem
          rw [Finset.mem_range] at stepMem ⊢
          exact scale.absoluteOccurrence_strict stepMem
        · intro occurrence _occurrenceMem _occurrenceNotSelected
          exact
            wholeRestartNextKineticDissipationPayment_nonneg
              initial occurrence
      _ ≤
          puncturedWholeVorticityKineticMass
            initial.contact.physicalState :=
        wholeRestartAccumulatedKineticDissipationPayment_le_initial
          initial (scale.absoluteOccurrence length)

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
