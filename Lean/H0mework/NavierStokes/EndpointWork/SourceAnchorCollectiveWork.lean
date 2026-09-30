import H0mework.NavierStokes.EndpointWork.AnchoredMixedWork
import H0mework.NavierStokes.PairRestart.AnchoredReflectedPairNativeProcess

/-!
# Source-anchor work forced by a positive endpoint kinetic atom

A source-generated positive endpoint atom already produces arbitrarily late
actual collective velocity gaps.  Actual unforced kinetic antitonicity fixes
the sign of the missing angular term: for the source-selected segment,

```text
Σᵢ Re⟪u_start, qᵢ⟫ < -atom / 4.
```

The anchor is the literal first contact of that same generated segment and
each `qᵢ` is its actual native causal write.  No anchor, endpoint, path,
sign, output, pair, cutoff, or settlement witness is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorCollectiveWork

open scoped BigOperators

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedWholeRestartEndpointMacroStep
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointCofinalPairDuhamelMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCollectiveCausalGapWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomAnchoredMixedWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredReflectedPairNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredReflectedPairNativeProcess.WholeRestartAnchoredReflectedPairFrame

noncomputable section

/-- Pairing one actual source anchor with one later native edge commutes with
the complete physical Fourier `tsum`. -/
theorem wholeRestartSourceAnchorNativeCausalVelocityWrite_realInner_eq_tsum
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start index : ℕ) :
    RCLike.re (inner ℂ
        (wholeRestartContactVelocityState current start)
        (wholeRestartNativeCausalVelocityWrite current index)) =
      ∑' wave : NonzeroIntegerWavevector,
        RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current start wave)
          (wholeRestartNativeCausalVelocityWrite current index wave)) := by
  rw [lp.inner_eq_tsum]
  exact Complex.reCLM.map_tsum
    (lp.summable_inner
      (wholeRestartContactVelocityState current start)
      (wholeRestartNativeCausalVelocityWrite current index))

private theorem
    physicalStageKineticEnergyAtom_pos_generates_cofinal_negativeSourceAnchorCollectiveWork
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (atomPositive : 0 < step.physicalStageKineticEnergyAtom)
    (requestedStart : ℕ) :
    ∃ start steps : ℕ,
      requestedStart ≤ start ∧
        0 < steps ∧
        wholeRestartCollectiveCausalVelocityWrite current start steps =
          wholeRestartContactVelocityState current (start + steps) -
            wholeRestartContactVelocityState current start ∧
        step.physicalStageKineticEnergyAtom / 2 <
          ‖wholeRestartCollectiveCausalVelocityWrite
            current start steps‖ ^ 2 ∧
        (∑ offset ∈ Finset.range steps,
          RCLike.re (inner ℂ
            (wholeRestartContactVelocityState current start)
            (wholeRestartNativeCausalVelocityWrite
              current (start + offset)))) <
          -step.physicalStageKineticEnergyAtom / 4 ∧
        2 * (∑ offset ∈ Finset.range steps,
          RCLike.re (inner ℂ
            (wholeRestartContactVelocityState current start)
            (wholeRestartNativeCausalVelocityWrite
              current (start + offset)))) =
          (‖wholeRestartContactVelocityState
                current (start + steps)‖ ^ 2 -
              ‖wholeRestartContactVelocityState current start‖ ^ 2) -
            ‖wholeRestartCollectiveCausalVelocityWrite
              current start steps‖ ^ 2 ∧
        ∃ frame : WholeRestartAnchoredReflectedPairFrame,
          frame.start = start ∧
            frame.offset < steps ∧
            frame.currentIndex = start + frame.offset ∧
            run current (frame.currentIndex + 1) =
              (run current frame.currentIndex).next ∧
            wholeRestartNativeCausalVelocityWrite
              current frame.currentIndex ≠ 0 ∧
            RCLike.re (inner ℂ
              (wholeRestartContactVelocityState current frame.start)
              (wholeRestartNativeCausalVelocityWrite
                current frame.currentIndex)) < 0 ∧
            ∃ wave : NonzeroIntegerWavevector,
              RCLike.re (inner ℂ
                (wholeRestartContactVelocityState current frame.start wave)
                (euclideanCoordinateRow
                  (biotSavartVelocityCoefficient wave.1
                    (wholeRestartCausalTangentGain
                          current frame.currentIndex wave.1 •
                        wholeRestartCrossingUnforcedTangentRow
                          current frame.currentIndex wave.1 +
                      ∑' first : IntegerWavevector,
                        wholeRestartPairDuhamelInnovationOccurrence
                          current frame.currentIndex wave.1 first)))) < 0 := by
  obtain
      ⟨start, steps, requestedLe, stepsPositive, gapEq,
        collectiveLower, _compiler⟩ :=
    physicalStageKineticEnergyAtom_pos_generates_cofinal_collectiveCausalGapWrite
      step atomPositive requestedStart
  have kineticMassLe :=
    run_contact_kineticMass_antitone current
      (Nat.le_add_right start steps)
  have velocityNormSqLe :
      ‖wholeRestartContactVelocityState current (start + steps)‖ ^ 2 ≤
        ‖wholeRestartContactVelocityState current start‖ ^ 2 := by
    rw [wholeRestartContactVelocityState_norm_sq,
      wholeRestartContactVelocityState_norm_sq]
    exact kineticMassLe
  have endpointEq :
      wholeRestartContactVelocityState current (start + steps) =
        wholeRestartContactVelocityState current start +
          wholeRestartCollectiveCausalVelocityWrite
            current start steps := by
    rw [gapEq]
    abel
  have polarization :
      ‖wholeRestartContactVelocityState current (start + steps)‖ ^ 2 =
        ‖wholeRestartContactVelocityState current start‖ ^ 2 +
          2 * RCLike.re (inner ℂ
            (wholeRestartContactVelocityState current start)
            (wholeRestartCollectiveCausalVelocityWrite
              current start steps)) +
          ‖wholeRestartCollectiveCausalVelocityWrite
            current start steps‖ ^ 2 := by
    rw [endpointEq, norm_add_sq (𝕜 := ℂ)]
  have anchorWorkNegative :
      RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current start)
          (wholeRestartCollectiveCausalVelocityWrite
            current start steps)) <
        -step.physicalStageKineticEnergyAtom / 4 := by
    linarith
  have anchorWorkEq :
      RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current start)
          (wholeRestartCollectiveCausalVelocityWrite
            current start steps)) =
        ∑ offset ∈ Finset.range steps,
          RCLike.re (inner ℂ
            (wholeRestartContactVelocityState current start)
            (wholeRestartNativeCausalVelocityWrite
              current (start + offset))) := by
    unfold wholeRestartCollectiveCausalVelocityWrite
    rw [inner_sum]
    change
      Complex.reCLM
          (∑ offset ∈ Finset.range steps,
            inner ℂ
              (wholeRestartContactVelocityState current start)
              (wholeRestartNativeCausalVelocityWrite
                current (start + offset))) =
        ∑ offset ∈ Finset.range steps,
          Complex.reCLM
            (inner ℂ
              (wholeRestartContactVelocityState current start)
              (wholeRestartNativeCausalVelocityWrite
                current (start + offset)))
    simp only [map_sum]
  have anchorWorkIdentity :
      2 * (∑ offset ∈ Finset.range steps,
          RCLike.re (inner ℂ
            (wholeRestartContactVelocityState current start)
            (wholeRestartNativeCausalVelocityWrite
              current (start + offset)))) =
        (‖wholeRestartContactVelocityState
              current (start + steps)‖ ^ 2 -
            ‖wholeRestartContactVelocityState current start‖ ^ 2) -
          ‖wholeRestartCollectiveCausalVelocityWrite
            current start steps‖ ^ 2 := by
    rw [← anchorWorkEq]
    linarith
  have anchorSumNegative :
      (∑ offset ∈ Finset.range steps,
          RCLike.re (inner ℂ
            (wholeRestartContactVelocityState current start)
            (wholeRestartNativeCausalVelocityWrite
              current (start + offset)))) < 0 := by
    rw [← anchorWorkEq]
    linarith
  have existsNegativeEdge :
      ∃ offset ∈ Finset.range steps,
        RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current start)
          (wholeRestartNativeCausalVelocityWrite
            current (start + offset))) < 0 := by
    by_contra noNegativeEdge
    push Not at noNegativeEdge
    have sumNonnegative :
        0 ≤ ∑ offset ∈ Finset.range steps,
          RCLike.re (inner ℂ
            (wholeRestartContactVelocityState current start)
            (wholeRestartNativeCausalVelocityWrite
              current (start + offset))) :=
      Finset.sum_nonneg fun offset offsetMem =>
        noNegativeEdge offset offsetMem
    linarith
  obtain ⟨offset, offsetMem, edgeNegative⟩ := existsNegativeEdge
  have writeNonzero :
      wholeRestartNativeCausalVelocityWrite
        current (start + offset) ≠ 0 := by
    intro writeZero
    rw [writeZero, inner_zero_right, map_zero] at edgeNegative
    exact (lt_irrefl 0) edgeNegative
  have existsNegativeWave :
      ∃ wave : NonzeroIntegerWavevector,
        RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current start wave)
          (wholeRestartNativeCausalVelocityWrite
            current (start + offset) wave)) < 0 := by
    by_contra noNegativeWave
    push Not at noNegativeWave
    have waveSumNonnegative :
        0 ≤ ∑' wave : NonzeroIntegerWavevector,
          RCLike.re (inner ℂ
            (wholeRestartContactVelocityState current start wave)
            (wholeRestartNativeCausalVelocityWrite
              current (start + offset) wave)) :=
      tsum_nonneg noNegativeWave
    rw [
      ←
        wholeRestartSourceAnchorNativeCausalVelocityWrite_realInner_eq_tsum
          current start (start + offset)] at waveSumNonnegative
    linarith
  obtain ⟨wave, waveNegative⟩ := existsNegativeWave
  have compiledWaveNegative :
      RCLike.re (inner ℂ
        (wholeRestartContactVelocityState current start wave)
        (euclideanCoordinateRow
          (biotSavartVelocityCoefficient wave.1
            (wholeRestartCausalTangentGain
                  current (start + offset) wave.1 •
                wholeRestartCrossingUnforcedTangentRow
                  current (start + offset) wave.1 +
              ∑' first : IntegerWavevector,
                wholeRestartPairDuhamelInnovationOccurrence
                  current (start + offset) wave.1 first)))) < 0 := by
    rw [
      ←
        wholeRestartNativeCausalVelocityWrite_apply_eq_causalTangent_add_pairInnovation]
    exact waveNegative
  let frame : WholeRestartAnchoredReflectedPairFrame :=
    { start := start, offset := offset }
  exact
    ⟨start, steps, requestedLe, stepsPositive, gapEq, collectiveLower,
      anchorWorkEq ▸ anchorWorkNegative, anchorWorkIdentity,
      frame, rfl, Finset.mem_range.mp offsetMem, rfl, run_succ current _,
      writeNonzero, edgeNegative, wave, compiledWaveNegative⟩

/-- A whole endpoint macro step internally exhausts its atom into either the
zero branch or an arbitrarily late actual finite segment carrying strictly
negative source-anchor work.  The positive branch and its quantitative
threshold are selected from the step's own endpoint receipt. -/
theorem
    wholeRestartEndpointMacroStep_generates_zero_or_cofinal_negativeSourceAnchorCollectiveWork
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    (wholeRestartEndpointCausalMacroFrame current step.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 =
        next ∧
      (step.physicalStageKineticEnergyAtom = 0 ∨
        ∀ requestedStart : ℕ,
          ∃ start steps : ℕ,
            requestedStart ≤ start ∧
              0 < steps ∧
              wholeRestartCollectiveCausalVelocityWrite current start steps =
                wholeRestartContactVelocityState current (start + steps) -
                  wholeRestartContactVelocityState current start ∧
              step.physicalStageKineticEnergyAtom / 2 <
                ‖wholeRestartCollectiveCausalVelocityWrite
                  current start steps‖ ^ 2 ∧
              (∑ offset ∈ Finset.range steps,
                RCLike.re (inner ℂ
                  (wholeRestartContactVelocityState current start)
                  (wholeRestartNativeCausalVelocityWrite
                    current (start + offset)))) <
                -step.physicalStageKineticEnergyAtom / 4 ∧
              2 * (∑ offset ∈ Finset.range steps,
                RCLike.re (inner ℂ
                  (wholeRestartContactVelocityState current start)
                  (wholeRestartNativeCausalVelocityWrite
                    current (start + offset)))) =
                (‖wholeRestartContactVelocityState
                      current (start + steps)‖ ^ 2 -
                    ‖wholeRestartContactVelocityState current start‖ ^ 2) -
                  ‖wholeRestartCollectiveCausalVelocityWrite
                    current start steps‖ ^ 2 ∧
              ∃ frame : WholeRestartAnchoredReflectedPairFrame,
                frame.start = start ∧
                  frame.offset < steps ∧
                  frame.currentIndex = start + frame.offset ∧
                  run current (frame.currentIndex + 1) =
                    (run current frame.currentIndex).next ∧
                  wholeRestartNativeCausalVelocityWrite
                    current frame.currentIndex ≠ 0 ∧
                  RCLike.re (inner ℂ
                    (wholeRestartContactVelocityState current frame.start)
                    (wholeRestartNativeCausalVelocityWrite
                      current frame.currentIndex)) < 0 ∧
                  ∃ wave : NonzeroIntegerWavevector,
                    RCLike.re (inner ℂ
                      (wholeRestartContactVelocityState
                        current frame.start wave)
                      (euclideanCoordinateRow
                        (biotSavartVelocityCoefficient wave.1
                          (wholeRestartCausalTangentGain
                                current frame.currentIndex wave.1 •
                              wholeRestartCrossingUnforcedTangentRow
                                current frame.currentIndex wave.1 +
                            ∑' first : IntegerWavevector,
                              wholeRestartPairDuhamelInnovationOccurrence
                                current frame.currentIndex
                                  wave.1 first)))) < 0) := by
  constructor
  · cases step with
    | advance elapsedBounded =>
        exact
          (wholeRestartEndpointCausalMacroFrame_physical_update
              elapsedBounded).trans
            (sourceGeneratedWholeRestartVelocityEndpointNextCurrent_eq_rootCofinalPhysicalNext
              current elapsedBounded)
  · let endpointReceipt :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        current step.elapsedBounded).family.endpointReceipt
    rcases endpointReceipt.kineticReceipt.defect_disposition with
      defectPositive | defectZero
    · right
      have atomPositive : 0 < step.physicalStageKineticEnergyAtom := by
        rw [step.physicalStageKineticEnergyAtom_eq_defect]
        exact defectPositive
      intro requestedStart
      exact
        physicalStageKineticEnergyAtom_pos_generates_cofinal_negativeSourceAnchorCollectiveWork
          step atomPositive requestedStart
    · left
      rw [step.physicalStageKineticEnergyAtom_eq_defect]
      exact defectZero.1

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorCollectiveWork
end NavierStokes
end SaturationMonoid
