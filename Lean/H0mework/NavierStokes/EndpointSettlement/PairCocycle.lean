import H0mework.NavierStokes.EndpointSettlement.ScaleLineage
import H0mework.NavierStokes.Crossing.PairGluingNativeCocycle
import H0mework.NavierStokes.Crossing.TangentQuantumCascade

/-!
# Pair-cocycle consumer of the reduced-core scale lineage

Every node of the generated reduced-core scale path is consumed before pair
aggregation.  If its whole nonlinear `H⁻¹` state is nonzero, the exact
reciprocal forcing identity generates a nonzero primitive self-pair
occurrence.  The same actual contact occurrence is then either physically
visible or forces a nonzero complete-gluing occurrence, which the existing
native cocycle redirects into the current trace, the adjacent source update,
or the next crossing keep.

Thus scalar gluing zero cannot silently erase the pair occurrence.  No output,
input pair, next crossing, or nonzero witness is supplied by the caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingWholeSourceGluingLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingSelfForcingReduction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairOccurrenceGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairGluingNativeCocycle
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentQuantumCascade

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- At one generated reduced-core node, either the actual whole nonlinear
state vanishes or a source-generated primitive pair occurrence is paid by
the same actual pair readout or redirected through the native three-term
gluing cocycle. -/
theorem WholeRestartReducedCoreScaleLineage.node_pairCocycleDisposition
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
    Nonempty (WholeRestartCrossingTangentQuantumReceipt tail index) ∧
      (wholeStateVorticityNonlinearNegativeOneState
            (run tail index).contact.physicalState
            (run tail index).contact.transverse
            (run tail index).contact.gradient_summable = 0 ∨
        ∃ output first : IntegerWavevector,
          wholeRestartCrossingFiniteComponentSelfPairOccurrence
                tail index crossed output first ≠ 0 ∧
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
                    (run tail (index + 1)).nextContact.time_pos.le⟩⟩ ≠ 0)) := by
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
    ⟨⟨wholeRestartCrossingTangentQuantumReceiptOfCrossed
        tail index crossed⟩, ?_⟩
  by_cases wholeZero : wholeNegativeOne = 0
  · exact Or.inl wholeZero
  right
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
              tail index crossed :=
        scale.reducedForcing step
      _ = sourceSelfNegativeOne :=
        (wholeRestartCrossingFiniteComponentSelfNegativeOneState_eq_core_smul
          tail index crossed).symm
  have sourceSelfNonzero : sourceSelfNegativeOne ≠ 0 := by
    intro sourceSelfZero
    exact wholeZero (wholeEqSourceSelf.trans sourceSelfZero)
  have existsOutput :
      ∃ output : IntegerWavevector,
        sourceSelfNegativeOne output ≠ 0 := by
    by_contra noOutput
    push Not at noOutput
    apply sourceSelfNonzero
    apply lp.ext
    funext output
    exact noOutput output
  obtain ⟨output, outputNonzero⟩ := existsOutput
  have sourceSelfRowNonzero :
      wholeRestartCrossingFiniteComponentSelfRow
        tail index crossed output ≠ 0 := by
    intro sourceSelfRowZero
    apply outputNonzero
    rw [wholeRestartCrossingFiniteComponentSelfNegativeOneState_apply]
    by_cases outputZero : output = 0
    · simp [outputZero]
    · simp [outputZero, sourceSelfRowZero]
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
  refine ⟨output, first, selfPairNonzero, ?_⟩
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
