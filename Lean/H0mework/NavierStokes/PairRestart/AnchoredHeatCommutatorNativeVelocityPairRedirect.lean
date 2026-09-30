import H0mework.NavierStokes.PairRestart.AnchoredReflectedPairNativeProcess

/-!
# Anchored heat-commutator native velocity-pair redirect

The anchored direct-work exhaustion already shows that a nonzero direct work
cannot disappear: it leaves either the anchored heat commutator or a
reflected ordered-pair next/trace responsibility.  This module closes the
remaining commutator branch on the same actual receipt.

A nonzero anchored heat-commutator integral generates a nonzero direct
velocity-pair occurrence at an actual physical time.  The existing
whole-restart pair process then retains that occurrence in its next current
or in the uniquely forced head trace.  Consequently every nonzero anchored
direct work reaches an actual pair responsibility; the commutator is not a
terminal readout.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredHeatCommutatorNativeVelocityPairRedirect

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHeatCommutatorNativeVelocityPairRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredReflectedPairNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredReflectedPairNativeProcess.WholeRestartAnchoredReflectedPairFrame
open AffineRelaxation

noncomputable section

/-! ## Same-receipt commutator redirect -/

/-- A nonzero anchored heat commutator generates a nonzero ordered
velocity-pair occurrence on the same actual receipt.  That occurrence is
written into the existing next contact or its exact whole-carrier head
trace.  The witness time is selected by the nonzero integral itself. -/
theorem
    wholeRestartAnchoredVelocityTriadHeatCommutatorTrace_ne_zero_generates_nativeVelocityPairResponsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector)
    (commutatorNonzero :
      wholeRestartAnchoredVelocityTriadHeatCommutatorTrace
        initial frame first second ≠ 0) :
    ∃ time :
        Icc (0 : ℝ)
          (run initial frame.currentIndex).nextContact.time.1,
      wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
          initial frame first second time ≠ 0 ∧
        actualWholeContinuousVelocityPairVector
          (run initial frame.currentIndex).nextContact.prefixReceipt
          first second time ≠ 0 ∧
        (wholeRestartNextVelocityPairOccurrence
              initial frame.currentIndex first second ≠ 0 ∨
          (linearResidualTrace
              wholeRestartSplicedVelocityPairOccurrenceTailKeep
              (wholeRestartSplicedVelocityPairOccurrenceTail
                initial frame.currentIndex time 0) 0)
                first second ≠ 0) ∧
        run initial frame.next.currentIndex =
          (run initial frame.currentIndex).next := by
  have energyOccurrenceExists :
      ∃ time :
          Icc (0 : ℝ)
            (run initial frame.currentIndex).nextContact.time.1,
        wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
          initial frame first second time ≠ 0 := by
    by_contra everyOccurrenceZero
    push Not at everyOccurrenceZero
    apply commutatorNonzero
    unfold wholeRestartAnchoredVelocityTriadHeatCommutatorTrace
    simp [everyOccurrenceZero]
  obtain ⟨time, energyNonzero⟩ := energyOccurrenceExists
  have velocityPairNonzero :
      actualWholeContinuousVelocityPairVector
          (run initial frame.currentIndex).nextContact.prefixReceipt
          first second time ≠ 0 := by
    intro pairZero
    apply energyNonzero
    unfold wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
      finiteStateVelocityBilinearEnergyOccurrence
      actualWholeContinuousVelocityPairVector at *
    rw [pairZero]
    exact complexCoordinateRealInner_zero_right _
  have nativeResponsibility :=
    actualWholeContinuousVelocityPairVector_ne_zero_next_or_trace
      initial frame.currentIndex first second time velocityPairNonzero
  refine
    ⟨time, energyNonzero, velocityPairNonzero, ?_,
      generatedWholeRestartAnchoredReflectedPairNativeResponse_physical
        initial frame⟩
  rcases nativeResponsibility with nextNonzero | traceNonzero
  · exact Or.inl nextNonzero
  · exact Or.inr (by
      rw [
        wholeRestartSplicedVelocityPairOccurrence_trace_head_apply_eq_occurrenceTrace]
      exact traceNonzero)

/-! ## Direct-work native exhaustion with no commutator terminal -/

/-- Every nonzero anchored direct work reaches an actual ordered-pair
responsibility.  The heat-commutator branch enters the ordinary same-receipt
pair process; the complementary branch enters the reflected anchored
pair process.  No time, branch, pair, target, or settlement witness is
supplied by the caller. -/
theorem
    wholeRestartAnchoredDirectVelocityBilinearEnergyWork_ne_zero_generates_nativePairResponsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector)
    (directNonzero :
      wholeRestartAnchoredDirectVelocityBilinearEnergyWork
        initial frame first second ≠ 0) :
    (∃ time :
        Icc (0 : ℝ)
          (run initial frame.currentIndex).nextContact.time.1,
      wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
          initial frame first second time ≠ 0 ∧
        actualWholeContinuousVelocityPairVector
          (run initial frame.currentIndex).nextContact.prefixReceipt
          first second time ≠ 0 ∧
        (wholeRestartNextVelocityPairOccurrence
              initial frame.currentIndex first second ≠ 0 ∨
          (linearResidualTrace
              wholeRestartSplicedVelocityPairOccurrenceTailKeep
              (wholeRestartSplicedVelocityPairOccurrenceTail
                initial frame.currentIndex time 0) 0)
                first second ≠ 0) ∧
        run initial frame.next.currentIndex =
          (run initial frame.currentIndex).next) ∨
      ∃ time :
          Icc (0 : ℝ)
            (run initial frame.currentIndex).nextContact.time.1,
        wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence
            initial frame first second time ≠ 0 ∧
          actualWholeRestartAnchoredReflectedVelocityPairVector
              initial frame first
                (outputNegSecondEquiv first second) time ≠ 0 ∧
          (wholeRestartAnchoredReflectedNextVelocityPairOccurrence
                initial frame first
                  (outputNegSecondEquiv first second) ≠ 0 ∨
            wholeRestartAnchoredReflectedVelocityPairOccurrenceTrace
                initial frame first
                  (outputNegSecondEquiv first second) time ≠ 0) ∧
          run initial frame.next.currentIndex =
            (run initial frame.currentIndex).next := by
  rcases
      wholeRestartAnchoredVelocityBilinearEnergyWork_nativeExhaustion
        initial frame first second with
    directZero | commutatorOrReflected
  · exact (directNonzero directZero).elim
  · rcases commutatorOrReflected with
      commutatorNonzero | reflectedResponsibility
    · exact Or.inl
        (wholeRestartAnchoredVelocityTriadHeatCommutatorTrace_ne_zero_generates_nativeVelocityPairResponsibility
          initial frame first second commutatorNonzero)
    · exact Or.inr reflectedResponsibility

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredHeatCommutatorNativeVelocityPairRedirect
end NavierStokes
end SaturationMonoid
