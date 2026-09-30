import H0mework.NavierStokes.Restart.GlobalPhysicalTrajectory
import H0mework.NavierStokes.Crossing.TangentPaymentCascade

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeGlobalTailOccurrence

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade

noncomputable section

variable {nu : Viscosity}

theorem tail_unbounded (current : GeneratedWholeRestartCurrent nu)
    (unbounded : ¬ BddAbove (range (elapsedTime current))) (start : ℕ) :
    ¬ BddAbove (range (elapsedTime (run current start))) := by
  rintro ⟨upper, bounded⟩
  apply unbounded
  refine ⟨elapsedTime current start + upper, ?_⟩
  rintro _ ⟨index, rfl⟩
  have forward := (elapsedTime_strictMono current).monotone (show index ≤ start + index by omega)
  have source := bounded (mem_range_self index)
  rw [← elapsedTime_run_add current start index] at forward
  linarith

def tail {current : GeneratedWholeRestartCurrent nu} (global : GeneratedWholeGlobalPhysicalTrajectory current) (start : ℕ) :
    GeneratedWholeGlobalPhysicalTrajectory (run current start) :=
  generatedWholeGlobalPhysicalTrajectory_of_unbounded (run current start) (tail_unbounded current global.timeUnbounded start)

theorem tail_path_zero {current : GeneratedWholeRestartCurrent nu}
    (global : GeneratedWholeGlobalPhysicalTrajectory current) (start : ℕ) :
    (tail global start).physicalPath 0 = global.physicalPath (elapsedTime current start) := by
  have original := global.receipt_chart start ⟨0, le_rfl, (run current start).contact.time_pos.le⟩
  rw [add_zero, (run current start).contact.prefixReceipt.wholePath_initial] at original
  exact (tail global start).initial_eq.trans original.symm

private theorem receipt_read_eq {left right : GeneratedWholeRestartCurrent nu} (same : left = right)
    (leftTime : Icc (0 : ℝ) left.contact.time.1) (rightTime : Icc (0 : ℝ) right.contact.time.1)
    (timeEq : leftTime.1 = rightTime.1) :
    left.contact.prefixReceipt.wholePath leftTime = right.contact.prefixReceipt.wholePath rightTime := by
  subst right
  cases Subtype.ext timeEq
  rfl

theorem tail_receipt_chart {current : GeneratedWholeRestartCurrent nu}
    (global : GeneratedWholeGlobalPhysicalTrajectory current) (start index : ℕ)
    (localTime : Icc (0 : ℝ) (run (run current start) index).contact.time.1) :
    (tail global start).physicalPath (elapsedTime (run current start) index + localTime.1) =
      global.physicalPath (elapsedTime current start + (elapsedTime (run current start) index + localTime.1)) := by
  have stateEq := ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade.run_run current start index
  have timeEq := congrArg (fun state : GeneratedWholeRestartCurrent nu => state.contact.time.1) stateEq
  have globalInside : localTime.1 ∈ Icc (0 : ℝ) (run current (start + index)).contact.time.1 :=
    ⟨localTime.2.1, localTime.2.2.trans_eq timeEq⟩
  have tailChart := (tail global start).receipt_chart index localTime
  have globalChart := global.receipt_chart (start + index)
    ⟨localTime.1, globalInside⟩
  rw [← elapsedTime_run_add current start index, add_assoc] at globalChart
  rw [tailChart, globalChart]
  exact receipt_read_eq stateEq localTime ⟨localTime.1, globalInside⟩ rfl

theorem tail_path {current : GeneratedWholeRestartCurrent nu}
    (global : GeneratedWholeGlobalPhysicalTrajectory current) (start : ℕ) (time : ℝ) (nonnegative : 0 ≤ time) :
    (tail global start).physicalPath time = global.physicalPath (elapsedTime current start + time) := by
  by_cases atZero : time = 0
  · subst time
    simpa only [add_zero] using tail_path_zero global start
  · have positive : 0 < time := lt_of_le_of_ne nonnegative (Ne.symm atZero)
    obtain ⟨length, covered⟩ := elapsedTime_cofinal (run current start) (tail global start).timeUnbounded time
    obtain ⟨index, location, _⟩ := wholeRestartPhysicalWindow_existsUnique (run current start)
      (length := length) ⟨positive, covered.le⟩
    have before := location.2.2
    rw [elapsedTime_succ] at before
    let localTime : Icc (0 : ℝ) (run (run current start) index).contact.time.1 :=
      ⟨time - elapsedTime (run current start) index, by constructor <;> linarith [location.2.1]⟩
    have same := tail_receipt_chart global start index localTime
    simpa only [localTime, add_sub_cancel] using same

theorem tail_initial_state {current : GeneratedWholeRestartCurrent nu}
    (global : GeneratedWholeGlobalPhysicalTrajectory current) (start : ℕ) :
    (run current start).initialState = global.physicalPath (elapsedTime current start) :=
  (tail global start).initial_eq.symm.trans (tail_path_zero global start)

end
end SaturationMonoid.NavierStokes.NativeGlobalTailOccurrence
