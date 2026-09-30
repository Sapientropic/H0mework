import H0mework.NavierStokes.WholeReceipt.PrefixReceipt
import H0mework.NavierStokes.Restart.GlobalPhysicalTrajectory
import H0mework.NavierStokes.Restart.CompleteSerrinLanding

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.WholeGlobalReceipt

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCompleteSerrinLanding
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}

private def cover (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial) (time : Real) : Nat :=
  wholeRestartGlobalCoverIndex initial trajectory.timeUnbounded time

private theorem cover_bound (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial) (time : Real) :
    time ≤ WholePrefixState.duration initial (cover trajectory time) :=
  (wholeRestartGlobalCoverIndex_spec initial trajectory.timeUnbounded time).le.trans
    ((elapsedTime_strictMono initial).monotone (Nat.le_succ _))

/-- The original global physical run generates standard receipts on every finite horizon. -/
def ofTrajectory (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial) :
    StandardGlobalWholeMildSerrinSolutionAt nu initial.initialState where
  receiptAt time positive := restrictWholeContinuousMildSerrinReceipt positive
    (cover_bound trajectory time) (WholePrefixReceipt.receipt initial (cover trajectory time))

theorem ofTrajectory_path (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial)
    (time : Real) (positive : 0 < time) (point : Icc (0 : Real) time) :
    ((ofTrajectory trajectory).receiptAt time positive).wholePath point =
      trajectory.physicalPath point.1 := by
  change wholeRestartPrefixPhysicalTrajectory initial (cover trajectory time + 1) point.1 = _
  exact (trajectory.prefix_eq (cover trajectory time + 1)
    ⟨point.2.1, point.2.2.trans (cover_bound trajectory time)⟩).symm

theorem standardGlobal_nonempty_iff_unbounded :
    Nonempty (StandardGlobalWholeMildSerrinSolutionAt nu initial.initialState) ↔
      ¬ BddAbove (range (elapsedTime initial)) := by
  constructor
  · rintro ⟨solution⟩ bounded
    exact (elapsedTime_bddAbove_standardGlobalWholeMildSerrinSolutionAt_isEmpty initial bounded).false
      solution
  · intro unbounded
    exact ⟨ofTrajectory (generatedWholeGlobalPhysicalTrajectory_of_unbounded initial unbounded)⟩

end
end SaturationMonoid.NavierStokes.WholeGlobalReceipt
