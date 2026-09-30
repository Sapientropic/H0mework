import H0mework.Versions.X.NavierStokes.SourceAction.Next
import H0mework.Versions.X.NavierStokes.SourceAction.Consumer
import H0mework.NavierStokes.WholeReceipt.Global

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeOldGlobalMoments

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderNext NativeFullOrderConsumer NativeFullOrderSynthesis NativePhysicalSource

noncomputable section

abbrev OriginalGlobal := GeneratedWholeGlobalPhysicalTrajectory stackedShortCurrent

def windowIndex (trajectory : OriginalGlobal) (horizon : ℝ) : ℕ :=
  wholeRestartGlobalCoverIndex stackedShortCurrent trajectory.timeUnbounded horizon

def windowMomentBudget (trajectory : OriginalGlobal) (horizon : ℝ) (order : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (windowIndex trajectory horizon + 1), runMomentBudget order index

theorem windowIndex_covers (trajectory : OriginalGlobal) (horizon : ℝ) :
    horizon < elapsedTime stackedShortCurrent (windowIndex trajectory horizon) :=
  wholeRestartGlobalCoverIndex_spec stackedShortCurrent trajectory.timeUnbounded horizon

theorem physicalPath_eq_original (trajectory : OriginalGlobal) (time : ℝ) (nonnegative : 0 ≤ time) :
    trajectory.physicalPath time =
      wholeRestartGlobalPhysicalTrajectory stackedShortCurrent trajectory.timeUnbounded time := by
  have covered := (windowIndex_covers trajectory time).le
  exact (trajectory.prefix_eq (windowIndex trajectory time) ⟨nonnegative, covered⟩).trans
    (wholeRestartGlobalPhysicalTrajectory_eq_prefix stackedShortCurrent trajectory.timeUnbounded
      (windowIndex trajectory time) covered).symm

theorem window_reads_original_receipt (trajectory : OriginalGlobal) (horizon : ℝ)
    (time : Icc (0 : ℝ) horizon) :
    ∃ index < windowIndex trajectory horizon + 1,
      ∃ localTime : Icc (0 : ℝ) (run stackedShortCurrent index).duration,
        trajectory.physicalPath time.1 = (run stackedShortCurrent index).receipt.wholePath localTime := by
  by_cases atZero : time.1 = 0
  · refine ⟨0, Nat.zero_lt_succ _,
      ⟨0, le_rfl, (run stackedShortCurrent 0).receipt.requestedTimePos.le⟩, ?_⟩
    rw [atZero, trajectory.initial_eq, (run stackedShortCurrent 0).receipt.wholePath_initial]
    rfl
  · have positive : 0 < time.1 := lt_of_le_of_ne time.2.1 (Ne.symm atZero)
    obtain ⟨index, indexSpec, _⟩ := wholeRestartPhysicalWindow_existsUnique stackedShortCurrent
      (length := windowIndex trajectory horizon)
      ⟨positive, time.2.2.trans (windowIndex_covers trajectory horizon).le⟩
    have localNonnegative : 0 ≤ time.1 - elapsedTime stackedShortCurrent index :=
      sub_nonneg.mpr indexSpec.2.1.le
    have localLe : time.1 - elapsedTime stackedShortCurrent index ≤
        (run stackedShortCurrent index).contact.time.1 := by
      have endpoint := indexSpec.2.2
      rw [elapsedTime_succ] at endpoint
      linarith
    let localTime : Icc (0 : ℝ) (run stackedShortCurrent index).contact.time.1 :=
      ⟨time.1 - elapsedTime stackedShortCurrent index, localNonnegative, localLe⟩
    refine ⟨index, indexSpec.1.trans (Nat.lt_succ_self _),
      ⟨localTime.1, localTime.2.1, localTime.2.2.trans
        (run stackedShortCurrent index).contact.time.2.2⟩, ?_⟩
    have chart := trajectory.receipt_chart index localTime
    change trajectory.physicalPath
      (elapsedTime stackedShortCurrent index + (time.1 - elapsedTime stackedShortCurrent index)) = _ at chart
    rw [← add_sub_assoc, add_sub_cancel_left] at chart
    exact chart

theorem runMomentBudget_nonnegative (order index : ℕ) : 0 ≤ runMomentBudget order index :=
  (tsum_nonneg (momentDensity_nonneg order (run stackedShortCurrent index).contact.physicalState)).trans
    (run_contact_moment_control order index).2

theorem runMomentBudget_le_window (trajectory : OriginalGlobal) (horizon : ℝ) (order index : ℕ)
    (inside : index < windowIndex trajectory horizon + 1) :
    runMomentBudget order index ≤ windowMomentBudget trajectory horizon order :=
  Finset.single_le_sum (fun actual _ => runMomentBudget_nonnegative order actual)
    (Finset.mem_range.mpr inside)

theorem global_window_moment_control (trajectory : OriginalGlobal) (horizon : ℝ) (order : ℕ)
    (time : Icc (0 : ℝ) horizon) :
    Summable (momentDensity order (trajectory.physicalPath time.1)) ∧
      moment order (trajectory.physicalPath time.1) ≤ windowMomentBudget trajectory horizon order := by
  obtain ⟨index, indexLt, localTime, samePath⟩ := window_reads_original_receipt trajectory horizon time
  rw [samePath]
  have paid := run_receipt_moment_control order index localTime
  refine ⟨paid.1, paid.2.trans ?_⟩
  exact runMomentBudget_le_window trajectory horizon order index indexLt

theorem global_window_momentRegular (trajectory : OriginalGlobal) (horizon : ℝ)
    (time : Icc (0 : ℝ) horizon) : MomentRegular (trajectory.physicalPath time.1) :=
  fun order => (global_window_moment_control trajectory horizon order time).1

theorem finite_global_receipt_moment_control (trajectory : OriginalGlobal) (horizon : ℝ)
    (positive : 0 < horizon) (order : ℕ) (time : Icc (0 : ℝ) horizon) :
    Summable (momentDensity order (((WholeGlobalReceipt.ofTrajectory trajectory).receiptAt horizon positive).wholePath time)) ∧
      moment order (((WholeGlobalReceipt.ofTrajectory trajectory).receiptAt horizon positive).wholePath time) ≤
        windowMomentBudget trajectory horizon order := by
  rw [WholeGlobalReceipt.ofTrajectory_path trajectory horizon positive time]
  exact global_window_moment_control trajectory horizon order time

def windowVelocityJetBudget (trajectory : OriginalGlobal) (horizon : ℝ) (order : ℕ) : ℝ :=
  (2 * Real.pi) ^ order * ((windowMomentBudget trajectory horizon (order + 2) + ∑' wave, decay wave) / 2)

def windowVorticityJetBudget (trajectory : OriginalGlobal) (horizon : ℝ) (order : ℕ) : ℝ :=
  (2 * Real.pi) ^ order *
    (((2 * Real.pi) ^ 2 * windowMomentBudget trajectory horizon (order + 3) + ∑' wave, decay wave) / 2)

theorem global_window_spatial_control (trajectory : OriginalGlobal) (horizon : ℝ)
    (time : Icc (0 : ℝ) horizon) :
    (ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField (wholeBiotSavartVelocityState (trajectory.physicalPath time.1))) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order
        (spatialField (wholeBiotSavartVelocityState (trajectory.physicalPath time.1))) point‖ ≤
          windowVelocityJetBudget trajectory horizon order) ∧
    (ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField (trajectory.physicalPath time.1)) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order (spatialField (trajectory.physicalPath time.1)) point‖ ≤
        windowVorticityJetBudget trajectory horizon order) := by
  obtain ⟨index, indexLt, localTime, samePath⟩ := window_reads_original_receipt trajectory horizon time
  rw [samePath]
  have paid := run_receipt_spatial_control index localTime
  refine ⟨⟨paid.1.1, ?_⟩, ⟨paid.2.1, ?_⟩⟩
  · intro order point
    apply (paid.1.2 order point).trans
    unfold velocityJetBudget windowVelocityJetBudget
    gcongr
    exact runMomentBudget_le_window trajectory horizon (order + 2) index indexLt
  · intro order point
    apply (paid.2.2 order point).trans
    unfold vorticityJetBudget windowVorticityJetBudget
    gcongr
    exact runMomentBudget_le_window trajectory horizon (order + 3) index indexLt

end
end SaturationMonoid.NavierStokes.NativeOldGlobalMoments
