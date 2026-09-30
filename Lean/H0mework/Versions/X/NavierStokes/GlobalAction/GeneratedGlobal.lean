import H0mework.Versions.X.NavierStokes.SourceAction.ReceiptProfile
import H0mework.NavierStokes.WholeReceipt.Global

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeGeneratedGlobalControl

open Set Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open NativeFullOrderNext NativeFullOrderEvolution NativeReceiptTimeProfile

noncomputable section

variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}

def runBudget (initialWindow : Window initial.receipt) (order : ℕ) : ℕ → ℝ
  | 0 => initialWindow.budget order
  | index + 1 => runBudget initialWindow order index *
      Real.exp (wordRate order nu * wholeRestartVelocityCeiling (run initial index).contact)

theorem contact_control (initialWindow : Window initial.receipt)
    (firstZero : initialWindow.first = 0) (lastFull : initialWindow.last = initial.duration) (order index : ℕ) :
    Summable (momentDensity order (run initial index).contact.physicalState) ∧
      moment order (run initial index).contact.physicalState ≤ runBudget initialWindow order index := by
  induction index with
  | zero =>
      have inside : initial.contact.time.1 ∈ Icc initialWindow.first initialWindow.last := by
        rw [firstZero, lastFull]
        exact initial.contact.time.2
      exact ⟨initialWindow.paid order initial.contact.time inside, initialWindow.bound order initial.contact.time inside⟩
  | succ index prior =>
      have actual := nextReceipt_moment_control (run initial index) order prior.1 (run initial index).nextContact.time
      exact ⟨actual.1, actual.2.trans (mul_le_mul_of_nonneg_right prior.2 (Real.exp_pos _).le)⟩

theorem receipt_control (initialWindow : Window initial.receipt)
    (firstZero : initialWindow.first = 0) (lastFull : initialWindow.last = initial.duration) (order index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).duration) :
    Summable (momentDensity order ((run initial index).receipt.wholePath time)) ∧
      moment order ((run initial index).receipt.wholePath time) ≤ runBudget initialWindow order index := by
  cases index with
  | zero =>
      have inside : time.1 ∈ Icc initialWindow.first initialWindow.last := by
        rw [firstZero, lastFull]
        exact time.2
      exact ⟨initialWindow.paid order time inside, initialWindow.bound order time inside⟩
  | succ index =>
      have prior := contact_control initialWindow firstZero lastFull order index
      have actual := nextReceipt_moment_control (run initial index) order prior.1 time
      exact ⟨actual.1, actual.2.trans (mul_le_mul_of_nonneg_right prior.2 (Real.exp_pos _).le)⟩

def cover (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial) (horizon : ℝ) : ℕ :=
  wholeRestartGlobalCoverIndex initial trajectory.timeUnbounded horizon

theorem cover_spec (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial) (horizon : ℝ) :
    horizon < elapsedTime initial (cover trajectory horizon) :=
  wholeRestartGlobalCoverIndex_spec initial trajectory.timeUnbounded horizon

theorem reads_original_receipt (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial) (horizon : ℝ)
    (time : Icc (0 : ℝ) horizon) :
    ∃ index < cover trajectory horizon + 1, ∃ localTime : Icc (0 : ℝ) (run initial index).duration,
      trajectory.physicalPath time.1 = (run initial index).receipt.wholePath localTime := by
  by_cases atZero : time.1 = 0
  · refine ⟨0, Nat.zero_lt_succ _, ⟨0, le_rfl, (run initial 0).receipt.requestedTimePos.le⟩, ?_⟩
    rw [atZero, trajectory.initial_eq, (run initial 0).receipt.wholePath_initial]
    rfl
  · have positive : 0 < time.1 := lt_of_le_of_ne time.2.1 (Ne.symm atZero)
    obtain ⟨index, indexSpec, _⟩ := wholeRestartPhysicalWindow_existsUnique initial
      (length := cover trajectory horizon) ⟨positive, time.2.2.trans (cover_spec trajectory horizon).le⟩
    have localNonnegative : 0 ≤ time.1 - elapsedTime initial index := sub_nonneg.mpr indexSpec.2.1.le
    have localLe : time.1 - elapsedTime initial index ≤ (run initial index).contact.time.1 := by
      have endpoint := indexSpec.2.2
      rw [elapsedTime_succ] at endpoint
      linarith
    let localTime : Icc (0 : ℝ) (run initial index).contact.time.1 :=
      ⟨time.1 - elapsedTime initial index, localNonnegative, localLe⟩
    refine ⟨index, indexSpec.1.trans (Nat.lt_succ_self _),
      ⟨localTime.1, localTime.2.1, localTime.2.2.trans (run initial index).contact.time.2.2⟩, ?_⟩
    have chart := trajectory.receipt_chart index localTime
    change trajectory.physicalPath (elapsedTime initial index + (time.1 - elapsedTime initial index)) = _ at chart
    rw [← add_sub_assoc, add_sub_cancel_left] at chart
    exact chart

def windowBudget (initialWindow : Window initial.receipt) (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial)
    (horizon : ℝ) (order : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (cover trajectory horizon + 1), runBudget initialWindow order index

theorem global_moment_control (initialWindow : Window initial.receipt)
    (firstZero : initialWindow.first = 0) (lastFull : initialWindow.last = initial.duration)
    (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial) (horizon : ℝ) (order : ℕ)
    (time : Icc (0 : ℝ) horizon) :
    Summable (momentDensity order (trajectory.physicalPath time.1)) ∧
      moment order (trajectory.physicalPath time.1) ≤ windowBudget initialWindow trajectory horizon order := by
  obtain ⟨index, indexLt, localTime, same⟩ := reads_original_receipt trajectory horizon time
  rw [same]
  have paid := receipt_control initialWindow firstZero lastFull order index localTime
  refine ⟨paid.1, paid.2.trans ?_⟩
  apply Finset.single_le_sum _ (Finset.mem_range.mpr indexLt)
  intro actual _
  exact (tsum_nonneg (momentDensity_nonneg order (run initial actual).contact.physicalState)).trans
    (contact_control initialWindow firstZero lastFull order actual).2

def globalWindow (initialWindow : Window initial.receipt)
    (firstZero : initialWindow.first = 0) (lastFull : initialWindow.last = initial.duration)
    (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial) (horizon : ℝ) (positive : 0 < horizon) :
    Window ((WholeGlobalReceipt.ofTrajectory trajectory).receiptAt horizon positive) where
  first := 0
  last := horizon
  first_nonnegative := le_rfl
  ordered := positive
  last_le := le_rfl
  budget := windowBudget initialWindow trajectory horizon
  paid order time _ := by
    rw [WholeGlobalReceipt.ofTrajectory_path trajectory horizon positive time]
    exact (global_moment_control initialWindow firstZero lastFull trajectory horizon order time).1
  bound order time _ := by
    rw [WholeGlobalReceipt.ofTrajectory_path trajectory horizon positive time]
    exact (global_moment_control initialWindow firstZero lastFull trajectory horizon order time).2

end
end SaturationMonoid.NavierStokes.NativeGeneratedGlobalControl
