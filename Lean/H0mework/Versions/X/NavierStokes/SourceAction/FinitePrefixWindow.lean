import H0mework.Versions.X.NavierStokes.SourceAction.ReceiptProfile
import H0mework.NavierStokes.WholeReceipt.PrefixReceipt
import H0mework.NavierStokes.Restart.GlobalPhysicalTrajectory

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeFinitePrefixUnifiedWindow

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderNext NativeReceiptTimeProfile

noncomputable section

variable {nu : Viscosity}

theorem prefix_reads_receipt (initial : GeneratedWholeRestartCurrent nu) (length : ℕ)
    (time : Icc (0 : ℝ) (WholePrefixState.duration initial length)) :
    ∃ index < length + 1, ∃ localTime : Icc (0 : ℝ) (run initial index).duration,
      (WholePrefixReceipt.receipt initial length).wholePath time = (run initial index).receipt.wholePath localTime := by
  by_cases atZero : time.1 = 0
  · refine ⟨0, Nat.zero_lt_succ _, ⟨0, le_rfl, (run initial 0).receipt.requestedTimePos.le⟩, ?_⟩
    have pointZero : time = ⟨0, le_rfl, (WholePrefixState.duration_pos initial length).le⟩ := Subtype.ext atZero
    rw [pointZero, (WholePrefixReceipt.receipt initial length).wholePath_initial,
      (run initial 0).receipt.wholePath_initial]
    rfl
  · have positive : 0 < time.1 := lt_of_le_of_ne time.2.1 (Ne.symm atZero)
    obtain ⟨index, indexSpec, _⟩ := wholeRestartPhysicalWindow_existsUnique initial
      (length := length + 1) ⟨positive, time.2.2⟩
    have localNonnegative : 0 ≤ time.1 - elapsedTime initial index := sub_nonneg.mpr indexSpec.2.1.le
    have localLe : time.1 - elapsedTime initial index ≤ (run initial index).contact.time.1 := by
      have endpoint := indexSpec.2.2
      rw [elapsedTime_succ] at endpoint
      linarith
    refine ⟨index, indexSpec.1, ⟨time.1 - elapsedTime initial index, localNonnegative,
      localLe.trans (run initial index).contact.time.2.2⟩, ?_⟩
    rw [WholePrefixReceipt.receipt_path,
      wholeRestartPrefixPhysicalTrajectory_eq_receipt initial indexSpec.1 indexSpec.2,
      wholeRestartReceiptPhysicalTrajectory, projIcc_of_mem _ ⟨localNonnegative, localLe⟩]
    rfl

def budget (length order : ℕ) : ℝ := ∑ index ∈ Finset.range (length + 1), runMomentBudget order index

theorem runBudget_nonnegative (order index : ℕ) : 0 ≤ runMomentBudget order index :=
  (tsum_nonneg (momentDensity_nonneg order (run stackedShortCurrent index).contact.physicalState)).trans
    (run_contact_moment_control order index).2

theorem prefix_moment_control (length order : ℕ)
    (time : Icc (0 : ℝ) (WholePrefixState.duration stackedShortCurrent length)) :
    Summable (momentDensity order ((WholePrefixReceipt.receipt stackedShortCurrent length).wholePath time)) ∧
      moment order ((WholePrefixReceipt.receipt stackedShortCurrent length).wholePath time) ≤ budget length order := by
  obtain ⟨index, indexLt, localTime, same⟩ := prefix_reads_receipt stackedShortCurrent length time
  rw [same]
  have paid := run_receipt_moment_control order index localTime
  exact ⟨paid.1, paid.2.trans (Finset.single_le_sum (fun actual _ => runBudget_nonnegative order actual)
    (Finset.mem_range.mpr indexLt))⟩

def window (length : ℕ) : Window (WholePrefixReceipt.receipt stackedShortCurrent length) where
  first := 0
  last := WholePrefixState.duration stackedShortCurrent length
  first_nonnegative := le_rfl
  ordered := WholePrefixState.duration_pos stackedShortCurrent length
  last_le := le_rfl
  budget := budget length
  paid order time _ := (prefix_moment_control length order time).1
  bound order time _ := (prefix_moment_control length order time).2

def chartTime (initial : GeneratedWholeRestartCurrent nu) (length index : ℕ) (included : index ≤ length)
    (localTime : Icc (0 : ℝ) (run initial index).contact.time.1) :
    Icc (0 : ℝ) (WholePrefixState.duration initial length) :=
  ⟨elapsedTime initial index + localTime.1, add_nonneg (elapsedTime_nonneg initial index) localTime.2.1, by
    have endpoint := add_le_add (le_refl (elapsedTime initial index)) localTime.2.2
    rw [← elapsedTime_succ] at endpoint
    exact endpoint.trans ((elapsedTime_strictMono initial).monotone (Nat.add_le_add_right included 1))⟩

theorem closed_receipt_chart (initial : GeneratedWholeRestartCurrent nu) (length index : ℕ) (included : index ≤ length)
    (localTime : Icc (0 : ℝ) (run initial index).contact.time.1) :
    (WholePrefixReceipt.receipt initial length).wholePath (chartTime initial length index included localTime) =
      (run initial index).receipt.wholePath ⟨localTime.1, localTime.2.1,
        localTime.2.2.trans (run initial index).contact.time.2.2⟩ := by
  rw [WholePrefixReceipt.receipt_path]
  change wholeRestartPrefixPhysicalTrajectory initial (length + 1) (elapsedTime initial index + localTime.1) = _
  by_cases atZero : localTime.1 = 0
  · have localZero : localTime = ⟨0, le_rfl, (run initial index).contact.time_pos.le⟩ := Subtype.ext atZero
    subst localTime
    dsimp only
    rw [add_zero,
      wholeRestartPrefixPhysicalTrajectory_eq_of_le initial (Nat.le_succ_of_le included) le_rfl,
      wholeRestartPrefixPhysicalTrajectory_endpoint]
    exact (run initial index).receipt.wholePath_initial.symm
  · have positive : 0 < localTime.1 := lt_of_le_of_ne localTime.2.1 (Ne.symm atZero)
    have physical : elapsedTime initial index + localTime.1 ∈
        Ioc (elapsedTime initial index) (elapsedTime initial (index + 1)) := by
      rw [elapsedTime_succ]
      exact ⟨lt_add_of_pos_right _ positive, add_le_add le_rfl localTime.2.2⟩
    rw [wholeRestartPrefixPhysicalTrajectory_eq_receipt initial (Nat.lt_succ_of_le included) physical,
      wholeRestartReceiptPhysicalTrajectory, add_sub_cancel_left,
      projIcc_of_mem _ localTime.2]
    rfl

theorem contact_interior (initial : GeneratedWholeRestartCurrent nu) (length index : ℕ) (included : index < length) :
    elapsedTime initial (index + 1) ∈ Ioo (0 : ℝ) (WholePrefixState.duration initial length) :=
  ⟨by simpa only [elapsedTime_zero] using elapsedTime_strictMono initial (Nat.zero_lt_succ index),
    elapsedTime_strictMono initial (Nat.add_lt_add_right included 1)⟩

theorem contact_read (index : ℕ) :
    (WholePrefixReceipt.receipt stackedShortCurrent (index + 2)).wholePath
      (chartTime stackedShortCurrent (index + 2) index (by omega)
        ⟨(run stackedShortCurrent index).contact.time.1, (run stackedShortCurrent index).contact.time_pos.le, le_rfl⟩) =
      (run stackedShortCurrent index).contact.physicalState :=
  closed_receipt_chart stackedShortCurrent (index + 2) index (by omega) _

theorem next_receipt_chart (index : ℕ)
    (localTime : Icc (0 : ℝ) (run stackedShortCurrent index).nextContact.time.1) :
    (WholePrefixReceipt.receipt stackedShortCurrent (index + 2)).wholePath
      (chartTime stackedShortCurrent (index + 2) (index + 1) (by omega) localTime) =
      (run stackedShortCurrent index).nextReceipt.wholePath
        ⟨localTime.1, localTime.2.1, localTime.2.2.trans (run stackedShortCurrent index).nextContact.time.2.2⟩ :=
  closed_receipt_chart stackedShortCurrent (index + 2) (index + 1) (by omega) localTime

end
end SaturationMonoid.NavierStokes.NativeFinitePrefixUnifiedWindow
