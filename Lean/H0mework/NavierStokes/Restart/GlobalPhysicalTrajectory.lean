import H0mework.NavierStokes.Restart.FinitePrefixDualSquareLedger
import H0mework.NavierStokes.Restart.HalfCriticalDualSquareReduction

/-!
# Global physical trajectory of an unbounded whole restart run

Every finite prefix of the native whole restart run is already one continuous
physical path on its exact accumulated time interval.  If the generated
elapsed times are unbounded, these nested prefixes stabilize at every finite
physical time.  This module takes that literal stabilized value and obtains
one global path.

The global path is not supplied by a caller.  On every actual restart window
it is definitionally controlled by the same source-owned unforced whole
receipt which generated that window.  No continuation oracle, target path,
partition, overlap certificate, or cutoff enters the construction.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalDualSquareReduction

noncomputable section

/-! ## Cofinality and stabilization of finite prefixes -/

/-- Unbounded generated elapsed time is cofinal in the physical time axis. -/
theorem elapsedTime_cofinal
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (timeUnbounded :
      ¬ BddAbove (Set.range (elapsedTime initial)))
    (time : ℝ) :
    ∃ length : ℕ, time < elapsedTime initial length := by
  obtain ⟨value, ⟨length, rfl⟩, timeLt⟩ :=
    not_bddAbove_iff.mp timeUnbounded time
  exact ⟨length, timeLt⟩

/-- Adding one more actual receipt does not alter the already written prefix. -/
theorem wholeRestartPrefixPhysicalTrajectory_succ_eq_of_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ)
    {time : ℝ}
    (timeLe : time ≤ elapsedTime initial length) :
    wholeRestartPrefixPhysicalTrajectory initial (length + 1) time =
      wholeRestartPrefixPhysicalTrajectory initial length time := by
  rw [wholeRestartPrefixPhysicalTrajectory]
  exact
    ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice.endpointSplice_of_le
      _ _ _ _ timeLe

/-- The finite physical paths form a nested literal direct system. -/
theorem wholeRestartPrefixPhysicalTrajectory_eq_of_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    {shorter longer : ℕ}
    (indexLe : shorter ≤ longer)
    {time : ℝ}
    (timeLe : time ≤ elapsedTime initial shorter) :
    wholeRestartPrefixPhysicalTrajectory initial longer time =
      wholeRestartPrefixPhysicalTrajectory initial shorter time := by
  induction longer generalizing shorter with
  | zero =>
      have shorterEq : shorter = 0 := by omega
      subst shorter
      rfl
  | succ longer inductionHypothesis =>
      by_cases shorterEq : shorter = longer + 1
      · subst shorter
        rfl
      · have shorterLe : shorter ≤ longer := by omega
        calc
          wholeRestartPrefixPhysicalTrajectory initial (longer + 1) time =
              wholeRestartPrefixPhysicalTrajectory initial longer time :=
            wholeRestartPrefixPhysicalTrajectory_succ_eq_of_le
              initial longer
              (timeLe.trans
                ((elapsedTime_strictMono initial).monotone shorterLe))
          _ = wholeRestartPrefixPhysicalTrajectory initial shorter time :=
            inductionHypothesis shorterLe timeLe

/-! ## The stabilized global path -/

/-- A generated prefix whose physical endpoint lies strictly after `time`. -/
noncomputable def wholeRestartGlobalCoverIndex
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (timeUnbounded :
      ¬ BddAbove (Set.range (elapsedTime initial)))
    (time : ℝ) : ℕ :=
  Classical.choose (elapsedTime_cofinal initial timeUnbounded time)

theorem wholeRestartGlobalCoverIndex_spec
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (timeUnbounded :
      ¬ BddAbove (Set.range (elapsedTime initial)))
    (time : ℝ) :
    time <
      elapsedTime initial
        (wholeRestartGlobalCoverIndex initial timeUnbounded time) :=
  Classical.choose_spec (elapsedTime_cofinal initial timeUnbounded time)

/-- The unique stabilized value of the generated finite-prefix paths. -/
noncomputable def wholeRestartGlobalPhysicalTrajectory
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (timeUnbounded :
      ¬ BddAbove (Set.range (elapsedTime initial)))
    (time : ℝ) : ComplexVorticityHilbertState :=
  wholeRestartPrefixPhysicalTrajectory initial
    (wholeRestartGlobalCoverIndex initial timeUnbounded time) time

/-- On every completed finite physical interval the global path is literally
the already generated finite-prefix path. -/
theorem wholeRestartGlobalPhysicalTrajectory_eq_prefix
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (timeUnbounded :
      ¬ BddAbove (Set.range (elapsedTime initial)))
    (length : ℕ)
    {time : ℝ}
    (timeLe : time ≤ elapsedTime initial length) :
    wholeRestartGlobalPhysicalTrajectory initial timeUnbounded time =
      wholeRestartPrefixPhysicalTrajectory initial length time := by
  let cover :=
    wholeRestartGlobalCoverIndex initial timeUnbounded time
  let upper := max cover length
  have timeLeCover : time ≤ elapsedTime initial cover :=
    (wholeRestartGlobalCoverIndex_spec
      initial timeUnbounded time).le
  calc
    wholeRestartGlobalPhysicalTrajectory initial timeUnbounded time =
        wholeRestartPrefixPhysicalTrajectory initial cover time := rfl
    _ = wholeRestartPrefixPhysicalTrajectory initial upper time :=
      (wholeRestartPrefixPhysicalTrajectory_eq_of_le
        initial (Nat.le_max_left cover length) timeLeCover).symm
    _ = wholeRestartPrefixPhysicalTrajectory initial length time :=
      wholeRestartPrefixPhysicalTrajectory_eq_of_le
        initial (Nat.le_max_right cover length) timeLe

/-- Equality with a finite prefix on its complete closed physical interval. -/
theorem wholeRestartGlobalPhysicalTrajectory_eq_prefix_on_Icc
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (timeUnbounded :
      ¬ BddAbove (Set.range (elapsedTime initial)))
    (length : ℕ) :
    Set.EqOn
      (wholeRestartGlobalPhysicalTrajectory initial timeUnbounded)
      (wholeRestartPrefixPhysicalTrajectory initial length)
      (Icc 0 (elapsedTime initial length)) := by
  intro time timeMem
  exact
    wholeRestartGlobalPhysicalTrajectory_eq_prefix
      initial timeUnbounded length timeMem.2

/-- Every finite physical interval of the global path is continuous. -/
theorem wholeRestartGlobalPhysicalTrajectory_continuousOn_Icc
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (timeUnbounded :
      ¬ BddAbove (Set.range (elapsedTime initial)))
    (length : ℕ) :
    ContinuousOn
      (wholeRestartGlobalPhysicalTrajectory initial timeUnbounded)
      (Icc 0 (elapsedTime initial length)) := by
  apply
    (wholeRestartPrefixPhysicalTrajectory_continuousOn
      initial length).congr
  intro time timeMem
  exact
    wholeRestartGlobalPhysicalTrajectory_eq_prefix
      initial timeUnbounded length timeMem.2

/-! ## Exact actual-receipt charts -/

/-- On an actual half-open native window, the global path is the same
source-owned unforced whole receipt, shifted by its generated elapsed time. -/
theorem wholeRestartGlobalPhysicalTrajectory_eq_receipt_on_window
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (timeUnbounded :
      ¬ BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    {time : ℝ}
    (timeMem : time ∈ wholeRestartPhysicalWindow initial index) :
    wholeRestartGlobalPhysicalTrajectory initial timeUnbounded time =
      wholeRestartReceiptPhysicalTrajectory
        (run initial index).contact.prefixReceipt
        (time - elapsedTime initial index) := by
  rw [wholeRestartGlobalPhysicalTrajectory_eq_prefix
    initial timeUnbounded (index + 1) timeMem.2]
  exact
    wholeRestartPrefixPhysicalTrajectory_eq_receipt
      initial (Nat.lt_succ_self index) timeMem

/-- The closed local-time chart of every actual receipt is retained by the
single global path, including both adjacent endpoints. -/
theorem wholeRestartGlobalPhysicalTrajectory_eq_receipt_chart
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (timeUnbounded :
      ¬ BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (localTime : ℝ)
    (localTimeMem :
      localTime ∈
        Icc 0 (run initial index).contact.time.1) :
    wholeRestartGlobalPhysicalTrajectory initial timeUnbounded
        (elapsedTime initial index + localTime) =
      wholeRestartReceiptPhysicalTrajectory
        (run initial index).contact.prefixReceipt localTime := by
  by_cases localTimeZero : localTime = 0
  · subst localTime
    rw [add_zero,
      wholeRestartGlobalPhysicalTrajectory_eq_prefix
        initial timeUnbounded index le_rfl,
      wholeRestartPrefixPhysicalTrajectory_endpoint,
      wholeRestartReceiptPhysicalTrajectory_zero]
  · have localTimePos : 0 < localTime :=
      lt_of_le_of_ne localTimeMem.1 (Ne.symm localTimeZero)
    have globalTimeMem :
        elapsedTime initial index + localTime ∈
          wholeRestartPhysicalWindow initial index := by
      constructor
      · linarith
      · rw [elapsedTime_succ]
        linarith [localTimeMem.2]
    simpa using
      (wholeRestartGlobalPhysicalTrajectory_eq_receipt_on_window
        initial timeUnbounded index globalTimeMem)

/-- Typed receipt form of the exact closed chart equality. -/
theorem wholeRestartGlobalPhysicalTrajectory_eq_receipt_wholePath
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (timeUnbounded :
      ¬ BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (localTime :
      Icc 0 (run initial index).contact.time.1) :
    wholeRestartGlobalPhysicalTrajectory initial timeUnbounded
        (elapsedTime initial index + localTime.1) =
      (run initial index).contact.prefixReceipt.wholePath localTime := by
  rw [wholeRestartGlobalPhysicalTrajectory_eq_receipt_chart
    initial timeUnbounded index localTime.1 localTime.2]
  unfold wholeRestartReceiptPhysicalTrajectory
  rw [projIcc_of_mem
    (run initial index).contact.prefixReceipt.requestedTimePos.le
    localTime.2]

/-! ## Source-generated global trajectory object and hard-gate exhaustion -/

/-- One global physical trajectory generated by an unbounded native restart
run.  Its path, every finite prefix, and every local unforced receipt remain
bound to the same authoritative run. -/
structure GeneratedWholeGlobalPhysicalTrajectory
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) where
  timeUnbounded :
    ¬ BddAbove (Set.range (elapsedTime initial))
  physicalPath : ℝ → ComplexVorticityHilbertState
  initial_eq : physicalPath 0 = initial.initialState
  prefix_eq :
    ∀ length : ℕ,
      Set.EqOn physicalPath
        (wholeRestartPrefixPhysicalTrajectory initial length)
        (Icc 0 (elapsedTime initial length))
  continuousOn_prefix :
    ∀ length : ℕ,
      ContinuousOn physicalPath
        (Icc 0 (elapsedTime initial length))
  receipt_chart :
    ∀ (index : ℕ)
      (localTime :
        Icc 0 (run initial index).contact.time.1),
      physicalPath
          (elapsedTime initial index + localTime.1) =
        (run initial index).contact.prefixReceipt.wholePath localTime

/-- An unbounded actual restart run generates its single global trajectory;
the target path is not supplied to the theorem. -/
noncomputable def generatedWholeGlobalPhysicalTrajectory_of_unbounded
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (timeUnbounded :
      ¬ BddAbove (Set.range (elapsedTime initial))) :
    GeneratedWholeGlobalPhysicalTrajectory initial where
  timeUnbounded := timeUnbounded
  physicalPath :=
    wholeRestartGlobalPhysicalTrajectory initial timeUnbounded
  initial_eq := by
    rw [wholeRestartGlobalPhysicalTrajectory_eq_prefix
      (time := (0 : ℝ)) initial timeUnbounded 0 (by simp)]
    rfl
  prefix_eq :=
    wholeRestartGlobalPhysicalTrajectory_eq_prefix_on_Icc
      initial timeUnbounded
  continuousOn_prefix :=
    wholeRestartGlobalPhysicalTrajectory_continuousOn_Icc
      initial timeUnbounded
  receipt_chart :=
    wholeRestartGlobalPhysicalTrajectory_eq_receipt_wholePath
      initial timeUnbounded

/-- The native run itself exhausts the global hard gate: finite accumulated
time produces an actual half-critical crossing, while unbounded accumulated
time produces the global actual unforced trajectory.  No continuation branch
is present. -/
noncomputable def
    generatedWholeRestart_halfCriticalCrossing_or_globalPhysicalTrajectory
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    PLift (∃ index : ℕ,
      wholeRestartHalfCriticalCrossed initial index) ⊕
      GeneratedWholeGlobalPhysicalTrajectory initial := by
  by_cases elapsedBounded :
      BddAbove (Set.range (elapsedTime initial))
  · exact Sum.inl
      ⟨elapsedTime_bddAbove_forces_halfCriticalCrossing
        initial elapsedBounded⟩
  · exact Sum.inr
      (generatedWholeGlobalPhysicalTrajectory_of_unbounded
        initial elapsedBounded)

/-- Initial half-critical control excludes every crossing and therefore
generates the global physical trajectory itself. -/
noncomputable def
    generatedWholeGlobalPhysicalTrajectory_of_initial_halfCriticalMargin
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (initialMargin :
      criticalEnstrophyLatticeConstant *
          wholeVorticityEuclideanMass initial.contact.physicalState ≤
        (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    GeneratedWholeGlobalPhysicalTrajectory initial :=
  generatedWholeGlobalPhysicalTrajectory_of_unbounded initial
    (elapsedTime_not_bddAbove_of_initial_halfCriticalMargin
      initial initialMargin)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
end NavierStokes
end SaturationMonoid
