import H0mework.NavierStokes.GlobalAction.GeneratedGlobal
import H0mework.NavierStokes.SourceAction.ReceiptSpacetime
import H0mework.NavierStokes.GlobalAction.GlobalSpacetime

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeGeneratedGlobalSpacetime

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open NativeGeneratedGlobalControl NativeReceiptTimeProfile NativeFullOrderSynthesis NativeSpacetimeControl

noncomputable section

variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}

abbrev halfspace : Set Spacetime := NativeOldGlobalSpacetime.halfspace

def field (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial) (pair : Spacetime) : PhysicalSpace :=
  spatialField (wholeBiotSavartVelocityState (trajectory.physicalPath pair.1)) pair.2

def vorticityField (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial) (pair : Spacetime) : PhysicalSpace :=
  spatialField (trajectory.physicalPath pair.1) pair.2

def correctionField (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial)
    (modes : Finset IntegerWavevector) (pair : Spacetime) : PhysicalSpace :=
  nativeTurbulenceCorrectionField modes (trajectory.physicalPath pair.1) pair.2

theorem state_reads_original (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial)
    (horizon : ℝ) (positive : 0 < horizon) (time : Icc (0 : ℝ) horizon) :
    NativeReceiptSpacetime.state ((WholeGlobalReceipt.ofTrajectory trajectory).receiptAt horizon positive) time.1 =
      trajectory.physicalPath time.1 := by
  rw [NativeReceiptSpacetime.state_on_interval, WholeGlobalReceipt.ofTrajectory_path]

theorem window_spacetime_control (initialWindow : Window initial.receipt)
    (firstZero : initialWindow.first = 0) (lastFull : initialWindow.last = initial.duration)
    (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial) (horizon : ℝ) (positive : 0 < horizon)
    (modes : Finset IntegerWavevector) :
    let support : Set Spacetime := Icc (0 : ℝ) horizon ×ˢ univ
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field trajectory) support ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (vorticityField trajectory) support ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (correctionField trajectory modes) support := by
  let window := globalWindow initialWindow firstZero lastFull trajectory horizon positive
  refine ⟨(NativeReceiptSpacetime.field_contDiffOn window).congr ?_,
    (NativeReceiptSpacetime.vorticityField_contDiffOn window).congr ?_,
    (NativeReceiptSpacetime.correctionField_contDiffOn window modes).congr ?_⟩
  · intro pair inside
    change spatialField (wholeBiotSavartVelocityState (trajectory.physicalPath pair.1)) pair.2 =
      spatialField (wholeBiotSavartVelocityState (NativeReceiptSpacetime.state
        ((WholeGlobalReceipt.ofTrajectory trajectory).receiptAt horizon positive) pair.1)) pair.2
    rw [state_reads_original trajectory horizon positive ⟨pair.1, inside.1⟩]
  · intro pair inside
    change spatialField (trajectory.physicalPath pair.1) pair.2 = spatialField (NativeReceiptSpacetime.state
      ((WholeGlobalReceipt.ofTrajectory trajectory).receiptAt horizon positive) pair.1) pair.2
    rw [state_reads_original trajectory horizon positive ⟨pair.1, inside.1⟩]
  · intro pair inside
    change nativeTurbulenceCorrectionField modes (trajectory.physicalPath pair.1) pair.2 =
      nativeTurbulenceCorrectionField modes (NativeReceiptSpacetime.state
        ((WholeGlobalReceipt.ofTrajectory trajectory).receiptAt horizon positive) pair.1) pair.2
    rw [state_reads_original trajectory horizon positive ⟨pair.1, inside.1⟩]

theorem smooth_on_halfspace_of_windows (observation : Spacetime → PhysicalSpace)
    (windows : ∀ horizon : ℝ, 0 < horizon →
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) observation (Icc (0 : ℝ) horizon ×ˢ univ)) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) observation halfspace := by
  intro pair inside
  have positive : 0 < pair.1 + 1 := by have lower : 0 ≤ pair.1 := inside.1; linarith
  have nearby := windows (pair.1 + 1) positive pair ⟨⟨inside.1, by linarith⟩, trivial⟩
  apply nearby.mono_of_mem_nhdsWithin
  have upper : ∀ᶠ sample : Spacetime in 𝓝 pair, sample.1 < pair.1 + 1 :=
    (continuous_fst.tendsto pair) (Iio_mem_nhds (by linarith : pair.1 < pair.1 + 1))
  filter_upwards [upper.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with sample below member
  exact ⟨⟨member.1, below.le⟩, trivial⟩

theorem global_spacetime_control (initialWindow : Window initial.receipt)
    (firstZero : initialWindow.first = 0) (lastFull : initialWindow.last = initial.duration)
    (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial) (modes : Finset IntegerWavevector) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field trajectory) halfspace ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (vorticityField trajectory) halfspace ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (correctionField trajectory modes) halfspace :=
  ⟨smooth_on_halfspace_of_windows _ (fun horizon positive =>
      (window_spacetime_control initialWindow firstZero lastFull trajectory horizon positive modes).1),
    smooth_on_halfspace_of_windows _ (fun horizon positive =>
      (window_spacetime_control initialWindow firstZero lastFull trajectory horizon positive modes).2.1),
    smooth_on_halfspace_of_windows _ (fun horizon positive =>
      (window_spacetime_control initialWindow firstZero lastFull trajectory horizon positive modes).2.2)⟩

theorem global_all_order_Lp (initialWindow : Window initial.receipt)
    (firstZero : initialWindow.first = 0) (lastFull : initialWindow.last = initial.duration)
    (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial) (modes : Finset IntegerWavevector)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain)
    (contained : domain ⊆ halfspace) :
    ∀ observation ∈ ({field trajectory, vorticityField trajectory, correctionField trajectory modes} :
        Set (Spacetime → PhysicalSpace)),
      ∃ budget : ℝ, 0 ≤ budget ∧
        MemLp (iteratedFDerivWithin ℝ order observation halfspace) exponent (volume.restrict domain) ∧
        eLpNorm (iteratedFDerivWithin ℝ order observation halfspace) exponent (volume.restrict domain) ≤
          ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) := by
  intro observation member
  have source := global_spacetime_control initialWindow firstZero lastFull trajectory modes
  have smooth : ContDiffOn ℝ (↑(⊤ : ℕ∞)) observation halfspace := by
    simp only [mem_insert_iff, mem_singleton_iff] at member
    rcases member with rfl | rfl | rfl
    · exact source.1
    · exact source.2.1
    · exact source.2.2
  exact NativeRecoveryTimeJets.spacetime_frechet_Lp_of_smooth _ _ smooth
    NativeOldGlobalSpacetime.halfspace_unique order exponent compact contained

end
end SaturationMonoid.NavierStokes.NativeGeneratedGlobalSpacetime
