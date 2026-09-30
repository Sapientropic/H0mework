import H0mework.NavierStokes.WholeHistory.WholeHistoryClock
import H0mework.NavierStokes.PhysicalJets.VorticityAction

set_option autoImplicit false
open scoped Topology ContDiff

namespace SaturationMonoid.NavierStokes.NativeWholeHistoryField

open Set Filter
open PhysicsCore.ProofFreeRicherAnholonomicSource
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeWholeHistoryClock NativeFullOrderSynthesis NativeSpacetimeControl
open NativeReceiptTimeProfile

noncomputable section

def receipt (length : ℕ) := WholePrefixReceipt.receipt stackedShortCurrent length

def window (length : ℕ) : Window (receipt length) := NativeFinitePrefixUnifiedWindow.window length

theorem path_agrees (first last : ℕ) (actual : ℝ)
    (inFirst : actual ∈ Icc (0 : ℝ) (duration first)) (inLast : actual ∈ Icc (0 : ℝ) (duration last)) :
    (receipt first).wholePath ⟨actual, inFirst⟩ = (receipt last).wholePath ⟨actual, inLast⟩ := by
  rw [receipt, receipt, WholePrefixReceipt.receipt_path, WholePrefixReceipt.receipt_path]
  rcases le_total first last with ordered | ordered
  · exact (wholeRestartPrefixPhysicalTrajectory_eq_of_le stackedShortCurrent (Nat.add_le_add_right ordered 1) inFirst.2).symm
  · exact wholeRestartPrefixPhysicalTrajectory_eq_of_le stackedShortCurrent (Nat.add_le_add_right ordered 1) inLast.2

theorem velocity_agrees (first last : ℕ) (actual : ℝ)
    (inFirst : actual ∈ Icc (0 : ℝ) (duration first)) (inLast : actual ∈ Icc (0 : ℝ) (duration last)) :
    NativeReceiptSpacetime.velocity (receipt first) actual = NativeReceiptSpacetime.velocity (receipt last) actual := by
  unfold NativeReceiptSpacetime.velocity
  rw [NativeReceiptSpacetime.state_on_interval (receipt first) ⟨actual, inFirst⟩,
    NativeReceiptSpacetime.state_on_interval (receipt last) ⟨actual, inLast⟩,
    path_agrees first last actual inFirst inLast]

def velocity (parameter : ℝ) : ComplexVorticityHilbertState :=
  NativeReceiptSpacetime.velocity (receipt (cover parameter)) (physicalTime parameter)

def vorticity (parameter : ℝ) : ComplexVorticityHilbertState :=
  NativeReceiptSpacetime.state (receipt (cover parameter)) (physicalTime parameter)

theorem velocity_read (length : ℕ) (parameter : ℝ) (before : physicalTime parameter ≤ duration length) :
    velocity parameter = NativeReceiptSpacetime.velocity (receipt length) (physicalTime parameter) :=
  velocity_agrees (cover parameter) length (physicalTime parameter)
    ⟨(physicalTime_pos parameter).le, (cover_spec parameter).le⟩ ⟨(physicalTime_pos parameter).le, before⟩

theorem vorticity_read (length : ℕ) (parameter : ℝ) (before : physicalTime parameter ≤ duration length) :
    vorticity parameter = NativeReceiptSpacetime.state (receipt length) (physicalTime parameter) := by
  unfold vorticity
  rw [NativeReceiptSpacetime.state_on_interval (receipt (cover parameter))
      ⟨physicalTime parameter, (physicalTime_pos parameter).le, (cover_spec parameter).le⟩,
    NativeReceiptSpacetime.state_on_interval (receipt length)
      ⟨physicalTime parameter, (physicalTime_pos parameter).le, before⟩]
  exact path_agrees _ _ _ _ _

def spacetime (point : BasePoint) : Spacetime :=
  (physicalTime (point 0), NativeFinitePrefixTimeChart.spatialRead point)

theorem spacetime_contDiff : ContDiff ℝ ∞ spacetime :=
  (physicalTime_contDiff.comp (contDiff_piLp_apply 2)).prodMk NativeFinitePrefixTimeChart.spatialRead_contDiff

def field (point : BasePoint) : PhysicalSpace :=
  spatialField (velocity (point 0)) (NativeFinitePrefixTimeChart.spatialRead point)

theorem field_read (length : ℕ) (point : BasePoint) (before : physicalTime (point 0) ≤ duration length) :
    field point = NativeReceiptSpacetime.field (receipt length) (spacetime point) := by
  unfold field
  rw [velocity_read length (point 0) before]
  rfl

theorem field_locally (point : BasePoint) : ∀ᶠ sample in 𝓝 point,
    field sample = NativeReceiptSpacetime.field (receipt (cover (point 0))) (spacetime sample) := by
  have clock : Continuous (fun sample : BasePoint => physicalTime (sample 0)) :=
    (physicalTime_contDiff.comp (contDiff_piLp_apply 2)).continuous
  filter_upwards [clock.tendsto point (Iio_mem_nhds (cover_spec (point 0)))] with sample before
  exact field_read _ sample before.le

theorem field_contDiff : ContDiff ℝ ∞ field := by
  apply contDiff_iff_contDiffAt.mpr
  intro point
  let length := cover (point 0)
  have nearby : NativeReceiptSpacetime.slab (window length) ∈ 𝓝 (spacetime point) := by
    apply Filter.mem_of_superset ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (show spacetime point ∈ Ioo (0 : ℝ) (duration length) ×ˢ (univ : Set PhysicalSpace) from
        ⟨⟨physicalTime_pos (point 0), cover_spec (point 0)⟩, trivial⟩))
    intro sample member
    exact ⟨⟨member.1.1.le, member.1.2.le⟩, trivial⟩
  have original := (NativeReceiptSpacetime.field_contDiffOn (window length)).contDiffAt nearby
  have composed := original.comp point spacetime_contDiff.contDiffAt
  exact composed.congr_of_eventuallyEq (field_locally point)

def sourcePoint (actual : ℝ) (space : PhysicalSpace) : BasePoint :=
  WithLp.toLp 2 (Fin.cases (inverseTime actual) (fun direction => space direction))

theorem sourcePoint_time (actual : ℝ) (space : PhysicalSpace) : sourcePoint actual space 0 = inverseTime actual := rfl

theorem sourcePoint_space (actual : ℝ) (space : PhysicalSpace) :
    NativeFinitePrefixTimeChart.spatialRead (sourcePoint actual space) = space := by
  apply PiLp.ext
  intro direction
  rfl

theorem physical_read (length : ℕ) (actual : ℝ) (inside : actual ∈ Ioc (0 : ℝ) (duration length))
    (space : PhysicalSpace) :
    field (sourcePoint actual space) =
      NativeReceiptSpacetime.field (receipt length) (actual, space) := by
  have domain := physicalDomain_of_le_duration length actual inside.1 inside.2
  have before : physicalTime ((sourcePoint actual space) 0) ≤ duration length := by
    rw [sourcePoint_time, physicalTime_inverse actual domain]
    exact inside.2
  rw [field_read length _ before]
  unfold spacetime
  rw [sourcePoint_time, physicalTime_inverse actual domain, sourcePoint_space]

theorem contact_read (index : ℕ) (space : PhysicalSpace) :
    field (sourcePoint (duration index) space) =
      spatialField (ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget.wholeBiotSavartVelocityState
        (run stackedShortCurrent index).contact.physicalState) space := by
  rw [physical_read (index + 2) _
    ⟨duration_pos index, (duration_strictMono.monotone (Nat.le_add_right index 2))⟩]
  unfold NativeReceiptSpacetime.field NativeReceiptSpacetime.velocity
  rw [NativeReceiptSpacetime.state_on_interval (receipt (index + 2))
    ⟨duration index, (duration_pos index).le, duration_strictMono.monotone (Nat.le_add_right index 2)⟩]
  have original := NativeFinitePrefixTimeChart.contact_state index
  change (receipt (index + 2)).wholePath _ = (run stackedShortCurrent index).contact.physicalState at original
  exact congrArg (fun state : ComplexVorticityHilbertState => spatialField
    (ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget.wholeBiotSavartVelocityState state) space) original

theorem next_contact_read (index : ℕ) (space : PhysicalSpace) :
    field (sourcePoint (NativeWholeHistoryClock.duration (index + 1)) space) =
      spatialField (ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget.wholeBiotSavartVelocityState
        (run stackedShortCurrent index).next.contact.physicalState) space :=
  contact_read (index + 1) space

end
end SaturationMonoid.NavierStokes.NativeWholeHistoryField
