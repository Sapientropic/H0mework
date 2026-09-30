import H0mework.Physics.Fluid.CurrentReadout
import H0mework.NavierStokes.SourceAction.FinitePrefixChart
import H0mework.NavierStokes.MaterialReadback.Differential

set_option autoImplicit false
open scoped ContDiff ENNReal

namespace SaturationMonoid.NavierStokes.NativeSourceCurrentReadout

open PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracExteriorMatterAction StageNineFullDiracAdjointMaterial
open Stage9CU.Fluid Stage9CU.Fluid.CurrentReadout
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderSynthesis MeasureTheory Set

noncomputable section

def matter (index : ℕ) (point : BasePoint) : DiracExteriorMatterCarrier :=
  NativeCanonicalFluidCoframe.matter (NativeFinitePrefixTimeChart.field index point)

def dual (index : ℕ) (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  NativeCanonicalFluidCoframe.dual (NativeFinitePrefixTimeChart.field index point)

theorem canonical_pairing (index : ℕ) (point : BasePoint) :
    FullDiracAdjointPaired (matter index point) (dual index point) :=
  NativeCanonicalFluidCoframe.canonical_paired _

theorem spatial_read (index : ℕ) (direction : Fin 3) :
    current (matter index) (dual index) direction.succ =
      fun point => NativeFinitePrefixTimeChart.field index point direction := by
  funext point
  exact InitialLift.spatialCurrent_eq _ direction

theorem temporal_read (index : ℕ) (point : BasePoint) :
    current (matter index) (dual index) 0 point =
      2 + ‖NativeFinitePrefixTimeChart.field index point‖ ^ 2 / 8 := by
  rw [current, dual, matter, NativeCanonicalFluidCoframe.dual, NativeCanonicalFluidCoframe.matter,
    InitialLift.temporalCurrent_eq, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

theorem matter_smooth (index : ℕ) :
    ContDiff ℝ ∞ (fun point => matterCoordinateEquiv (matter index point)) :=
  InitialLift.matter_contDiff (NativeFinitePrefixTimeChart.field_contDiff index)

theorem dual_smooth (index : ℕ) (candidate : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (fun point => dual index point candidate) :=
  InitialLift.dual_contDiff (NativeFinitePrefixTimeChart.field_contDiff index) candidate

theorem source_all_order_control (index order : ℕ)
    {domain : Set BasePoint} (compact : IsCompact domain) :
    ∃ bound : ℝ, ∀ direction : Fin 4, ∀ point ∈ domain,
      ‖iteratedFDeriv ℝ order (current (matter index) (dual index) direction) point‖ ≤ bound :=
  compact_all_order_control (matter index) (dual index) (matter_smooth index)
    (fun _ => dual_smooth index _) order compact

theorem source_all_order_Lp (index order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set BasePoint} (compact : IsCompact domain) :
    ∃ bound : ℝ, ∀ direction : Fin 4,
      MemLp (iteratedFDeriv ℝ order (current (matter index) (dual index) direction))
        exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (current (matter index) (dual index) direction))
        exponent (volume.restrict domain) ≤
          ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp (matter index) (dual index) (matter_smooth index)
    (fun _ => dual_smooth index _) order exponent compact

theorem source_spatial_jets (index order : ℕ) (direction : Fin 3) (point : BasePoint) :
    iteratedFDeriv ℝ order (current (matter index) (dual index) direction.succ) point =
      iteratedFDeriv ℝ order (fun actual => NativeFinitePrefixTimeChart.field index actual direction) point := by
  rw [spatial_read]

theorem contact_read (index : ℕ) (space : PhysicalSpace) (direction : Fin 3) :
    current (matter index) (dual index) direction.succ
      (NativeFinitePrefixTimeChart.sourcePoint index (NativeFinitePrefixTimeChart.contactTime index) space) =
        spatialField (wholeBiotSavartVelocityState (run stackedShortCurrent index).contact.physicalState)
          space direction := by
  rw [spatial_read]
  exact congrArg (fun value : PhysicalSpace => value direction) (NativeFinitePrefixTimeChart.contact_read index space)

theorem next_contact_read (index : ℕ) (space : PhysicalSpace) (direction : Fin 3) :
    current (matter index) (dual index) direction.succ
      (NativeFinitePrefixTimeChart.sourcePoint index (NativeFinitePrefixTimeChart.nextContactTime index) space) =
        spatialField (wholeBiotSavartVelocityState (run stackedShortCurrent index).next.contact.physicalState)
          space direction := by
  rw [spatial_read]
  exact congrArg (fun value : PhysicalSpace => value direction) (NativeFinitePrefixTimeChart.next_contact_read index space)

end
end SaturationMonoid.NavierStokes.NativeSourceCurrentReadout
