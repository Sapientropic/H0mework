import H0mework.NavierStokes.WholeHistory.WholeHistoryCurl

set_option autoImplicit false
open scoped ContDiff ENNReal

namespace SaturationMonoid.NavierStokes.NativeWholeHistoryCurrent

open PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracExteriorMatterAction StageNineFullDiracAdjointMaterial StageNineCanonicalCauchyState
open Stage9CU.Fluid Stage9CU.Fluid.CurrentReadout
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open NativeFullOrderSynthesis NativeWholeHistoryClock NativeWholeHistoryField
open NativeSourceUnifiedActionSplice (target target_is_original_next)
open MeasureTheory Set

noncomputable section

def matter (point : BasePoint) : DiracExteriorMatterCarrier := NativeCanonicalFluidCoframe.matter (field point)

def dual (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier := NativeCanonicalFluidCoframe.dual (field point)

theorem canonical_pairing (point : BasePoint) : FullDiracAdjointPaired (matter point) (dual point) :=
  NativeCanonicalFluidCoframe.canonical_paired _

theorem spatial_read (direction : Fin 3) :
    current matter dual direction.succ = fun point => field point direction := by
  funext point
  exact InitialLift.spatialCurrent_eq _ direction

theorem temporal_read (point : BasePoint) : current matter dual 0 point = 2 + ‖field point‖ ^ 2 / 8 := by
  rw [current, dual, matter, NativeCanonicalFluidCoframe.dual, NativeCanonicalFluidCoframe.matter,
    InitialLift.temporalCurrent_eq, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

theorem matter_smooth : ContDiff ℝ ∞ (fun point => matterCoordinateEquiv (matter point)) :=
  InitialLift.matter_contDiff field_contDiff

theorem dual_smooth (candidate : DiracExteriorMatterCarrier) : ContDiff ℝ ∞ (fun point => dual point candidate) :=
  InitialLift.dual_contDiff field_contDiff candidate

theorem current_smooth (direction : Fin 4) : ContDiff ℝ ∞ (current matter dual direction) :=
  current_contDiff matter dual matter_smooth (fun _ => dual_smooth _) direction

theorem source_all_order_Lp (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set BasePoint} (compact : IsCompact domain) :
    ∃ bound : ℝ, ∀ direction : Fin 4,
      MemLp (iteratedFDeriv ℝ order (current matter dual direction)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (current matter dual direction)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp matter dual matter_smooth (fun _ => dual_smooth _) order exponent compact

theorem field_on_slice (parameter : ℝ) (space : PhysicalSpace) :
    field (canonicalCauchySlicePoint parameter space) = spatialField (velocity parameter) space := by
  have spatial : NativeFinitePrefixTimeChart.spatialRead (canonicalCauchySlicePoint parameter space) = space := by
    apply PiLp.ext
    intro direction
    exact canonicalCauchySlicePoint_spatial parameter space direction
  have temporal : canonicalCauchySlicePoint parameter space 0 = parameter :=
    canonicalCauchySlicePoint_time parameter space
  rw [field, temporal, spatial]

theorem field_hasDerivAt (parameter : ℝ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => field (canonicalCauchySlicePoint sample space))
      (clockRate parameter • spatialField (NativeWholeHistoryAction.momentum parameter) space) parameter := by
  simp only [field_on_slice]
  exact NativeWholeHistoryAction.physical_velocity_hasDerivAt parameter space

theorem spatial_current_hasDerivAt (parameter : ℝ) (space : PhysicalSpace) (direction : Fin 3) :
    HasDerivAt (fun sample => current matter dual direction.succ (canonicalCauchySlicePoint sample space))
      ((clockRate parameter • spatialField (NativeWholeHistoryAction.momentum parameter) space) direction) parameter := by
  rw [spatial_read]
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) direction).hasFDerivAt.comp_hasDerivAt parameter
    (field_hasDerivAt parameter space)

theorem temporal_current_hasDerivAt (parameter : ℝ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => current matter dual 0 (canonicalCauchySlicePoint sample space))
      (inner ℝ (field (canonicalCauchySlicePoint parameter space))
        (clockRate parameter • spatialField (NativeWholeHistoryAction.momentum parameter) space) / 4) parameter := by
  simp only [temporal_read]
  convert! ((field_hasDerivAt parameter space).norm_sq.div_const 8).const_add 2 using 1
  ring

theorem target_initial_current (index : ℕ) (space : PhysicalSpace) (direction : Fin 3) :
    current matter dual direction.succ (sourcePoint (duration index) space) =
      spatialField (wholeBiotSavartVelocityState (target index).initialState) space direction := by
  rw [spatial_read, target_is_original_next]
  exact congrArg (fun value : PhysicalSpace => value direction) (contact_read index space)

theorem target_contact_current (index : ℕ) (space : PhysicalSpace) (direction : Fin 3) :
    current matter dual direction.succ (sourcePoint (duration (index + 1)) space) =
      spatialField (wholeBiotSavartVelocityState (target index).contact.physicalState) space direction := by
  rw [spatial_read, target_is_original_next]
  exact congrArg (fun value : PhysicalSpace => value direction) (next_contact_read index space)

end
end SaturationMonoid.NavierStokes.NativeWholeHistoryCurrent
