import H0mework.Versions.X.NavierStokes.SourceAction.CurrentReadout
import H0mework.Versions.X.NavierStokes.SourceAction.ChartPhysicalAction

set_option autoImplicit false
open scoped ContDiff ENNReal

namespace SaturationMonoid.NavierStokes.NativeSourceCurrentAction

open PhysicsCore StageNineCanonicalCauchyState StageNineHolonomicField
open ProofFreeRicherAnholonomicSource Stage9CU.Fluid.CurrentReadout
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeFullOrderSynthesis NativeSourceCurrentReadout

noncomputable section

theorem field_on_slice (index : ℕ) (parameter : ℝ) (space : PhysicalSpace) :
    NativeFinitePrefixTimeChart.field index (canonicalCauchySlicePoint parameter space) =
      spatialField (NativeFinitePrefixTimeChart.velocity index parameter) space := by
  have spatial : NativeFinitePrefixTimeChart.spatialRead (canonicalCauchySlicePoint parameter space) = space := by
    apply PiLp.ext
    intro direction
    exact canonicalCauchySlicePoint_spatial parameter space direction
  have time : canonicalCauchySlicePoint parameter space 0 = parameter :=
    canonicalCauchySlicePoint_time parameter space
  unfold NativeFinitePrefixTimeChart.field NativeFinitePrefixTimeChart.spacetime
  rw [time, spatial]
  rfl

def tangent (index : ℕ) (parameter : ℝ) (space : PhysicalSpace) : PhysicalSpace :=
  spatialField (NativeFinitePrefixTimeChart.velocityRate index parameter) space

theorem field_hasDerivAt (index : ℕ) (parameter : ℝ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => NativeFinitePrefixTimeChart.field index (canonicalCauchySlicePoint sample space))
      (tangent index parameter space) parameter := by
  simp only [field_on_slice]
  exact NativeTimeChartPhysicalAction.source_physical_hasDerivAt index parameter space

theorem spatial_current_hasDerivAt (index : ℕ) (parameter : ℝ) (space : PhysicalSpace) (direction : Fin 3) :
    HasDerivAt (fun sample => current (matter index) (dual index) direction.succ
      (canonicalCauchySlicePoint sample space)) (tangent index parameter space direction) parameter := by
  rw [spatial_read]
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) direction).hasFDerivAt.comp_hasDerivAt parameter
    (field_hasDerivAt index parameter space)

theorem temporal_current_hasDerivAt (index : ℕ) (parameter : ℝ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => current (matter index) (dual index) 0 (canonicalCauchySlicePoint sample space))
      (inner ℝ (NativeFinitePrefixTimeChart.field index (canonicalCauchySlicePoint parameter space))
        (tangent index parameter space) / 4) parameter := by
  simp only [temporal_read]
  convert! ((field_hasDerivAt index parameter space).norm_sq.div_const 8).const_add 2 using 1
  ring

theorem matter_hasDerivAt (index : ℕ) (parameter : ℝ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => matterCoordinateEquiv (matter index (canonicalCauchySlicePoint sample space)))
      (NativeMaterialReadback.materialIncrement (tangent index parameter space)) parameter := by
  have actual := (NativeMaterialReadback.materialIncrement.hasFDerivAt.comp_hasDerivAt parameter
    (field_hasDerivAt index parameter space)).const_add
      (matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter 0))
  have read : (fun sample => matterCoordinateEquiv (matter index (canonicalCauchySlicePoint sample space))) =
      fun sample => matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter 0) +
        NativeMaterialReadback.materialIncrement
          (NativeFinitePrefixTimeChart.field index (canonicalCauchySlicePoint sample space)) := by
    funext sample
    exact NativeMaterialDifferential.source_coordinate_eq _
  rw [read]
  exact actual

theorem source_action_unscale (index : ℕ) (parameter : ℝ) (space : PhysicalSpace) :
    (NativeFinitePrefixTimeChart.clockRate index parameter)⁻¹ • tangent index parameter space =
      spatialField (NativeReceiptSpacetime.timeJet (NativeFinitePrefixTimeChart.window index) 1
        (NativeFinitePrefixTimeChart.physicalTime index parameter)) space := by
  unfold tangent NativeFinitePrefixTimeChart.velocityRate
  rw [NativeTimeChartPhysicalAction.spatialField_real_smul, smul_smul,
    inv_mul_cancel₀ (NativeFinitePrefixTimeChart.clockRate_pos index parameter).ne', one_smul]

theorem source_phase_hasDerivAt (index : ℕ) (parameter : ℝ) (space : PhysicalSpace) (direction : Fin 3) :
    HasDerivAt (fun sample => NativeCanonicalFluidCoframe.phaseMomentum
      (NativeFinitePrefixTimeChart.field index (canonicalCauchySlicePoint sample space)) direction.succ)
      (-tangent index parameter space direction) parameter := by
  simp only [NativeCanonicalFluidCoframe.phaseMomentum_spatial]
  exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) direction).hasFDerivAt.comp_hasDerivAt parameter
    (field_hasDerivAt index parameter space)).neg

end
end SaturationMonoid.NavierStokes.NativeSourceCurrentAction
