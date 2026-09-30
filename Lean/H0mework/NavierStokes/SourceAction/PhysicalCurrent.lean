import H0mework.NavierStokes.SourceAction.CurrentAction

set_option autoImplicit false
open scoped ContDiff ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeCurrentPhysicalReadout

open PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9CU.Fluid.CurrentReadout NativeSourceCurrentReadout
open NativeFinitePrefixTimeChart NativeFullOrderSynthesis
open ThreeDimensionalPeriodicCoarseFilterCore MeasureTheory Set

noncomputable section

def physicalDomain (index : ℕ) : Set BasePoint :=
  {point | point 0 ∈ Ioo (0 : ℝ) (duration index)}

def pullback (index : ℕ) (point : BasePoint) : BasePoint :=
  sourcePoint index (point 0) (spatialRead point)

def physicalCurrent (index : ℕ) (direction : Fin 4) : BasePoint → ℝ :=
  current (matter index) (dual index) direction ∘ pullback index

theorem pullback_contDiffAt (index : ℕ) (point : BasePoint) (inside : point ∈ physicalDomain index) :
    ContDiffAt ℝ ∞ (pullback index) point := by
  have ratio : ContDiffAt ℝ ∞ (fun sample : BasePoint => sample 0 / duration index) point :=
    (contDiff_piLp_apply 2).contDiffAt.div_const _
  have ratioPositive : 0 < point 0 / duration index := div_pos inside.1 (duration_pos index)
  have argumentPositive : 0 < (point 0 / duration index)⁻¹ - 1 := by
    rw [sub_pos, one_lt_inv_iff₀]
    exact ⟨ratioPositive, (div_lt_one (duration_pos index)).mpr inside.2⟩
  have time := (((ratio.inv ratioPositive.ne').sub contDiffAt_const).log argumentPositive.ne').neg
  apply (contDiffAt_piLp 2).mpr
  intro direction
  refine Fin.cases ?_ (fun _ => ?_) direction
  · exact time
  · exact (contDiff_piLp_apply 2).contDiffAt

theorem physicalCurrent_contDiffAt (index : ℕ) (direction : Fin 4) (point : BasePoint)
    (inside : point ∈ physicalDomain index) : ContDiffAt ℝ ∞ (physicalCurrent index direction) point :=
  (current_contDiff (matter index) (dual index) (matter_smooth index) (fun _ => dual_smooth index _) direction).contDiffAt.comp
    point (pullback_contDiffAt index point inside)

theorem physical_spatial_read (index : ℕ) (direction : Fin 3) (point : BasePoint)
    (inside : point ∈ physicalDomain index) :
    physicalCurrent index direction.succ point =
      spatialField (NativeReceiptSpacetime.velocity (NativeFinitePrefixTimeChart.receipt index) (point 0))
        (spatialRead point) direction := by
  change current (matter index) (dual index) direction.succ (sourcePoint index (point 0) (spatialRead point)) = _
  rw [spatial_read]
  have original := field_original_read index (point 0) inside (spatialRead point)
  have state := NativeReceiptSpacetime.state_on_interval (NativeFinitePrefixTimeChart.receipt index)
    ⟨point 0, inside.1.le, inside.2.le⟩
  change NativeReceiptSpacetime.state (NativeFinitePrefixTimeChart.receipt index) (point 0) = _ at state
  change NativeFinitePrefixTimeChart.field index (sourcePoint index (point 0) (spatialRead point)) direction = _
  rw [original, NativeReceiptSpacetime.velocity, state]

theorem physical_all_order_Lp (index order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set BasePoint} (compact : IsCompact domain) (contained : domain ⊆ physicalDomain index) :
    ∃ bound : ℝ, ∀ direction : Fin 4,
      MemLp (iteratedFDeriv ℝ order (physicalCurrent index direction)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (physicalCurrent index direction)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  let jets (point : BasePoint) : Fin 4 →
      ContinuousMultilinearMap ℝ (fun _ : Fin order => BasePoint) ℝ :=
    fun direction => iteratedFDeriv ℝ order (physicalCurrent index direction) point
  have continuousAt (point : BasePoint) (inside : point ∈ domain) : ContinuousAt jets point :=
    continuousAt_pi.mpr fun direction =>
      (physicalCurrent_contDiffAt index direction point (contained inside)).continuousAt_iteratedFDeriv
        (WithTop.coe_le_coe.mpr le_top)
  have continuity : ContinuousOn jets domain := fun point inside => (continuousAt point inside).continuousWithinAt
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuity
  refine ⟨bound, fun direction => ?_⟩
  have component : ContinuousOn (iteratedFDeriv ℝ order (physicalCurrent index direction)) domain :=
    fun point inside => ((physicalCurrent_contDiffAt index direction point (contained inside)).continuousAt_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt
  have paid : ∀ᵐ point ∂volume.restrict domain,
      ‖iteratedFDeriv ℝ order (physicalCurrent index direction) point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact (norm_le_pi_norm (jets point) direction).trans (bounded point inside)
  exact ⟨MemLp.of_bound (component.aestronglyMeasurable compact.measurableSet) bound paid,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) paid⟩

end
end SaturationMonoid.NavierStokes.NativeCurrentPhysicalReadout
