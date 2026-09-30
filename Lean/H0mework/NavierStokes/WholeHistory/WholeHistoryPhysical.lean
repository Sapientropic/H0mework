import H0mework.NavierStokes.WholeHistory.WholeHistoryCurrent

set_option autoImplicit false
open scoped ContDiff Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeWholeHistoryPhysical

open PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9CU
open Fluid.CurrentReadout NativeWholeHistoryCurrent NativeWholeHistoryField
open NativeFullOrderSynthesis
open NativeFinitePrefixTimeChart (spatialRead)
open ThreeDimensionalPeriodicCoarseFilterCore MeasureTheory Set

noncomputable section

def physicalDomain : Set BasePoint := {point | point 0 ∈ NativeWholeHistoryClock.physicalDomain}

def pullback (point : BasePoint) : BasePoint := sourcePoint (point 0) (spatialRead point)

def physicalCurrent (direction : Fin 4) : BasePoint → ℝ := current matter dual direction ∘ pullback

def physicalVorticity : BasePoint → PhysicalSpace := Fluid.curl field ∘ pullback

theorem pullback_contDiffAt (point : BasePoint) (inside : point ∈ physicalDomain) :
    ContDiffAt ℝ ∞ pullback point := by
  have coordinate : ContDiffAt ℝ ∞ (fun sample : BasePoint => sample 0) point := (contDiff_piLp_apply 2).contDiffAt
  have fraction : ContDiffAt ℝ ∞ (fun sample : BasePoint => NativeWholeHistoryClock.fraction (sample 0)) point :=
    coordinate.div (contDiffAt_const.add coordinate) (by linarith [inside.1])
  have ratio := fraction.div_const NativeWholeHistoryClock.ceiling
  have ratioPositive : 0 < NativeWholeHistoryClock.fraction (point 0) / NativeWholeHistoryClock.ceiling :=
    div_pos (NativeWholeHistoryClock.fraction_pos inside.1) NativeWholeHistoryClock.ceiling_pos
  have argumentPositive : 0 < (NativeWholeHistoryClock.fraction (point 0) / NativeWholeHistoryClock.ceiling)⁻¹ - 1 := by
    rw [sub_pos, one_lt_inv_iff₀]
    exact ⟨ratioPositive, (div_lt_one NativeWholeHistoryClock.ceiling_pos).mpr inside.2⟩
  have time := (((ratio.inv ratioPositive.ne').sub contDiffAt_const).log argumentPositive.ne').neg
  apply (contDiffAt_piLp 2).mpr
  intro direction
  refine Fin.cases ?_ (fun _ => ?_) direction
  · exact time
  · exact (contDiff_piLp_apply 2).contDiffAt

theorem current_contDiffAt (direction : Fin 4) (point : BasePoint) (inside : point ∈ physicalDomain) :
    ContDiffAt ℝ ∞ (physicalCurrent direction) point :=
  (current_smooth direction).contDiffAt.comp point (pullback_contDiffAt point inside)

theorem vorticity_contDiffAt (point : BasePoint) (inside : point ∈ physicalDomain) :
    ContDiffAt ℝ ∞ physicalVorticity point :=
  (Fluid.curl_contDiff field_contDiff).contDiffAt.comp point (pullback_contDiffAt point inside)

theorem spatial_original (length : ℕ) (point : BasePoint)
    (inside : point 0 ∈ Ioc (0 : ℝ) (NativeWholeHistoryClock.duration length)) (direction : Fin 3) :
    physicalCurrent direction.succ point =
      NativeReceiptSpacetime.field (receipt length) (point 0, spatialRead point) direction := by
  change current matter dual direction.succ (sourcePoint (point 0) (spatialRead point)) = _
  rw [spatial_read]
  exact congrArg (fun value : PhysicalSpace => value direction) (physical_read length (point 0) inside (spatialRead point))

theorem vorticity_original (length : ℕ) (point : BasePoint)
    (inside : point 0 ∈ Ioc (0 : ℝ) (NativeWholeHistoryClock.duration length)) :
    physicalVorticity point = spatialField
      (NativeReceiptSpacetime.state (receipt length) (point 0)) (spatialRead point) := by
  have domain := NativeWholeHistoryClock.physicalDomain_of_le_duration length (point 0) inside.1 inside.2
  have before : NativeWholeHistoryClock.physicalTime (NativeWholeHistoryClock.inverseTime (point 0)) ≤
      NativeWholeHistoryClock.duration length := by
    rw [NativeWholeHistoryClock.physicalTime_inverse _ domain]
    exact inside.2
  change Fluid.curl field (sourcePoint (point 0) (spatialRead point)) = _
  rw [NativeWholeHistoryCurl.unified_curl_original, sourcePoint_time, sourcePoint_space,
    vorticity_read length _ before, NativeWholeHistoryClock.physicalTime_inverse _ domain]

theorem source_current_all_order_Lp (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set BasePoint} (compact : IsCompact domain) (contained : domain ⊆ physicalDomain) :
    ∃ bound : ℝ, ∀ direction : Fin 4,
      MemLp (iteratedFDeriv ℝ order (physicalCurrent direction)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (physicalCurrent direction)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  let jets (point : BasePoint) : Fin 4 →
      ContinuousMultilinearMap ℝ (fun _ : Fin order => BasePoint) ℝ :=
    fun direction => iteratedFDeriv ℝ order (physicalCurrent direction) point
  have continuousAt (point : BasePoint) (inside : point ∈ domain) : ContinuousAt jets point :=
    continuousAt_pi.mpr fun direction =>
      (current_contDiffAt direction point (contained inside)).continuousAt_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
  have continuity : ContinuousOn jets domain := fun point inside => (continuousAt point inside).continuousWithinAt
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuity
  refine ⟨bound, fun direction => ?_⟩
  have component : ContinuousOn (iteratedFDeriv ℝ order (physicalCurrent direction)) domain :=
    fun point inside => ((current_contDiffAt direction point (contained inside)).continuousAt_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt
  have paid : ∀ᵐ point ∂volume.restrict domain,
      ‖iteratedFDeriv ℝ order (physicalCurrent direction) point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact (norm_le_pi_norm (jets point) direction).trans (bounded point inside)
  exact ⟨MemLp.of_bound (component.aestronglyMeasurable compact.measurableSet) bound paid,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) paid⟩

theorem source_vorticity_all_order_Lp (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set BasePoint} (compact : IsCompact domain) (contained : domain ⊆ physicalDomain) :
    ∃ bound : ℝ,
      MemLp (iteratedFDeriv ℝ order physicalVorticity) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order physicalVorticity) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have continuity : ContinuousOn (iteratedFDeriv ℝ order physicalVorticity) domain := fun point inside =>
    ((vorticity_contDiffAt point (contained inside)).continuousAt_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuity
  have paid : ∀ᵐ point ∂volume.restrict domain, ‖iteratedFDeriv ℝ order physicalVorticity point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact bounded point inside
  exact ⟨bound, MemLp.of_bound (continuity.aestronglyMeasurable compact.measurableSet) bound paid,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) paid⟩

end
end SaturationMonoid.NavierStokes.NativeWholeHistoryPhysical
