import H0mework.Physics.LowEnergy.PacketPairResponse.Band
import Mathlib.MeasureTheory.Measure.Restrict

/-! The physical momentum band carries the restriction of three-dimensional Lebesgue measure, without normalizing away its volume. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
open FullQuantum FullSpace
noncomputable section

theorem band_compact : IsCompact {momentum : Position | ‖momentum‖ ≤ bandRadius} := by
  simpa only [Metric.closedBall,dist_zero_right] using isCompact_closedBall (0 : Position) bandRadius

instance lightBand_compactSpace : CompactSpace LightBand := isCompact_iff_compactSpace.mp band_compact

theorem band_measurable : MeasurableSet {momentum : Position | ‖momentum‖ ≤ bandRadius} :=
  band_compact.measurableSet

def bandMeasure : Measure LightBand := volume.comap (fun point : LightBand => point.val)

theorem bandMeasure_univ : bandMeasure Set.univ=volume {momentum : Position | ‖momentum‖ ≤ bandRadius} := by
  exact (comap_subtype_coe_apply band_measurable volume Set.univ).trans
    (by rw [Set.image_univ,Subtype.range_coe])

instance bandMeasure_finite : IsFiniteMeasure bandMeasure :=
  ⟨by rw [bandMeasure_univ]; exact band_compact.measure_lt_top⟩

theorem bandMeasure_map : bandMeasure.map (fun point : LightBand => point.val)=
    volume.restrict {momentum : Position | ‖momentum‖ ≤ bandRadius} :=
  map_comap_subtype_coe band_measurable volume

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
