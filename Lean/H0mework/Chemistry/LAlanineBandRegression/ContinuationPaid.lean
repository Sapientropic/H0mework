import H0mework.Chemistry.LAlanineBandContinuation.Images
import H0mework.Chemistry.LAlanineBandRegression.ContinuationCell0
import H0mework.Chemistry.LAlanineBandSource.Certified
import H0mework.Chemistry.LAlanineWholeBandCell0.CrossNoFold

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuation

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap WholeBandSource WholeBandGeometry
open WholeBandTransverse TrueFlowGeometry TrueFlowDifferential WholeBandCrossGeometry Set
noncomputable section

theorem cell0_positive_reports : PositiveNormalReports 0 := by
  intro d i
  exact (by norm_num : (0 : ℚ) < 1/20).trans (all_cell0_normal_lower d i).2

theorem cell16_source_fields : ∀ d, DirectionFields 16 d := by
  intro d i role x inside
  cases role
  · change FieldHolds (recordedCallField (initialCallAt 16 d i)) x
    rw [cell16_initialCallAt, cell16_recordedCallField]
    apply TrueTubeWholeMatrix.all_actual_call_fields _ x
    change InRectangle (callBox (initialCallAt 16 d i)) x at inside
    simpa only [cell16_initialCallAt, cell16_callBox] using inside
  · change FieldHolds (recordedCallField (tubeCallAt 16 d i)) x
    rw [cell16_tubeCallAt, cell16_recordedCallField]
    apply TrueTubeWholeMatrix.all_actual_call_fields _ x
    change InRectangle (callBox (tubeCallAt 16 d i)) x at inside
    simpa only [cell16_tubeCallAt, cell16_callBox] using inside

theorem cell16_positive_reports : PositiveNormalReports 16 := by
  intro d i
  rw [cell16_tubeCallAt, normalLower, cell16_recordedCallField]
  exact all_calls_transverse _

theorem cell0_same_actual_map : sourceParameterMap 0 = WholeBandCell0Geometry.cell0ParameterMap := rfl

theorem cell16_same_actual_map : sourceParameterMap 16 = trueParameterMap := rfl

theorem paid_pair_parameter_classification (p q : Point)
    (hp : p ∈ cellDomain 0) (hq : q ∈ cellDomain 16) :
    WholeBandCell0Geometry.cell0ParameterMap p = trueParameterMap q ↔ p = q :=
  actual_parameter_meeting 0 16 cell0_source_fields cell16_source_fields
    cell0_positive_reports cell16_positive_reports p q hp hq

theorem paid_pair_intersection_exact :
    (WholeBandCell0Geometry.cell0ParameterMap '' cellDomain 0) ∩ truePatch =
      WholeBandCell0Geometry.cell0ParameterMap '' (cellDomain 0 ∩ cellDomain 16) := by
  simpa only [cell0_same_actual_map, cell16_same_actual_map, cell16_domain_is_original, truePatch] using
    actual_images_intersection 0 16 cell0_source_fields cell16_source_fields
      cell0_positive_reports cell16_positive_reports

theorem paid_pair_disjoint_recovered : type_of% cell0_cell16_actual_images_disjoint := by
  apply Set.disjoint_iff_inter_eq_empty.mpr
  rw [paid_pair_intersection_exact]
  have empty : cellDomain 0 ∩ cellDomain 16 = (∅ : Set Point) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p inside
    have gap : (cellV 0 1 : ℝ) < cellV 16 0 := Rat.cast_lt.mpr cell0_cell16_source_separation
    exact (not_lt_of_ge (inside.2.2.1.1.trans inside.1.2.1.2)) gap
  rw [empty, image_empty]

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
