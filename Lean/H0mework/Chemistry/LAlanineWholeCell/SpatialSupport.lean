import H0mework.Chemistry.LAlanineWholeCell.SpatialIntegral
import H0mework.Chemistry.LAlanineSourceMatrix.MatrixFinalConsumer
import H0mework.Chemistry.LAlanineGradient.Bounds

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellSpatial

open SourceGaussianModel SourceSignedEvaluator SourceFiniteData ContinuousGradient
open WholeCellPartition WholeCellReplay ContinuousParameterMap Set MeasureTheory

noncomputable section

theorem all_source_boxes_in_cube : ∀ f : WholeCellSource.Field, ∀ axis : Fin 3,
    boxCentre axis - boxRadius ≤ (WholeCellSource.box f axis).1 ∧
      (WholeCellSource.box f axis).2 ≤ boxCentre axis + boxRadius := by decide +kernel

theorem source_box_subset_cube (f : WholeCellSource.Field) (x : Point)
    (inside : InRectangle (WholeCellSource.box f) x) : x ∈ sourceCube := by
  intro axis
  apply abs_le.mpr
  have lower : (boxCentre axis : ℝ) - (boxRadius : ℝ) ≤ ((WholeCellSource.box f axis).1 : ℝ) := by
    exact_mod_cast (all_source_boxes_in_cube f axis).1
  have upper : ((WholeCellSource.box f axis).2 : ℝ) ≤ (boxCentre axis : ℝ) + (boxRadius : ℝ) := by
    exact_mod_cast (all_source_boxes_in_cube f axis).2
  have bounds := inside axis
  constructor <;> linarith [bounds.1, bounds.2]

theorem fullPatch_subset_sourceCube (fields : SourceFieldLaw) : fullPatch ⊆ sourceCube := by
  rintro x ⟨p, hp, rfl⟩
  rw [fullDomain_eq_iUnion_quarters] at hp
  obtain ⟨q, hq⟩ := mem_iUnion.mp hp
  exact source_box_subset_cube (finalField q) _ (generated_target_in_final_field fields q p hq)

theorem old_parameter_domain_subset : SourceCellGeometry.cellDomain ⊆ fullDomain := by
  have bounds : ∀ axis : Fin 3, fullLowerQ axis ≤ SourceCellGeometry.cellLowerQ axis ∧
      SourceCellGeometry.cellUpperQ axis ≤ fullUpperQ axis := by decide +kernel
  intro p hp
  exact ⟨fun axis => (Rat.cast_le.mpr (bounds axis).1).trans (hp.1 axis),
    fun axis => (hp.2 axis).trans (Rat.cast_le.mpr (bounds axis).2)⟩

theorem old_spatial_patch_subset : SourceChart.spatialPatch ⊆ fullPatch :=
  image_mono old_parameter_domain_subset

theorem fullPatch_volume_positive : 0 < volume fullPatch :=
  SourceFieldMatrices.actual_spatial_volume_positive.trans_le (measure_mono old_spatial_patch_subset)

theorem fullPatch_volume_finite : volume fullPatch < ⊤ := fullPatch_compact.measure_lt_top

end
end LAlanine40K2025.BasinRefinement.WholeCellSpatial
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
