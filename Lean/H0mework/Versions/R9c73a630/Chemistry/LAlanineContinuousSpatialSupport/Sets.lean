import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousSource.SpatialIntegral
import H0mework.Versions.R9c73a630.Chemistry.LAlanineGradient.Bounds

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSpatialSupport

open SourceGaussianModel SourceSignedEvaluator SourceRectangle SourceFiniteData
open SourceRK4Replay SourceCellGeometry SourceChart ContinuousParameterMap ContinuousGradient
open Set MeasureTheory

noncomputable section
attribute [local irreducible] parameterMap

theorem source_radius_exact : sourceRadius = (5764607523034235 / 72057594037927936 : ℝ) := by
  have h : boxRadius = (5764607523034235 / 72057594037927936 : ℚ) := by rfl
  unfold sourceRadius
  rw [h]
  norm_num

theorem final_box_inside_source : ∀ axis : Fin 3,
    boxCentre axis - boxRadius ≤ (actualBox 16 axis).1 ∧
      (actualBox 16 axis).2 ≤ boxCentre axis + boxRadius := by decide +kernel

theorem final_box_subset_sourceCube (x : Point) (inside : InRectangle (actualBox 16) x) :
    x ∈ sourceCube := by
  intro axis
  apply abs_le.mpr
  have lower : ((boxCentre axis : ℝ) - (boxRadius : ℝ)) ≤ ((actualBox 16 axis).1 : ℝ) := by
    exact_mod_cast (final_box_inside_source axis).1
  have upper : ((actualBox 16 axis).2 : ℝ) ≤ (boxCentre axis : ℝ) + (boxRadius : ℝ) := by
    exact_mod_cast (final_box_inside_source axis).2
  have bounds := inside axis
  constructor <;> linarith [bounds.1, bounds.2]

theorem spatialPatch_subset_sourceCube (fields : SourceFieldLaw) : spatialPatch ⊆ sourceCube := by
  rintro x ⟨p, hp, rfl⟩
  exact final_box_subset_sourceCube _ (generated_target_in_final_field fields p hp)

theorem spatialPatch_isCompact : IsCompact spatialPatch :=
  isCompact_Icc.image (parameterMap_contDiff 0 4 0).continuous

theorem spatialPatch_nonempty : spatialPatch.Nonempty := cellDomain_nonempty.image _

theorem spatialPatch_measurable : MeasurableSet spatialPatch := spatialPatch_isCompact.isClosed.measurableSet

theorem spatialPatch_volume_finite : volume spatialPatch < ⊤ := spatialPatch_isCompact.measure_lt_top

theorem spatialPatch_laplacian_integrable :
    IntegrableOn (laplacian sourceTerms densityMatrix) spatialPatch :=
  (laplacian_contDiff sourceTerms densityMatrix 0).continuous.continuousOn.integrableOn_compact
    spatialPatch_isCompact

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSpatialSupport
