import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Frontier
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Differential.Orientation
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin
open SourceGaussianModel GlobalSource GlobalSource.Differential MeasureTheory Set
open _root_.LAlanineTrueFlowDifferential
noncomputable section

theorem basin_original_change_variables (t : Time) (observable : Point → ℝ) :
    (∫ x in basin, observable x) =
      ∫ x in basin, (responseMatrix x t).det * observable (flow x (spatialStep*(t : ℝ))) := by
  have formula := integral_image_eq_integral_abs_det_fderiv_smul volume basin_measurable
    (fun x _ => (original_flow_strictDerivative x t).hasFDerivAt.hasFDerivWithinAt)
    (flowHomeomorph (spatialStep*(t : ℝ))).injective.injOn observable
  change (∫ x in (flowHomeomorph (spatialStep*(t : ℝ))) '' basin, observable x) = _ at formula
  rw [flow_image_basin] at formula
  rw [formula]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [abs_of_pos (actual_determinant_positive x t)]
  change (flowDerivative x t).det * observable (flow x (spatialStep*(t : ℝ))) = _
  rw [responseMatrix_actual,LinearMap.det_toMatrix']

theorem basin_pullback_integrable (t : Time) (observable : Point → ℝ) (paid : IntegrableOn observable basin) :
    IntegrableOn (fun x => (responseMatrix x t).det * observable (flow x (spatialStep*(t : ℝ)))) basin := by
  have formula := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume basin_measurable
    (fun x _ => (original_flow_strictDerivative x t).hasFDerivAt.hasFDerivWithinAt)
    (flowHomeomorph (spatialStep*(t : ℝ))).injective.injOn observable
  change IntegrableOn observable ((flowHomeomorph (spatialStep*(t : ℝ))) '' basin) ↔ _ at formula
  rw [flow_image_basin] at formula
  have received := formula.mp paid
  convert! received using 1
  funext x
  rw [abs_of_pos (actual_determinant_positive x t)]
  rw [responseMatrix_actual,LinearMap.det_toMatrix']
  rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
