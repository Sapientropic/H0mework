import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.Derivative
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentFlow

open SourceGaussianModel WholeBandGeometry WholeBandContinuationParameter Set MeasureTheory Filter
open scoped ENNReal
noncomputable section

def jointImage : Set Point := jointMap '' jointDomain

theorem jointImage_compact : IsCompact jointImage :=
  joint_domain_compact.image_of_continuousOn jointMap_continuousOn

theorem jointImage_measurable : MeasurableSet jointImage := jointImage_compact.isClosed.measurableSet
theorem jointImage_nonempty : jointImage.Nonempty := joint_source_nonempty.image jointMap
theorem jointImage_volume_lt_top : volume jointImage < ⊤ := jointImage_compact.measure_lt_top

theorem jointImage_eq_union : jointImage =
    WholeBandContinuation.sourceParameterMap 0 '' cellDomain 0 ∪
      WholeBandContinuation.sourceParameterMap 1 '' cellDomain 1 := image_union _ _ _

theorem joint_spatial_integral_commutes (g : Point → ℝ) :
    (∫ x in jointImage, g x) =
      ∫ p in jointDomain, |(jointJacobian p).det| • g (jointMap p) :=
  integral_image_eq_integral_abs_det_fderiv_smul volume joint_domain_measurable
    (fun p _ => jointMap_hasFDerivWithinAt p) jointMap_injOn g

theorem joint_spatial_integrable_iff (g : Point → ℝ) :
    IntegrableOn g jointImage ↔
      IntegrableOn (fun p => |(jointJacobian p).det| • g (jointMap p)) jointDomain :=
  integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume joint_domain_measurable
    (fun p _ => jointMap_hasFDerivWithinAt p) jointMap_injOn g

theorem joint_spatial_lintegral_commutes (g : Point → ℝ≥0∞) :
    (∫⁻ x in jointImage, g x) =
      ∫⁻ p in jointDomain, ENNReal.ofReal |(jointJacobian p).det| * g (jointMap p) :=
  lintegral_image_eq_lintegral_abs_det_fderiv_mul volume joint_domain_measurable
    (fun p _ => jointMap_hasFDerivWithinAt p) jointMap_injOn g

theorem joint_volume_eq_jacobian_lintegral :
    volume jointImage = ∫⁻ p in jointDomain, ENNReal.ofReal |(jointJacobian p).det| :=
  (lintegral_abs_det_fderiv_eq_addHaar_image volume joint_domain_measurable
    (fun p _ => jointMap_hasFDerivWithinAt p) jointMap_injOn).symm

theorem jointImage_volume_pos : 0 < volume jointImage := by
  rw [joint_volume_eq_jacobian_lintegral]
  apply pos_iff_ne_zero.mpr
  intro zero
  have measured := aemeasurable_ofReal_abs_det_fderivWithin volume joint_domain_measurable
    (fun p _ => jointMap_hasFDerivWithinAt p)
  have aeZero := (lintegral_eq_zero_iff' measured).mp zero
  have outside : ∀ᵐ p ∂(volume : Measure Point), p ∉ jointDomain := by
    filter_upwards [(ae_restrict_iff' joint_domain_measurable).mp aeZero] with p hp
    intro inside
    have positive : 0 < ENNReal.ofReal |(jointJacobian p).det| :=
      ENNReal.ofReal_pos.mpr (abs_pos.mpr (jointJacobian_det_ne_zero p inside))
    exact positive.ne' (hp inside)
  have null : volume jointDomain = 0 := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using outside
  exact (Measure.measure_pos_of_nonempty_interior volume
    ((domain_interior_nonempty 0).mono (interior_mono subset_union_left))).ne' null

end
end LAlanine40K2025.BasinRefinement.AdjacentFlow
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
