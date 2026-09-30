import H0mework.Chemistry.LAlanineWholeBandCell0.SpatialImage
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Spatial

open SourceGaussianModel WholeBandActual WholeBandGeometry WholeBandCell0Geometry
open WholeBandCell0Differential Set MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem cell0_true_spatial_integral_commutes (g : Point → ℝ) :
    (∫ x in cell0_truePatch, g x) =
      ∫ p in cellDomain 0, |(cell0_actualDerivative p).det| • g (cell0ParameterMap p) :=
  integral_image_eq_integral_abs_det_fderiv_smul volume cell0_domain_measurable
    cell0_actualDerivative_hasFDerivWithinAt cell0ParameterMap_injOn g

theorem cell0_true_spatial_integrable_iff (g : Point → ℝ) :
    IntegrableOn g cell0_truePatch ↔
      IntegrableOn (fun p => |(cell0_actualDerivative p).det| • g (cell0ParameterMap p)) (cellDomain 0) :=
  integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume cell0_domain_measurable
    cell0_actualDerivative_hasFDerivWithinAt cell0ParameterMap_injOn g

theorem cell0_true_spatial_lintegral_commutes (g : Point → ℝ≥0∞) :
    (∫⁻ x in cell0_truePatch, g x) =
      ∫⁻ p in cellDomain 0, ENNReal.ofReal |(cell0_actualDerivative p).det| * g (cell0ParameterMap p) :=
  lintegral_image_eq_lintegral_abs_det_fderiv_mul volume cell0_domain_measurable
    cell0_actualDerivative_hasFDerivWithinAt cell0ParameterMap_injOn g

theorem cell0_true_volume_eq_jacobian_lintegral :
    volume cell0_truePatch = ∫⁻ p in cellDomain 0, ENNReal.ofReal |(cell0_actualDerivative p).det| :=
  (lintegral_abs_det_fderiv_eq_addHaar_image volume cell0_domain_measurable
    cell0_actualDerivative_hasFDerivWithinAt cell0ParameterMap_injOn).symm

theorem cell0_actualDerivative_det_ne_zero (p : Point) (inside : p ∈ cellDomain 0) :
    (cell0_actualDerivative p).det ≠ 0 := by
  rw [cell0_actualDerivative_eq_trueJacobian ⟨p, inside⟩]
  exact cell0_trueJacobian_det_ne_zero ⟨p, inside⟩

theorem cell0_truePatch_volume_pos : 0 < volume cell0_truePatch := by
  rw [cell0_true_volume_eq_jacobian_lintegral]
  apply pos_iff_ne_zero.mpr
  intro zero
  have measured := aemeasurable_ofReal_abs_det_fderivWithin volume cell0_domain_measurable
    cell0_actualDerivative_hasFDerivWithinAt
  have aeZero := (lintegral_eq_zero_iff' measured).mp zero
  have outside : ∀ᵐ p ∂(volume : Measure Point), p ∉ cellDomain 0 := by
    filter_upwards [(ae_restrict_iff' cell0_domain_measurable).mp aeZero] with p hp
    intro inside
    have positive : 0 < ENNReal.ofReal |(cell0_actualDerivative p).det| :=
      ENNReal.ofReal_pos.mpr (abs_pos.mpr (cell0_actualDerivative_det_ne_zero p inside))
    exact positive.ne' (hp inside)
  have null : volume (cellDomain 0) = 0 := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using outside
  exact (Measure.measure_pos_of_nonempty_interior volume cell0_domain_interior_nonempty).ne' null

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Spatial
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
