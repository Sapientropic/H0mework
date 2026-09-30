import H0mework.Chemistry.LAlanineTrueFlowGeometry.SpatialImage
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open SourceGaussianModel TrueFlowDifferential TrueTubeWholeActual WholeCellPartition
open Set MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Change of variables on the actual true-flow image, with its canonical source derivative. -/
theorem true_spatial_integral_commutes (g : Point → ℝ) :
    (∫ x in truePatch, g x) =
      ∫ p in fullDomain, |(actualDerivative p).det| • g (trueParameterMap p) :=
  integral_image_eq_integral_abs_det_fderiv_smul volume full_measurable
    actualDerivative_hasFDerivWithinAt trueParameterMap_injOn g

theorem true_spatial_integrable_iff (g : Point → ℝ) :
    IntegrableOn g truePatch ↔
      IntegrableOn (fun p => |(actualDerivative p).det| • g (trueParameterMap p)) fullDomain :=
  integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume full_measurable
    actualDerivative_hasFDerivWithinAt trueParameterMap_injOn g

theorem true_spatial_lintegral_commutes (g : Point → ℝ≥0∞) :
    (∫⁻ x in truePatch, g x) =
      ∫⁻ p in fullDomain, ENNReal.ofReal |(actualDerivative p).det| * g (trueParameterMap p) :=
  lintegral_image_eq_lintegral_abs_det_fderiv_mul volume full_measurable
    actualDerivative_hasFDerivWithinAt trueParameterMap_injOn g

theorem true_volume_eq_jacobian_lintegral :
    volume truePatch = ∫⁻ p in fullDomain, ENNReal.ofReal |(actualDerivative p).det| :=
  (lintegral_abs_det_fderiv_eq_addHaar_image volume full_measurable
    actualDerivative_hasFDerivWithinAt trueParameterMap_injOn).symm

theorem actualDerivative_det_ne_zero (p : Point) (inside : p ∈ fullDomain) :
    (actualDerivative p).det ≠ 0 := by
  rw [actualDerivative_eq_trueJacobian ⟨p, inside⟩]
  exact trueJacobian_det_ne_zero ⟨p, inside⟩

theorem truePatch_volume_pos : 0 < volume truePatch := by
  rw [true_volume_eq_jacobian_lintegral]
  apply pos_iff_ne_zero.mpr
  intro zero
  have measured := aemeasurable_ofReal_abs_det_fderivWithin volume full_measurable
    actualDerivative_hasFDerivWithinAt
  have aeZero := (lintegral_eq_zero_iff' measured).mp zero
  have outside : ∀ᵐ p ∂(volume : Measure Point), p ∉ fullDomain := by
    filter_upwards [(ae_restrict_iff' full_measurable).mp aeZero] with p hp
    intro inside
    have positive : 0 < ENNReal.ofReal |(actualDerivative p).det| :=
      ENNReal.ofReal_pos.mpr (abs_pos.mpr (actualDerivative_det_ne_zero p inside))
    exact positive.ne' (hp inside)
  have null : volume fullDomain = 0 := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using outside
  exact (Measure.measure_pos_of_nonempty_interior volume fullDomain_interior_nonempty).ne' null

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
