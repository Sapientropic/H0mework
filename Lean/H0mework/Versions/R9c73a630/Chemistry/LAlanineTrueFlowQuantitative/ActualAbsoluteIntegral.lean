import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowQuantitative.ActualVolumeBounds
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowQuantitative.ActualIntegral
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowQuantitative.SourceParameterMeasure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowQuantitative

open SourceGaussianModel SourceFiniteData TrueFlowGeometry TrueFlowConservation
open WholeCellPartition WholeCellBoundary Set MeasureTheory
noncomputable section

theorem true_volume_eq_actual_det_integral :
    volume.real truePatch = ∫ p in fullDomain, (actualDerivative p).det := by
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using
    true_spatial_integral_oriented (fun _ : Point => (1 : ℝ))

theorem actual_determinant_integrable :
    IntegrableOn (fun p => (actualDerivative p).det) fullDomain := by
  have source := (true_spatial_integrable_iff (fun _ : Point => (1 : ℝ))).mp
    (integrableOn_const (C := (1 : ℝ)) truePatch_volume_lt_top.ne)
  apply source.congr_fun _ full_measurable
  intro p inside
  simp only [abs_of_pos (actualDerivative_det_pos p inside), smul_eq_mul, mul_one]

theorem true_volume_relative_parameter_bounds :
    (1 / 80000 : ℝ) * volume.real fullDomain ≤ volume.real truePatch ∧
      volume.real truePatch ≤ (31 / 1000000 : ℝ) * volume.real fullDomain := by
  rw [true_volume_eq_actual_det_integral]
  constructor
  · exact setIntegral_ge_of_const_le_real full_measurable full_compact.measure_lt_top.ne
      (fun p hp => (actualDerivative_det_bounds p hp).1.le) actual_determinant_integrable
  · have bound := setIntegral_mono_on actual_determinant_integrable
      (integrableOn_const (C := (31 / 1000000 : ℝ)) full_compact.measure_lt_top.ne)
      full_measurable (fun p hp => (actualDerivative_det_bounds p hp).2.le)
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using bound

/-- Absolute real volume bounds use the original parameter measure and actual generated determinant. -/
theorem true_volume_absolute_bounds :
    (3 / 100000000 : ℝ) < volume.real truePatch ∧ volume.real truePatch < 8 / 100000000 := by
  have measure := fullDomain_volume_bounds
  have determinant := true_volume_relative_parameter_bounds
  constructor <;> linarith

theorem true_laplacian_absolute_bounds :
    (-(6 / 100000000) : ℝ) < (∫ x in truePatch, laplacian sourceTerms densityMatrix x) ∧
      (∫ x in truePatch, laplacian sourceTerms densityMatrix x) < -(3 / 400000000) := by
  have volumeBounds := true_volume_absolute_bounds
  have sourceBounds := true_spatial_laplacian_bounds
  constructor <;> linarith

theorem true_net_cap_flux_absolute_bounds :
    (-(6 / 100000000) : ℝ) <
        (∫ p in faceDomain 2, actualCapFlux true p + actualCapFlux false p) ∧
      (∫ p in faceDomain 2, actualCapFlux true p + actualCapFlux false p) < -(3 / 400000000) := by
  rw [← true_spatial_laplacian_eq_cap_flux]
  exact true_laplacian_absolute_bounds

end
end LAlanine40K2025.BasinRefinement.TrueFlowQuantitative
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
