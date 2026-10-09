import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowConservation.SourceOrientation
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowGeometry.SpatialIntegral

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowConservation

open SourceGaussianModel TrueFlowDifferential TrueFlowGeometry WholeCellPartition Set MeasureTheory
noncomputable section

theorem actualDerivative_det_pos (p : Point) (inside : p ∈ fullDomain) :
    0 < (actualDerivative p).det := by
  rw [actualDerivative_eq_trueJacobian ⟨p, inside⟩]
  exact trueJacobian_det_pos ⟨p, inside⟩

/-- The actual positive orientation removes the absolute value from the original change of variables. -/
theorem true_spatial_integral_oriented (g : Point → ℝ) :
    (∫ x in truePatch, g x) =
      ∫ p in fullDomain, (actualDerivative p).det • g (trueParameterMap p) := by
  rw [true_spatial_integral_commutes]
  apply setIntegral_congr_fun full_measurable
  intro p inside
  change |(actualDerivative p).det| • g (trueParameterMap p) = _
  rw [abs_of_pos (actualDerivative_det_pos p inside)]

end
end LAlanine40K2025.BasinRefinement.TrueFlowConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
