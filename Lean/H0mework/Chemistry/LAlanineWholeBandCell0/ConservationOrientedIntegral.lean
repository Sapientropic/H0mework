import H0mework.Chemistry.LAlanineWholeBandCell0.ConservationOrientation
import H0mework.Chemistry.LAlanineWholeBandCell0.SpatialIntegral

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData ContinuousGradient ContinuousSeed TrueFlowDifferential TrueFlowGeometry
open TrueFlowConservation WholeBandActual WholeBandGeometry WholeBandCell0Geometry WholeBandCell0Differential
open WholeBandCell0Continuation WholeBandCell0Spatial WholeBandCell0Boundary WholeCellBoundary
open Matrix Set MeasureTheory
noncomputable section

theorem cell0_actualDerivative_det_pos (p : Point) (inside : p ∈ (cellDomain 0)) :
    0 < (cell0_actualDerivative p).det := by
  rw [cell0_actualDerivative_eq_trueJacobian ⟨p, inside⟩]
  exact cell0_trueJacobian_det_pos ⟨p, inside⟩

/-- The actual positive orientation removes the absolute value from the original change of variables. -/
theorem cell0_true_spatial_integral_oriented (g : Point → ℝ) :
    (∫ x in cell0_truePatch, g x) =
      ∫ p in (cellDomain 0), (cell0_actualDerivative p).det • g (cell0ParameterMap p) := by
  rw [cell0_true_spatial_integral_commutes]
  apply setIntegral_congr_fun cell0_domain_measurable
  intro p inside
  change |(cell0_actualDerivative p).det| • g (cell0ParameterMap p) = _
  rw [abs_of_pos (cell0_actualDerivative_det_pos p inside)]

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
