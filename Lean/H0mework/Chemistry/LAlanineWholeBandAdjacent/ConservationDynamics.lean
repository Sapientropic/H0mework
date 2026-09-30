import H0mework.Chemistry.LAlanineBandContinuation.ConservationOrientation
import H0mework.Chemistry.LAlanineWholeBandAdjacent.Consumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentConservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandCell1Actual WholeBandContinuationDifferential WholeBandContinuationParameter
open WholeBandConservation AdjacentFlow Set MeasureTheory
noncomputable section

theorem joint_retime_inside (p : Point) (inside : p ∈ jointDomain) (s : Time) : retime p s ∈ jointDomain := by
  rcases inside with left | right
  · exact Or.inl (retime_inside 0 p left s)
  · exact Or.inr (retime_inside 1 p right s)

theorem joint_evolvingJacobian_eq_retimed (p : Point) (inside : p ∈ jointDomain) (s : Time) :
    evolvingJacobian 0 p s = LinearMap.toMatrix' (jointJacobian (retime p s)).toLinearMap := by
  rcases inside with left | right
  · exact evolvingJacobian_eq_retimed 0 cell0_source_fields WholeBandCell0Differential.cell0_analytic_bounds p left s
  · exact evolvingJacobian_eq_retimed 1 cell1_source_fields WholeBandCell1Differential.cell1_analytic_bounds p right s

theorem jointJacobian_det_pos (p : Point) (inside : p ∈ jointDomain) :
    0 < (jointJacobian p).det := by
  rcases inside with left | right
  · exact actualJacobian_det_pos 0 cell0_source_fields WholeBandCell0Differential.cell0_analytic_bounds cell0_positive_reports p left
  · exact actualJacobian_det_pos 1 cell1_source_fields WholeBandCell1Differential.cell1_analytic_bounds cell1_positive_reports p right

theorem joint_actual_time_integral (p : Point) (inside : p ∈ jointDomain) :
    (∫ t in (-(1/2 : ℝ))..(1/2), signedVolumeRate 0 p t) =
      (evolvingJacobian 0 p (1/2)).det - (evolvingJacobian 0 p (-(1/2))).det := by
  rcases inside with left | right
  · exact actual_time_integral_eq_det_difference 0 cell0_source_fields WholeBandCell0Differential.cell0_analytic_bounds p left
  · exact actual_time_integral_eq_det_difference 1 cell1_source_fields WholeBandCell1Differential.cell1_analytic_bounds p right

theorem jointJacobian_time_column (p : Point) (inside : p ∈ jointDomain) :
    jointJacobian p (Pi.single 2 1) = ContinuousGradient.sourceGradient (jointMap p) := by
  rcases inside with left | right
  · exact trueJacobian_time_column 0 cell0_source_fields WholeBandCell0Differential.cell0_analytic_bounds p left
  · exact trueJacobian_time_column 1 cell1_source_fields WholeBandCell1Differential.cell1_analytic_bounds p right

end
end LAlanine40K2025.BasinRefinement.AdjacentConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
