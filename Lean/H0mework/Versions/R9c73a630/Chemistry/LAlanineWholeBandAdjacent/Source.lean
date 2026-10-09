import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell1.ActualNondegenerate

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentFlow

open SourceGaussianModel WholeBandGeometry WholeBandContinuation WholeBandContinuationParameter
open WholeBandCell1Actual WholeBandAdjacentGeometry WholeBandCell1Differential Set
noncomputable section

def jointDomain : Set Point := cellDomain 0 ∪ cellDomain 1
def jointMap : Point → Point := sourceParameterMap 0
def jointJacobian (p : Point) : Point →L[ℝ] Point := trueJacobian 0 p

theorem maps_are_same : sourceParameterMap 1 = sourceParameterMap 0 := rfl
theorem jacobians_are_same : trueJacobian 1 = trueJacobian 0 := rfl

theorem jointMap_injOn : InjOn jointMap jointDomain := by
  intro p hp q hq meeting
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact (actual_parameter_meeting 0 0 cell0_source_fields cell0_source_fields
      cell0_positive_reports cell0_positive_reports p q hp hq).mp meeting
  · exact (actual_parameter_meeting 0 1 cell0_source_fields cell1_source_fields
      cell0_positive_reports cell1_positive_reports p q hp hq).mp meeting
  · exact (actual_parameter_meeting 1 0 cell1_source_fields cell0_source_fields
      cell1_positive_reports cell0_positive_reports p q hp hq).mp meeting
  · exact (actual_parameter_meeting 1 1 cell1_source_fields cell1_source_fields
      cell1_positive_reports cell1_positive_reports p q hp hq).mp meeting

theorem jointJacobian_det_ne_zero (p : Point) (inside : p ∈ jointDomain) :
    LinearMap.det (jointJacobian p).toLinearMap ≠ 0 := by
  rcases inside with left | right
  · exact trueJacobian_det_ne_zero 0 cell0_source_fields WholeBandCell0Differential.cell0_analytic_bounds
      cell0_positive_reports p left
  · exact cell1_actual_jacobian_det_ne_zero ⟨p,right⟩

theorem joint_source_nonempty : jointDomain.Nonempty := (cellDomain_nonempty 0).mono subset_union_left

end
end LAlanine40K2025.BasinRefinement.AdjacentFlow
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
