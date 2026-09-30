import H0mework.Chemistry.LAlanineWholeBandAdjacent.Domain

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentFlow

open SourceGaussianModel WholeBandGeometry WholeBandContinuation WholeBandContinuationParameter
open WholeBandCell1Actual Set
noncomputable section

theorem jointMap_hasFDerivWithinAt (p : Point) :
    HasFDerivWithinAt jointMap (jointJacobian p) jointDomain p := by
  have left : HasFDerivWithinAt jointMap (jointJacobian p) (cellDomain 0) p := by
    by_cases inside : p ∈ cellDomain 0
    · exact actualMap_hasFDerivWithinAt 0 cell0_source_fields WholeBandCell0Differential.cell0_analytic_bounds p inside
    · apply HasFDerivWithinAt.of_notMem_closure
      have closed : IsClosed (cellDomain 0) := (domain_eq_Icc 0).symm ▸ isClosed_Icc
      rwa [closed.closure_eq]
  have right : HasFDerivWithinAt jointMap (jointJacobian p) (cellDomain 1) p := by
    by_cases inside : p ∈ cellDomain 1
    · exact cell1_actual_parameter_derivative ⟨p,inside⟩
    · apply HasFDerivWithinAt.of_notMem_closure
      have closed : IsClosed (cellDomain 1) := (domain_eq_Icc 1).symm ▸ isClosed_Icc
      rwa [closed.closure_eq]
  exact left.union right

theorem jointJacobian_eq_fderivWithin (p : Point) (inside : p ∈ jointDomain) :
    jointJacobian p = fderivWithin ℝ jointMap jointDomain p :=
  ((jointMap_hasFDerivWithinAt p).fderivWithin (joint_domain_uniqueDiffOn p inside)).symm

theorem jointMap_continuousOn : ContinuousOn jointMap jointDomain :=
  fun p _ => (jointMap_hasFDerivWithinAt p).continuousWithinAt

end
end LAlanine40K2025.BasinRefinement.AdjacentFlow
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
