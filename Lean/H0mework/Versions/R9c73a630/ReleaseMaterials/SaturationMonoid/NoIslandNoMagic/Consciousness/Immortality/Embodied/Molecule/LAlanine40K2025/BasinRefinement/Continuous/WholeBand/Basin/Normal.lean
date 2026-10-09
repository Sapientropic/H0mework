import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Tangent

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin
open SourceGaussianModel ContinuousGradient GlobalSource Set
noncomputable section

theorem source_normal_derivative_zero (x : Point) (inside : x ∈ frontier basin)
    (level : Point → ℝ) (normal : Point →L[ℝ] ℝ) (differentiable : HasFDerivAt level normal x)
    (zero_on_boundary : ∀ y ∈ frontier basin, level y = 0) : normal (sourceGradient x) = 0 := by
  have trajectory : HasDerivAt (flow x) (sourceGradient x) 0 := by
    simpa only [flow_starts] using flow_hasDerivAt x 0
  have chain : HasDerivAt (fun t : ℝ => level (flow x t)) (normal (sourceGradient x)) 0 := by
    have atStart : HasFDerivAt level normal (flow x 0) := by simpa only [flow_starts] using differentiable
    exact atStart.comp_hasDerivAt 0 trajectory
  have constant : (fun t : ℝ => level (flow x t)) = fun _ => 0 := by
    funext t
    exact zero_on_boundary _ (actual_frontier_retention x inside t)
  rw [constant] at chain
  exact chain.unique (hasDerivAt_const 0 (0 : ℝ))

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
