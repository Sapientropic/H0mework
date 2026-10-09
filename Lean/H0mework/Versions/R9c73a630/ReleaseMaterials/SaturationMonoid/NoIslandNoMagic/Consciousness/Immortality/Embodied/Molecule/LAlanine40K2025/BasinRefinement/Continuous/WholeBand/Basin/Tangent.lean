import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Frontier
import Mathlib.Analysis.Calculus.TangentCone.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin
open SourceGaussianModel ContinuousGradient GlobalSource Set Filter
open scoped Topology
noncomputable section

theorem original_gradient_tangent (x : Point) (inside : x ∈ frontier basin) :
    sourceGradient x ∈ tangentConeAt ℝ (frontier basin) x := by
  apply mem_tangentConeAt_of_seq (𝓝[≠] (0 : ℝ)) (fun t : ℝ => t⁻¹) (fun t => flow x t-x)
  · have first : Tendsto (flow x) (𝓝[≠] (0 : ℝ)) (𝓝 (flow x 0)) :=
      (flow_continuous x).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have tends := first.sub_const x
    simpa only [flow_starts,sub_self] using tends
  · apply Eventually.of_forall
    intro t
    have equal : x + (flow x t-x) = flow x t := by abel
    rw [equal]
    exact actual_frontier_retention x inside t
  · have derivative := (flow_hasDerivAt x 0).tendsto_slope_zero
    simpa only [flow_starts,zero_add] using derivative

theorem original_negative_gradient_tangent (x : Point) (inside : x ∈ frontier basin) :
    -sourceGradient x ∈ tangentConeAt ℝ (frontier basin) x := by
  apply mem_tangentConeAt_of_seq (𝓝[≠] (0 : ℝ)) (fun t : ℝ => t⁻¹) (fun t => flow x (-t)-x)
  · have first : Tendsto (fun t : ℝ => flow x (-t)) (𝓝[≠] (0 : ℝ)) (𝓝 (flow x (-0))) :=
      ((flow_continuous x).comp continuous_neg).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have tends := first.sub_const x
    simpa only [Function.comp_def,neg_zero,flow_starts,sub_self] using tends
  · apply Eventually.of_forall
    intro t
    have equal : x + (flow x (-t)-x) = flow x (-t) := by abel
    rw [equal]
    exact actual_frontier_retention x inside (-t)
  · have derivative := (reverse_flow_derivative x 0).tendsto_slope_zero
    simpa only [flow_starts,zero_add,neg_zero] using derivative

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
