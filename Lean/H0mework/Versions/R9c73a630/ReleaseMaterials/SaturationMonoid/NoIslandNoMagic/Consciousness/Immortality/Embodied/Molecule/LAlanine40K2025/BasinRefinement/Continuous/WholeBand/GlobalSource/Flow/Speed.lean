import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandGlobalSource.FlowGlobal

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource
open SourceGaussianModel ContinuousGradient
noncomputable section

theorem flow_time_lipschitz (x : Point) : LipschitzWith sourceSpeedBound (flow x) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (flow_hasDerivAt x t).differentiableAt)
  intro t
  rw [(flow_hasDerivAt x t).deriv]
  exact_mod_cast sourceGradient_uniform_bound (flow x t)

theorem flow_displacement (x : Point) (t : ℝ) : dist (flow x t) x ≤ (sourceSpeedBound : ℝ)*|t| := by
  have bound := (flow_time_lipschitz x).dist_le_mul t 0
  simpa only [flow_starts,Real.dist_eq,sub_zero] using bound

end
end LAlanine40K2025.BasinRefinement.GlobalSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
