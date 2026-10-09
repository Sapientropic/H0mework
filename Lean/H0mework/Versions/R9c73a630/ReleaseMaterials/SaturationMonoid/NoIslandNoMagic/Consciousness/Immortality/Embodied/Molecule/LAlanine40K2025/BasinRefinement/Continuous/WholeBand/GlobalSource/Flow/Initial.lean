import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandGlobalSource.FlowGlobal

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource
open SourceGaussianModel ContinuousGradient Set
noncomputable section

theorem flow_initial_distance (x y : Point) (t : ℝ) (nonnegative : 0 ≤ t) :
    dist (flow x t) (flow y t) ≤ dist x y * Real.exp ((sourceLipschitzBound : ℝ)*t) := by
  have bound := dist_le_of_trajectories_ODE (v := fun _ => sourceGradient)
    (fun _ => sourceGradient_globally_lipschitz) (flow_continuous x).continuousOn
    (fun u _ => (flow_hasDerivAt x u).hasDerivWithinAt) (flow_continuous y).continuousOn
    (fun u _ => (flow_hasDerivAt y u).hasDerivWithinAt)
    (show dist (flow x 0) (flow y 0) ≤ dist x y by rw [flow_starts,flow_starts]) t
    (show t ∈ Icc 0 t from ⟨nonnegative,le_rfl⟩)
  simpa only [sub_zero] using bound

theorem flow_initial_lipschitz (t : ℝ) (nonnegative : 0 ≤ t) :
    LipschitzWith ⟨Real.exp ((sourceLipschitzBound : ℝ)*t), (Real.exp_pos _).le⟩
      (fun x : Point => flow x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (flow x t) (flow y t) ≤ Real.exp ((sourceLipschitzBound : ℝ)*t)*dist x y
  rw [mul_comm]
  exact flow_initial_distance x y t nonnegative

theorem flow_initial_continuous (t : ℝ) (nonnegative : 0 ≤ t) :
    Continuous (fun x : Point => flow x t) := (flow_initial_lipschitz t nonnegative).continuous

end
end LAlanine40K2025.BasinRefinement.GlobalSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
