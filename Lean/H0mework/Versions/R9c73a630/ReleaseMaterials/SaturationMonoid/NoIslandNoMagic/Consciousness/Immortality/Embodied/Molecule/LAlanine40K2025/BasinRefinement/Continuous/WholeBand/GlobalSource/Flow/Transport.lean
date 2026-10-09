import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Flow.Initial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource
open SourceGaussianModel ContinuousGradient Set
noncomputable section

theorem reverse_flow_derivative (x : Point) (t : ℝ) :
    HasDerivAt (fun s : ℝ => flow x (-s)) (-sourceGradient (flow x (-t))) t := by
  have derivative := (flow_hasDerivAt x (-t)).scomp t (hasDerivAt_neg t)
  simpa only [Function.comp_def,neg_smul,one_smul] using derivative

theorem reverse_flow_distance (x y : Point) (t : ℝ) (nonnegative : 0 ≤ t) :
    dist (flow x (-t)) (flow y (-t)) ≤ dist x y * Real.exp ((sourceLipschitzBound : ℝ)*t) := by
  have bound := dist_le_of_trajectories_ODE (v := fun _ z => -sourceGradient z)
    (fun _ => sourceGradient_globally_lipschitz.neg) ((flow_continuous x).comp continuous_neg).continuousOn
    (fun u _ => (reverse_flow_derivative x u).hasDerivWithinAt)
    ((flow_continuous y).comp continuous_neg).continuousOn
    (fun u _ => (reverse_flow_derivative y u).hasDerivWithinAt)
    (show dist (flow x (-0)) (flow y (-0)) ≤ dist x y by rw [neg_zero,flow_starts,flow_starts]) t
    (show t ∈ Icc 0 t from ⟨nonnegative,le_rfl⟩)
  simpa only [sub_zero,Function.comp_def] using bound

theorem flow_initial_distance_all (x y : Point) (t : ℝ) :
    dist (flow x t) (flow y t) ≤ dist x y * Real.exp ((sourceLipschitzBound : ℝ)*|t|) := by
  by_cases nonnegative : 0 ≤ t
  · simpa only [abs_of_nonneg nonnegative] using flow_initial_distance x y t nonnegative
  · have negative := le_of_not_ge nonnegative
    simpa only [neg_neg,abs_of_nonpos negative] using reverse_flow_distance x y (-t) (neg_nonneg.mpr negative)

theorem flow_initial_continuous_all (t : ℝ) : Continuous (fun x : Point => flow x t) := by
  have lip : LipschitzWith ⟨Real.exp ((sourceLipschitzBound : ℝ)*|t|),(Real.exp_pos _).le⟩
      (fun x : Point => flow x t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (flow x t) (flow y t) ≤ Real.exp ((sourceLipschitzBound : ℝ)*|t|)*dist x y
    rw [mul_comm]
    exact flow_initial_distance_all x y t
  exact lip.continuous

def flowHomeomorph (t : ℝ) : Point ≃ₜ Point where
  toFun := fun x => flow x t
  invFun := fun x => flow x (-t)
  left_inv := fun x => flow_inverse x t
  right_inv := fun x => by simpa only [neg_neg] using flow_inverse x (-t)
  continuous_toFun := flow_initial_continuous_all t
  continuous_invFun := flow_initial_continuous_all (-t)

end
end LAlanine40K2025.BasinRefinement.GlobalSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
