import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A012.Bounds
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandAttractor.Equilibrium

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAttractor.Atom012
open SourceGaussianModel ContinuousGradient Metric
noncomputable section

/-- Original source calculations generate the zero, rather than assume the numerical proposal is one. -/
def actualZero : Attractor.ZeroInBall centre radius :=
  Attractor.produceZero centre radius alpha contraction radius_positive alpha_positive
    contraction_lt_one actual_budget.le actual_shifted_hessian

theorem actual_gradient_zero : sourceGradient actualZero.point = 0 := actualZero.zero

theorem actual_zero_unique (x : SourceGaussianModel.Point) (inside : x ∈ closedBall centre radius)
    (zero : sourceGradient x = 0) : x = actualZero.point := actualZero.unique x inside zero

theorem actual_zero_interior : actualZero.point ∈ ball centre radius :=
  Attractor.zero_interior centre radius alpha contraction radius_positive.le alpha_positive
    contraction_lt_one actual_budget actual_shifted_hessian actualZero

theorem actual_zero_distance : dist actualZero.point centre ≤ (1/1000000000 : ℝ) := by
  have h := Attractor.zero_distance_le centre radius alpha contraction radius_positive.le alpha_positive
    contraction_lt_one actual_shifted_hessian actualZero.point actualZero.inside actualZero.zero
  have small := actual_gradient_small
  norm_num [alpha,contraction] at h
  linarith

theorem actual_full_flow_equilibrium (t : ℝ) : GlobalSource.flow actualZero.point t = actualZero.point :=
  Attractor.zero_is_original_flow_equilibrium centre radius actualZero t

end
end LAlanine40K2025.BasinRefinement.WholeBandAttractor.Atom012
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
