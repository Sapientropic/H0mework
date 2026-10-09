import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A010.Producer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandAttractor.FlowNeighborhood
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAttractor.Atom010
open SourceGaussianModel ContinuousGradient Metric Set Filter MeasureTheory
open scoped Topology
noncomputable section

def attractingNeighborhood : Set SourceGaussianModel.Point := Attractor.neighborhood actualZero

theorem attracting_nonempty : attractingNeighborhood.Nonempty :=
  Attractor.neighborhood_nonempty centre radius alpha contraction radius_positive.le alpha_positive
    contraction_lt_one actual_budget actual_shifted_hessian actualZero

theorem attracting_open : IsOpen attractingNeighborhood := Attractor.neighborhood_open actualZero

theorem attracting_positive_volume : 0 < volume attractingNeighborhood :=
  attracting_open.measure_pos volume attracting_nonempty

theorem actual_positive_retention (x : SourceGaussianModel.Point) (inside : x ∈ attractingNeighborhood)
    (t : ℝ) (nonnegative : 0 ≤ t) : GlobalSource.flow x t ∈ attractingNeighborhood :=
  Attractor.neighborhood_retained centre radius alpha contraction radius_positive.le alpha_positive
    contraction_lt_one actual_budget actual_shifted_hessian actualZero x inside t nonnegative

theorem actual_convergence (x : SourceGaussianModel.Point) (inside : x ∈ attractingNeighborhood) :
    Tendsto (GlobalSource.flow x) atTop (𝓝 actualZero.point) :=
  Attractor.neighborhood_converges centre radius alpha contraction radius_positive.le alpha_positive
    contraction_lt_one actual_budget actual_shifted_hessian actualZero x inside

theorem actual_exponential_rate (x : SourceGaussianModel.Point) (inside : x ∈ attractingNeighborhood)
    (t : ℝ) (nonnegative : 0 ≤ t) :
    dist (GlobalSource.flow x t) actualZero.point ≤ dist x actualZero.point * Real.exp (-(7/5 : ℝ)*t) := by
  have geometry := Attractor.neighborhood_geometry actualZero actual_zero_interior
  have bound := Attractor.flow_exponential_bound centre radius alpha contraction alpha_positive
    contraction_lt_one actual_shifted_hessian actualZero (Attractor.neighborhoodRadius actualZero)
    geometry.1 geometry.2 x (Metric.mem_ball.mp inside).le t nonnegative
  have rate : Attractor.attractionRate alpha contraction = 7/5 := by
    norm_num [Attractor.attractionRate,alpha,contraction]
  rwa [rate] at bound

end
end LAlanine40K2025.BasinRefinement.WholeBandAttractor.Atom010
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
