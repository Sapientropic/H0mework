import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Instances

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
open SourceGaussianModel GlobalSource Set Filter Metric
open WholeBandAttractor
open scoped Topology
noncomputable section

theorem original_centres_separated :
    Atom006.centre 0+Atom006.radius < Atom007.centre 0-Atom007.radius := by
  norm_num [Atom006.centre,Atom006.centreRat,Atom006.radius,Atom006.radiusRat,
    Atom007.centre,Atom007.centreRat,Atom007.radius,Atom007.radiusRat,
    Atom006.Point.rawCenter,Atom007.Point.rawCenter,SourceExponential.scale]

theorem original_critical_points_distinct :
    Atom006.actualZero.point ≠ Atom007.actualZero.point := by
  intro same
  have sixth := Metric.mem_closedBall.mp Atom006.actualZero.inside
  have seventh := Metric.mem_closedBall.mp Atom007.actualZero.inside
  rw [dist_eq_norm,pi_norm_le_iff_of_nonneg Atom006.radius_positive.le] at sixth
  rw [dist_eq_norm,pi_norm_le_iff_of_nonneg Atom007.radius_positive.le] at seventh
  have six := abs_le.mp (sixth 0)
  have seven := abs_le.mp (seventh 0)
  rw [same] at six
  simp only [Pi.sub_apply] at six seven
  have gap := original_centres_separated
  linarith

theorem original_basins_disjoint : Disjoint atom006Basin WholeBandBasin.basin := by
  rw [Set.disjoint_left]
  intro x hx hy
  have sixth : Tendsto (flow x) atTop (𝓝 Atom006.actualZero.point) := hx
  have seventh : Tendsto (flow x) atTop (𝓝 Atom007.actualZero.point) := hy
  exact original_critical_points_distinct (tendsto_nhds_unique sixth seventh)

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
