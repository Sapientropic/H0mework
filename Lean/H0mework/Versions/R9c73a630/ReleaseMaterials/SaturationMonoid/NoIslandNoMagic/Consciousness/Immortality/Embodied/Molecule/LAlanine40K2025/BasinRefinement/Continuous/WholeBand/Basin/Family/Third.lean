import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Interaction
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Instances
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A009.Flow

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
open SourceGaussianModel GlobalSource Set Filter Metric MeasureTheory
open WholeBandAttractor
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open scoped Topology
noncomputable section

def atom009Basin : Set Point := basin atom009Seed
def atom009Patches (n : ℕ) : Set Point := entryPatch atom009Seed n

theorem atom009_basin_cover : atom009Basin=⋃ n : ℕ, atom009Patches n :=
  basin_eq_union atom009Seed
theorem atom009_basin_open : IsOpen atom009Basin := basin_open atom009Seed
theorem atom009_basin_positive : 0 < volume atom009Basin :=
  basin_positive_volume atom009Seed

theorem original_centres_separated_6_9 :
    Atom006.centre 0+Atom006.radius < Atom009.centre 0-Atom009.radius := by
  norm_num [Atom006.centre,Atom006.centreRat,Atom006.radius,Atom006.radiusRat,
    Atom009.centre,Atom009.centreRat,Atom009.radius,Atom009.radiusRat,
    Atom006.Point.rawCenter,Atom009.Point.rawCenter,SourceExponential.scale]

theorem original_centres_separated_7_9 :
    Atom007.centre 0+Atom007.radius < Atom009.centre 0-Atom009.radius := by
  norm_num [Atom007.centre,Atom007.centreRat,Atom007.radius,Atom007.radiusRat,
    Atom009.centre,Atom009.centreRat,Atom009.radius,Atom009.radiusRat,
    Atom007.Point.rawCenter,Atom009.Point.rawCenter,SourceExponential.scale]

private theorem critical_distinct_of_separated
    (left right : Point) (centreLeft centreRight : Point)
    (radiusLeft radiusRight : ℝ)
    (insideLeft : left ∈ closedBall centreLeft radiusLeft)
    (insideRight : right ∈ closedBall centreRight radiusRight)
    (radiusLeftNonnegative : 0 ≤ radiusLeft)
    (radiusRightNonnegative : 0 ≤ radiusRight)
    (separated : centreLeft 0+radiusLeft < centreRight 0-radiusRight) :
    left ≠ right := by
  intro same
  have first := Metric.mem_closedBall.mp insideLeft
  have second := Metric.mem_closedBall.mp insideRight
  rw [dist_eq_norm,pi_norm_le_iff_of_nonneg radiusLeftNonnegative] at first
  rw [dist_eq_norm,pi_norm_le_iff_of_nonneg radiusRightNonnegative] at second
  have leftCoordinate := abs_le.mp (first 0)
  have rightCoordinate := abs_le.mp (second 0)
  rw [same] at leftCoordinate
  simp only [Pi.sub_apply] at leftCoordinate rightCoordinate
  linarith

theorem original_critical_6_ne_9 :
    Atom006.actualZero.point ≠ Atom009.actualZero.point :=
  critical_distinct_of_separated _ _ _ _ _ _
    Atom006.actualZero.inside Atom009.actualZero.inside
    Atom006.radius_positive.le Atom009.radius_positive.le
    original_centres_separated_6_9

theorem original_critical_7_ne_9 :
    Atom007.actualZero.point ≠ Atom009.actualZero.point :=
  critical_distinct_of_separated _ _ _ _ _ _
    Atom007.actualZero.inside Atom009.actualZero.inside
    Atom007.radius_positive.le Atom009.radius_positive.le
    original_centres_separated_7_9

theorem original_basins_6_9_disjoint : Disjoint atom006Basin atom009Basin :=
  basins_disjoint_of_critical_ne atom006Seed atom009Seed original_critical_6_ne_9

theorem original_basins_7_9_disjoint : Disjoint WholeBandBasin.basin atom009Basin := by
  rw [← atom007_basin_same_source]
  exact basins_disjoint_of_critical_ne atom007Seed atom009Seed original_critical_7_ne_9

def interatomicEnergy69 : ℝ := interatomicPairEnergy atom006Seed atom009Seed
def interatomicEnergy79 : ℝ := interatomicPairEnergy atom007Seed atom009Seed

theorem both_interatomic_nonnegative :
    0 ≤ interatomicEnergy69 ∧ 0 ≤ interatomicEnergy79 :=
  ⟨interatomic_pair_energy_nonnegative _ _,interatomic_pair_energy_nonnegative _ _⟩

theorem both_interatomic_symmetric :
    interatomicEnergy69=2*halfPairEnergy atom006Seed atom009Seed ∧
    interatomicEnergy79=2*halfPairEnergy atom007Seed atom009Seed :=
  ⟨interatomic_pair_energy_twice _ _,interatomic_pair_energy_twice _ _⟩

theorem both_interatomic_patch_limits :
    Tendsto (fun n : ℕ => (1/2 : ℝ) * ∫ z in pairPatch atom006Seed atom009Seed n,
      realPairIntegrand z) atTop (𝓝 (halfPairEnergy atom006Seed atom009Seed)) ∧
    Tendsto (fun n : ℕ => (1/2 : ℝ) * ∫ z in pairPatch atom007Seed atom009Seed n,
      realPairIntegrand z) atTop (𝓝 (halfPairEnergy atom007Seed atom009Seed)) :=
  ⟨half_pair_energy_patch_limit _ _,half_pair_energy_patch_limit _ _⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
