import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Third
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A008.Flow

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
open SourceGaussianModel GlobalSource Set Filter Metric MeasureTheory
open WholeBandAttractor
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open scoped Topology
noncomputable section

def atom008Basin : Set Point := basin atom008Seed
def atom008Patches (n : ℕ) : Set Point := entryPatch atom008Seed n

theorem atom008_basin_cover : atom008Basin=⋃ n : ℕ, atom008Patches n :=
  basin_eq_union atom008Seed
theorem atom008_basin_open : IsOpen atom008Basin := basin_open atom008Seed
theorem atom008_basin_positive : 0 < volume atom008Basin :=
  basin_positive_volume atom008Seed

theorem original_centres_separated_6_8 :
    Atom006.centre 0+Atom006.radius < Atom008.centre 0-Atom008.radius := by
  norm_num [Atom006.centre,Atom006.centreRat,Atom006.radius,Atom006.radiusRat,
    Atom008.centre,Atom008.centreRat,Atom008.radius,Atom008.radiusRat,
    Atom006.Point.rawCenter,Atom008.Point.rawCenter,SourceExponential.scale]

theorem original_centres_separated_7_8 :
    Atom007.centre 0+Atom007.radius < Atom008.centre 0-Atom008.radius := by
  norm_num [Atom007.centre,Atom007.centreRat,Atom007.radius,Atom007.radiusRat,
    Atom008.centre,Atom008.centreRat,Atom008.radius,Atom008.radiusRat,
    Atom007.Point.rawCenter,Atom008.Point.rawCenter,SourceExponential.scale]

theorem original_centres_separated_8_9 :
    Atom008.centre 0+Atom008.radius < Atom009.centre 0-Atom009.radius := by
  norm_num [Atom008.centre,Atom008.centreRat,Atom008.radius,Atom008.radiusRat,
    Atom009.centre,Atom009.centreRat,Atom009.radius,Atom009.radiusRat,
    Atom008.Point.rawCenter,Atom009.Point.rawCenter,SourceExponential.scale]

theorem critical_distinct_of_separated_boxes
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

theorem original_critical_6_ne_8 :
    Atom006.actualZero.point ≠ Atom008.actualZero.point :=
  critical_distinct_of_separated_boxes _ _ _ _ _ _
    Atom006.actualZero.inside Atom008.actualZero.inside
    Atom006.radius_positive.le Atom008.radius_positive.le
    original_centres_separated_6_8

theorem original_critical_7_ne_8 :
    Atom007.actualZero.point ≠ Atom008.actualZero.point :=
  critical_distinct_of_separated_boxes _ _ _ _ _ _
    Atom007.actualZero.inside Atom008.actualZero.inside
    Atom007.radius_positive.le Atom008.radius_positive.le
    original_centres_separated_7_8

theorem original_critical_8_ne_9 :
    Atom008.actualZero.point ≠ Atom009.actualZero.point :=
  critical_distinct_of_separated_boxes _ _ _ _ _ _
    Atom008.actualZero.inside Atom009.actualZero.inside
    Atom008.radius_positive.le Atom009.radius_positive.le
    original_centres_separated_8_9

theorem original_basins_6_8_disjoint : Disjoint atom006Basin atom008Basin :=
  basins_disjoint_of_critical_ne atom006Seed atom008Seed original_critical_6_ne_8

theorem original_basins_7_8_disjoint : Disjoint WholeBandBasin.basin atom008Basin := by
  rw [← atom007_basin_same_source]
  exact basins_disjoint_of_critical_ne atom007Seed atom008Seed original_critical_7_ne_8

theorem original_basins_8_9_disjoint : Disjoint atom008Basin atom009Basin :=
  basins_disjoint_of_critical_ne atom008Seed atom009Seed original_critical_8_ne_9

def interatomicEnergy68 : ℝ := interatomicPairEnergy atom006Seed atom008Seed
def interatomicEnergy78 : ℝ := interatomicPairEnergy atom007Seed atom008Seed
def interatomicEnergy89 : ℝ := interatomicPairEnergy atom008Seed atom009Seed

theorem three_interatomic_nonnegative :
    0 ≤ interatomicEnergy68 ∧ 0 ≤ interatomicEnergy78 ∧ 0 ≤ interatomicEnergy89 :=
  ⟨interatomic_pair_energy_nonnegative _ _,
    interatomic_pair_energy_nonnegative _ _,
    interatomic_pair_energy_nonnegative _ _⟩

theorem three_interatomic_symmetric :
    interatomicEnergy68=2*halfPairEnergy atom006Seed atom008Seed ∧
    interatomicEnergy78=2*halfPairEnergy atom007Seed atom008Seed ∧
    interatomicEnergy89=2*halfPairEnergy atom008Seed atom009Seed :=
  ⟨interatomic_pair_energy_twice _ _,
    interatomic_pair_energy_twice _ _,
    interatomic_pair_energy_twice _ _⟩

theorem three_interatomic_patch_limits :
    Tendsto (fun n : ℕ => (1/2 : ℝ) * ∫ z in pairPatch atom006Seed atom008Seed n,
      realPairIntegrand z) atTop (𝓝 (halfPairEnergy atom006Seed atom008Seed)) ∧
    Tendsto (fun n : ℕ => (1/2 : ℝ) * ∫ z in pairPatch atom007Seed atom008Seed n,
      realPairIntegrand z) atTop (𝓝 (halfPairEnergy atom007Seed atom008Seed)) ∧
    Tendsto (fun n : ℕ => (1/2 : ℝ) * ∫ z in pairPatch atom008Seed atom009Seed n,
      realPairIntegrand z) atTop (𝓝 (halfPairEnergy atom008Seed atom009Seed)) :=
  ⟨half_pair_energy_patch_limit _ _,
    half_pair_energy_patch_limit _ _,
    half_pair_energy_patch_limit _ _⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
