import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Seeds.Middle

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
open SourceGaussianModel GlobalSource Set Filter MeasureTheory
open WholeBandAttractor
open scoped Topology
noncomputable section

def atom006Basin : Set Point := basin atom006Seed
def atom006Patches (n : ℕ) : Set Point := entryPatch atom006Seed n

theorem atom007_basin_same_source : basin atom007Seed = WholeBandBasin.basin := rfl
theorem atom007_patches_same_source (n : ℕ) :
    entryPatch atom007Seed n = WholeBandBasin.entryPatch n := rfl

theorem atom006_basin_open : IsOpen atom006Basin := basin_open atom006Seed
theorem atom006_basin_positive : 0 < volume atom006Basin :=
  basin_positive_volume atom006Seed
theorem atom006_basin_cover : atom006Basin = ⋃ n : ℕ, atom006Patches n :=
  basin_eq_union atom006Seed
theorem atom006_patches_monotone : Monotone atom006Patches :=
  entryPatch_monotone atom006Seed

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
