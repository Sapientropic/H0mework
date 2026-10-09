import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Slater.Additivity
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.SourceClosure
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater
open SourceGaussianModel GlobalSource WholeBandBasin Set MeasureTheory
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
noncomputable section

structure Material where
  parent : Outer.Material
  basin : WholeBandBasin.BasinMaterial
  intra : ℝ
  cross : ℝ
  exterior : ℝ

def material : Material where
  parent := Outer.material
  basin := WholeBandBasin.material
  intra := intraEnergy
  cross := firstCrossEnergy
  exterior := exteriorEnergy

theorem parent_same_source : material.parent=Outer.material := rfl
theorem basin_same_source : material.basin.basin=WholeBandBasin.basin := rfl

theorem material_pair_energy :
    material.intra+2*material.cross+material.exterior =
      LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.pairCoulombEnergy.re :=
  full_pair_energy_three_regions

structure Closure : Prop where
  parent : Outer.Closure
  actualBasin : WholeBandBasin.BasinClosure
  parentIdentity : type_of% parent_same_source
  basinIdentity : type_of% basin_same_source
  regionalIntegrable : type_of% regional_integrable
  fourRegions : type_of% full_pair_energy_four_regions
  crossSymmetric : type_of% cross_region_energy_symmetry
  regionalPositive : type_of% four_region_nonnegative
  threeRegions : type_of% material_pair_energy
  originalAO : type_of% original_ao_energy_four_regions
  patchLimit : type_of% intra_energy_patch_limit

theorem sourceGeneratedClosure : Closure :=
  ⟨Outer.sourceGeneratedClosure,WholeBandBasin.sourceGeneratedBasin,
    parent_same_source,basin_same_source,regional_integrable,
    full_pair_energy_four_regions,cross_region_energy_symmetry,
    four_region_nonnegative,material_pair_energy,original_ao_energy_four_regions,
    intra_energy_patch_limit⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
