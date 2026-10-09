import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Pair
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Slater.D3Residual.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
open SourceGaussianModel GlobalSource WholeBandBasin Set MeasureTheory
open LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater
open WholeBandAttractor
noncomputable section

structure Material where
  parent : D3Residual.Material
  atom006Critical : Point
  atom006Basin : Set Point
  cross : ℝ
  interatomic : ℝ

def material : Material where
  parent := D3Residual.material
  atom006Critical := Atom006.actualZero.point
  atom006Basin := Family.atom006Basin
  cross := crossEnergy
  interatomic := interatomicEnergy

theorem parent_same_source : material.parent=D3Residual.material := rfl
theorem atom006_basin_same_source : material.atom006Basin=atom006Basin := rfl
theorem interatomic_same_source : material.interatomic=2*material.cross :=
  interatomic_energy_twice

structure Closure : Prop where
  parent : D3Residual.Closure
  actualAtom006Zero : type_of% Atom006.actual_gradient_zero
  actualAtom006Attraction : type_of% Atom006.actual_convergence
  parentIdentity : type_of% parent_same_source
  basinIdentity : type_of% atom006_basin_same_source
  oldBasinIdentity : type_of% atom007_basin_same_source
  newCover : type_of% atom006_basin_cover
  newOpen : type_of% atom006_basin_open
  newPositive : type_of% atom006_basin_positive
  disjoint : type_of% original_basins_disjoint
  crossIntegrable : type_of% cross_energy_integrable
  crossPositive : type_of% cross_energy_nonnegative
  crossSymmetric : type_of% cross_energy_symmetric
  actualInteraction : type_of% interatomic_same_source
  interactionPositive : type_of% interatomic_energy_nonnegative
  patchLimit : type_of% cross_energy_patch_limit

theorem sourceGeneratedClosure : Closure :=
  ⟨D3Residual.sourceGeneratedClosure,Atom006.actual_gradient_zero,
    Atom006.actual_convergence,parent_same_source,
    atom006_basin_same_source,atom007_basin_same_source,
    atom006_basin_cover,atom006_basin_open,atom006_basin_positive,
    original_basins_disjoint,cross_energy_integrable,
    cross_energy_nonnegative,cross_energy_symmetric,
    interatomic_same_source,interatomic_energy_nonnegative,
    cross_energy_patch_limit⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
