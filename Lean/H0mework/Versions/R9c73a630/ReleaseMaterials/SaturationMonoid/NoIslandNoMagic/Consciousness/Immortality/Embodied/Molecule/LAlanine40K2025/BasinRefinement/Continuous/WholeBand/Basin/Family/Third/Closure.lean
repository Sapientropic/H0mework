import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Third
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Third
open SourceGaussianModel GlobalSource WholeBandBasin Set MeasureTheory
open WholeBandAttractor
noncomputable section

structure Material where
  parent : Family.Material
  atom009Basin : Set Point
  energy69 : ℝ
  energy79 : ℝ

def material : Material where
  parent := Family.material
  atom009Basin := Family.atom009Basin
  energy69 := Family.interatomicEnergy69
  energy79 := Family.interatomicEnergy79

theorem parent_same_source : material.parent=Family.material := rfl
theorem atom009_basin_same_source : material.atom009Basin=Family.atom009Basin := rfl

structure Closure : Prop where
  parent : Family.Closure
  actualAtom009Zero : type_of% Atom009.actual_gradient_zero
  actualAtom009Attraction : type_of% Atom009.actual_convergence
  parentIdentity : type_of% parent_same_source
  basinIdentity : type_of% atom009_basin_same_source
  newCover : type_of% Family.atom009_basin_cover
  newOpen : type_of% Family.atom009_basin_open
  newPositive : type_of% Family.atom009_basin_positive
  disjoint69 : type_of% Family.original_basins_6_9_disjoint
  disjoint79 : type_of% Family.original_basins_7_9_disjoint
  crossPositive : type_of% Family.both_interatomic_nonnegative
  crossSymmetric : type_of% Family.both_interatomic_symmetric
  patchLimits : type_of% Family.both_interatomic_patch_limits

theorem sourceGeneratedClosure : Closure :=
  ⟨Family.sourceGeneratedClosure,Atom009.actual_gradient_zero,
    Atom009.actual_convergence,parent_same_source,
    atom009_basin_same_source,Family.atom009_basin_cover,
    Family.atom009_basin_open,Family.atom009_basin_positive,
    Family.original_basins_6_9_disjoint,
    Family.original_basins_7_9_disjoint,
    Family.both_interatomic_nonnegative,
    Family.both_interatomic_symmetric,
    Family.both_interatomic_patch_limits⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Third
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
