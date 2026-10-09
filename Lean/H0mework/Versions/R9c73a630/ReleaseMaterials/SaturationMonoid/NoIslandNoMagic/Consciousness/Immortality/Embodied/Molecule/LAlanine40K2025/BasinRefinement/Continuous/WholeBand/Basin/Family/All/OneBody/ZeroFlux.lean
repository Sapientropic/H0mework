import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Closure
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Weak.Invariant

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.OneBody
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource WholeBandBasin Set MeasureTheory
noncomputable section

theorem basin_invariant (i : Fin 13) (x : Point) (t : ℝ) :
    flow x t ∈ sourceBasin i ↔ x ∈ sourceBasin i :=
  Family.flow_membership (sourceSeed i) x t

theorem region_invariant (z : Option (Fin 13)) (x : Point) (t : ℝ) :
    flow x t ∈ region z ↔ x ∈ region z := by
  cases z with
  | some i =>
    rw [original_region]
    exact basin_invariant i x t
  | none =>
    rw [original_residual]
    simp only [mem_compl_iff,mem_iUnion,not_exists]
    constructor
    · intro h i inside
      exact h i ((basin_invariant i x t).mpr inside)
    · intro h i inside
      exact h i ((basin_invariant i x t).mp inside)

theorem every_basin_zero_flux (i : Fin 13) :
    (∫ x in sourceBasin i, laplacian sourceTerms densityMatrix x) = 0 :=
  Weak.Invariant.zero_flux (sourceBasin i) (Family.basin_measurable (sourceSeed i))
    (basin_invariant i)

theorem residual_zero_flux :
    (∫ x in region none, laplacian sourceTerms densityMatrix x) = 0 :=
  Weak.Invariant.zero_flux (region none) (all_regions_measurable none) (region_invariant none)

theorem every_zone_zero_flux (z : Option (Fin 13)) :
    (∫ x in region z, laplacian sourceTerms densityMatrix x) = 0 :=
  Weak.Invariant.zero_flux (region z) (all_regions_measurable z) (region_invariant z)

theorem atom7_same_basin : sourceBasin 7 = WholeBandBasin.basin :=
  Family.atom007_basin_same_source

theorem atom7_same_zero_flux : type_of% Weak.actual_basin_zero_flux := by
  rw [← atom7_same_basin]
  exact every_basin_zero_flux 7

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.OneBody
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
